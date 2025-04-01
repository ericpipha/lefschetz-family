import logging
import time

from sage.all import (
    block_matrix,
    ComplexBallField,
    diagonal_matrix,
    Frac,
    matrix,
    MatrixSpace,
    RBF,
    ZZ
)

from ore_algebra import OreAlgebra
from ore_algebra.analytic.accuracy import PrecisionError
from ore_algebra.analytic.bounds import BoundPrecisionError
from ore_algebra.analytic.context import Context, dctx
from ore_algebra.analytic.dac_sum import HighestSolMapper_dac
from ore_algebra.analytic.differential_operator import DifferentialOperator
from ore_algebra.analytic.path import EvaluationPoint_step, Path
from ore_algebra.analytic.utilities import prec_from_eps
from ore_algebra.tools import clear_denominators


logger = logging.getLogger(__name__)

# 2024-12-17 En théorie on pourrait généraliser tout ça aux points singuliers
# réguliers : pour calculer ∫RY sur un lacet basé en z0 ≈ 0, on intègre
# formellement terme à terme RY où R est la même matrice de fractions
# rationnelles que d'habitude et Y est une matrice de séries logarithmiques
# tronquées (qui arrivent par blocs).

class StreamOperation:
    r"""
    Some infrastructure for operations on streams of coefficients

    The aim is to be able to experiment with several ways of implementing our
    integrator.
    """

    def __init__(self, parent, arity, block_size, shift=0):
        # parent = polynomial ring in which we are working
        # (not strictly necessary: for more flexibility, we could start with
        # ints and rely on coercion)
        self.parent = parent
        # block_size = how many coeffs process_block() consumes at once
        # XXX Pas sûr qu'on veuille vraiment fixer ça à l'initialisation, la
        # plupart des opérations sont en réalité plus souples. Et il faut
        # peut-être découpler la taille du bloc qu'on extrait du buffer de
        # celle qu'on produit en sortie.
        assert block_size > 0
        self.block_size = block_size
        self.shift = shift
        self.input = [parent.zero()]*arity
        self.input_len = [0]*arity
        self.input_done = [False]*arity
        self.pos = 0
        # XXX return instead of writing to self.output?
        self.output = parent.zero()
        self.subscribers = []

    def __repr__(self):
        return type(self).__name__

    def subscribe(self, series, operand=0):
        self.subscribers.append((series, operand))

    def push_coefficients(self, coeff, push_len, operand):
        assert coeff.degree() < push_len
        logger.debug("%s received %s coefficients (block size=%s)", self, coeff.degree(), self.block_size)
        self.input[operand] += (coeff << self.input_len[operand])
        self.input_len[operand] += push_len
        # XXX on jette le dernier bloc incomplet reçu, et de même récursivement
        # pour les opérations en aval, c'est un peu merdique
        while all(l >= self.block_size for l in self.input_len):
            self._do_process_block()

    def _do_process_block(self):
        logger.debug("%s processing block at pos %s", self, self.pos)
        block = [input[:self.block_size] for input in self.input]
        self.process_block(*block)
        for i in range(len(self.input)):
            self.input[i] >>= self.block_size
            self.input_len[i] -= self.block_size
            self.input_len[i] = max(0, self.input_len[i])
        push_len = self.block_size
        if self.pos == 0:
            push_len += self.shift
        assert push_len >= 0
        for ser, op in self.subscribers:
            ser.push_coefficients(self.output, push_len, op)
        self.output = self.parent.zero()
        self.pos += self.block_size

    def process_block(self):
        raise NotImplementedError

    def close_input(self, operand=None):
        if operand is not None:
            self.input_done[operand] = True
        if all(self.input_done):
            logger.debug("%s done", self)
            # WARNING for ops with multiple inputs, this consumes all available
            # coefficients, even if some inputs have more data than others
            while any(self.input_len):
                self._do_process_block()
            for ser, op in self.subscribers:
                ser.close_input(op)


class Source(StreamOperation):

    def __init__(self, parent, block_size):
        super().__init__(parent, arity=0, block_size=block_size)

    def push_coefficients(self, coeff, push_len, operand):
        raise RuntimeError

    def generate(self, block):
        assert block.degree() < self.block_size
        for (ser, op) in self.subscribers:
            ser.push_coefficients(block, self.block_size, op)

    def process_block(self):  # XXX
        pass


class Capture(StreamOperation):  # for testing

    def __init__(self, series):
        super().__init__(series.parent, arity=1, block_size=series.block_size)
        series.subscribe(self)
        self.value = series.parent.zero()

    def process_block(self, block):
        self.value += block << self.pos


class Diff(StreamOperation):

    def __init__(self, series):
        super().__init__(series.parent, arity=1, block_size=series.block_size,
                         shift=-1)
        series.subscribe(self)

    def process_block(self, block):
        if self.pos == 0:
            self.output = block.derivative()
        else:  # XXX
            self.output = (block << self.pos).derivative() >> (self.pos - 1)


class Int(StreamOperation):

    def __init__(self, series):
        super().__init__(series.parent, arity=1, block_size=series.block_size,
                         shift=+1)
        series.subscribe(self)

    def process_block(self, block):
        if self.pos == 0:
            self.output = block.integral()
        else:  # XXX
            self.output = (block << self.pos).integral() >> (self.pos + 1)


class MulByPoly(StreamOperation):

    def __init__(self, poly, series):
        assert poly.parent() is series.parent
        super().__init__(poly.parent(), arity=1, block_size=max(poly.degree(), 0) + 1)
        self.poly = poly
        self.state = series.parent.zero()
        series.subscribe(self)

    def __repr__(self):
        return f"{type(self).__name__}(deg={self.poly.degree()})"

    def process_block(self, block):
        # XXX Le gros du temps passe dans la ligne suivante. Normal, mais
        # peut-on faire mieux ? Peut-être via une autre formule d'intégration ?
        self.state += self.poly*block
        self.output = self.state[:self.block_size]
        self.state >>= self.block_size


class DivByPoly(StreamOperation):

    def __init__(self, series, poly):
        assert poly.parent() is series.parent
        super().__init__(poly.parent(), arity=1, block_size=poly.degree() + 1)
        series.subscribe(self)
        self.poly = poly  # just for printing
        # precomputed inverse: poly*inv = 1 + x^n*rem
        self.inv = poly.inverse_series_trunc(self.block_size)
        self.rem = (self.inv*poly) >> self.block_size
        # state
        self.quo = self.parent.zero()
        self.num = self.parent.zero()

    def __repr__(self):
        return f"{type(self).__name__}(deg={self.poly.degree()})"

    def process_block(self, block):  # likely improvable
        # XXX coûteux (normal...)
        self.num += block
        # f/poly = inv*poly - x^n*(rem*f)/poly
        # (f0 + x^n*f1)/poly
        # = low(inv*f0) + x^n*(high(u*f0) + (-rem*f0 + f1)/poly)
        f0 = self.num[:self.block_size]
        self.quo += self.inv*f0
        self.num = (self.num >> self.block_size) - self.rem*f0
        self.output = self.quo[:self.block_size]
        self.quo >>= self.block_size  # high(inv*f0)


class Add(StreamOperation):

    def __init__(self, series):
        assert len(series) > 0
        assert all(ser.parent is series[0].parent for ser in series)
        super().__init__(series[0].parent, arity=len(series),
                         block_size=max(ser.block_size for ser in series))
        for i, ser in enumerate(series):
            ser.subscribe(self, i)

    def process_block(self, *blocks):
        self.output = sum(blocks)


class EvalSum(StreamOperation):

    def __init__(self, series, point):
        super().__init__(series.parent, arity=1, block_size=series.block_size)
        series.subscribe(self)
        self.point = point
        self.point_pow = point.parent().one()
        self.point_pow_block = point**series.block_size
        self.value = point.parent().zero()  # assumes large enough parent

    def push_coefficients(self, coeff, push_len, operand):
        super().push_coefficients(coeff, push_len, operand)

    def process_block(self, block):
        self.value += self.point_pow*block(self.point)
        # XXX redundant computation (DACUnroller + each EvalSum)
        self.point_pow *= self.point_pow_block


# On pourrait essayer d'autres formulations : séparer les multiplications par
# les matrices aux et itnum, utiliser des dénominateurs distincts pour les
# lignes de aux, réécrire la formule par intégration par parties... C'est une
# partie de l'intérêt de tout le bazar ci-dessus, l'autre étant de rendre les
# bouts plus faciles à tester séparément.
#
# 2024-12-17 Voir aussi si une structure des degrés/dénominateurs issue de la
# filtration de Hodge se retrouve quelque part et si on pourrait l'exploiter.
def shifted_int_mat_times_fmat(num, den, pts, Pol, blksz):
    assert len(den) == num.nrows()
    sources = [Source(Pol, blksz) for _ in range(num.ncols())]
    fmatA = [sources]
    for i in range(num.ncols() - 1):
        fmatA.append([Diff(f) for f in fmatA[-1]])
    # XXX manque-t-il une multiplication ou division par une diagonale de
    # fatorielles quelque part ? non, je ne crois pas : dans cette partie
    # symbolique, tout est écrit en termes des dérivées usuelles
    expr = [
        [[EvalSum(
            Int(
                DivByPoly(
                    # on veut peut-être garder les coefficients rationnels dans
                    # les polynômes...
                    Add([MulByPoly(Pol(num[i][k]), fmatA[k][j])
                         for k in range(num.ncols())]),
                    Pol(den[i]))),
            pt)
          for j in range(num.ncols())]
         for i in range(num.nrows())]
        for pt in pts]
    return sources, expr


def uncouple(sys, den, vec=None):
    r"""
    Uncouple a differential system (fraction-free).

    Return:
    * a diff op annihilating ``y = vec·Y`` where ``Y`` is a vector such that
      ``den·Y' = Y``,
    * a matrix ``T(x)`` s.t. ``T(x)·Y(x) = [y, y', y'', ...]``.
    """
    # maybe clear denominators from the coefficients of sys and den
    Mat = sys.parent()
    Pol = sys.base_ring()
    Dop = OreAlgebra(Pol, 'D' + Pol.variable_name())
    if vec is None:
        vec = Mat.column_space().gen(0)
    else:
        vec = Mat.column_space()(vec)
    x = Pol.gen()
    dden = den.derivative(x)
    mat = matrix(vec)
    for k in range(sys.ncols()):
        v = mat.row(-1)
        v1 = den*v.derivative(x) + v*sys - k*dden*v
        mat = mat.stack(v1)
    denpow = Pol.one()
    for i in range(mat.nrows() - 2, -1, -1):
        denpow *= den
        mat.rescale_row(i, denpow)
    # assert mat.row(0) == den**sys.ncols()*vec
    #ker = mat.left_kernel_matrix()
    #ker = mat.minimal_kernel_basis()  # LEFT kernel
    solver = Dop._solver(mat.base_ring())
    ker = matrix(solver(mat.transpose()))
    if ker.nrows() != 1:
        raise RuntimeError("not cyclic")
    dop = Dop.change_ring(Frac(Pol.change_ring(ZZ)))(list(ker[0])).numerator()
    # maybe keep num&den separate in transformation matrix
    return dop, ~denpow*mat[:-1][:]


class PostIntObserver:

    def __init__(self, num, den, pts):
        self.num = num
        self.den = den
        self.pts = pts
        self.sources = None
        self.expr = None

    def reset(self, unr):
        # TODO better choice of prec here? we *are* losing a significant number
        # of digits in this phase too
        Pol = self.num.base_ring().change_ring(ComplexBallField(unr.sums_prec))
        self.sources, self.expr = shifted_int_mat_times_fmat(
            self.num, self.den, self.pts, Pol, unr.blksz)

    def push_block(self, unr, data):
        for sol, source in zip(data, self.sources):
            assert len(sol) == 1  # log_prec
            source.generate(sol[0])

    def finalize(self):  # XXX un peu pourri comme interface
        for source in self.sources:
            source.close_input()


def fundamental_matrices(sys, den, aux, auxden, path, eps, vec=None, ctx=dctx):

    z = den.parent().gen()
    logger.info("uncoupling...")
    t0 = time.time()
    dop, transf = uncouple(sys, den, vec)
    logger.info("done uncoupling, degree=%s, time=%ss",
                dop.degree(), time.time() - t0)
    dop = DifferentialOperator(dop)
    logger.info("computing transformation...")
    t0 = time.time()
    # wasteful
    itnum, itden = clear_denominators(transf.inverse().list())
    itnum = matrix(transf.nrows(), transf.ncols(), itnum)
    # compute these while we are (presumably) working over QQ
    # XXX pas sûr que ça soit vraiment ce qu'on veut
    # (ni finalement que ça n'ait une importance maintenant qu'on fait le shift
    # numériquement)
    aux1 = aux*itnum
    auxden1 = auxden*itden
    logger.info("done, time=%s s", time.time() - t0)
    dop2 = DifferentialOperator(auxden1*dop)
    # print(len(dop._singularities()), len(dop2._singularities()))
    path = Path(path, dop2)
    # path = Path(path, dop)
    logger.info("path = %ss", path)
    eps = RBF(eps)
    # FIXME prec currently needs to be >= sums_prec (as chosen by HSM) or we
    # are wasting precision
    prec0 = prec_from_eps(eps)
    prec = 6*(prec0 + 2*dop.order())//5 + 100
    Val = ComplexBallField(prec)
    diag = diagonal_matrix(ZZ(i).factorial() for i in range(sys.nrows()))

    logger.info("computing singularities, subdividing path...")
    t0 = time.time()
    # Il peut arriver qu'on se retrouve avec un opérateur singulier en 0
    # même si au départ le système ne l'était pas...
    path = path.bypass_singularities()
    # path.check_singularity()
    path = path.subdivide(1)  # TODO support 2-point mode
    path = path.simplify_points_add_detours(ctx)
    path.check_singularity()
    path.check_convergence()
    logger.info("done, time=%ss, path = %s", time.time() - t0, path)

    tmat_path = block_matrix([[1, MatrixSpace(Val, aux.nrows(), aux.ncols()).zero()],
                              [0, 1]])
    steps = list(path.steps())
    steps.reverse()
    while steps:

        step = steps.pop()
        logger.info("step %s", step)
        t0 = time.time()
        evpts = EvaluationPoint_step([step], jet_order=sys.nrows())
        deltas = [evpts.approx(Val, i) for i in range(len(evpts))]
        z0 = Val(step.start.as_sage_value())
        z1 = Val(step.end.as_sage_value())

        # TODO bornes d'erreur sur la partie aux
        # il faut, en gros :
        # - bien comprendre ce qu'on fait exactement avec les derniers
        # coefficients des développements en série des intégrales (toutes les
        # séries en jeu n'étant pas tronquées au même ordre, on se retrouve
        # peut-être par exemple avec des sommes de trucs tronqués à des ordres
        # différents)
        # - multiplier le majorant sur le reste de la sys par un majorant
        # rationnel convenable
        post_integrator = PostIntObserver(
            aux1(z0+z),
            [auxden1(z0+z)]*aux.nrows(),
            deltas)
        ldop = dop.shift(step.start)
        ctx = Context(ctx=ctx)
        ctx._set_interval_fields(256)
        ctx.__coeff_observer=post_integrator
        hsm = HighestSolMapper_dac(ldop, evpts, eps, fail_fast=True,
                                   effort=0,  # ???
                                   ctx=ctx)
        try:
            cols = hsm.run()
        except (BoundPrecisionError, PrecisionError):
            steps.extend(reversed(step.split()))
            continue

        # XXX redundant with adjacent steps
        transf0 = transf(z0)
        transf1 = transf(z1)

        fmats = []
        for m, delta in enumerate(deltas):  # only one iteration for now
            tmat_dop = matrix([sol.value[m] for sol in cols]).transpose()
            vmat_sys = ~transf1*diag*tmat_dop*~diag*transf0
            vmat_aux = matrix([[post_integrator.expr[m][i][j].value
                                for j in range(aux.ncols())]
                               for i in range(aux.nrows())])
            vmat_aux = vmat_aux*~diag*transf0
            fmat = block_matrix([[1, vmat_aux], [0, vmat_sys]])
            fmats.append(fmat)

        # XXX this is certainly improvable...
        if any(c.rad() > 2.**(-prec0) and c.accuracy() < prec0//2
               for c in vmat_aux.list()):
            steps.extend(reversed(step.split()))
            continue

        [fmat] = fmats
        tmat_path = fmat*tmat_path

        logger.info("done with step %s, time=%ss", step, time.time() - t0)

    return tmat_path
