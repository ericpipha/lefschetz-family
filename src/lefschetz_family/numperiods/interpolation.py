# AUTHORS:
#   - Pierre Lairez (2019): initial implementation

from sage.arith.misc import random_prime
from sage.functions.other import floor
from sage.misc.cachefunc import cached_method
from sage.rings.finite_rings.finite_field_constructor import FiniteField
from sage.rings.polynomial.polynomial_element import *
from sage.rings.polynomial.polynomial_ring import *
from sage.matrix.constructor import Matrix
from sage.modules.free_module_element import vector
from sage.rings.rational_field import QQ
from sage.rings.integer_ring import ZZ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing

from ore_algebra.ore_algebra import DifferentialOperators
from ore_algebra import ore_operator

import logging

def subproduct_tree(self, points):
    """Return the the subproduct tree associated to the points. The root is the
    polynomial `prod(t - p for p in points)` and the left and right children are
    the subproduct trees associated to the first and second half of the list
    `points`, respectively.

    """
    if len(points) <= 0:
        return None
    if len(points) == 1:
        return (self.gen() - points[0], )

    left = subproduct_tree(self, points[:len(points)//2])
    right = subproduct_tree(self, points[len(points)//2:])

    return (left[0]*right[0], left, right)

PolynomialRing_commutative.subproduct_tree = subproduct_tree


def polynomial_multi_evaluation_with_spt(self, spt, ret=None):
    if spt == None:
        return []

    if ret is None:
        ret = []

    rem = self.mod(spt[0])
    if len(spt) == 1:
        ret.append(rem.constant_coefficient())
    else:
        polynomial_multi_evaluation_with_spt(rem, spt[1], ret)
        polynomial_multi_evaluation_with_spt(rem, spt[2], ret)

    return ret


def sum_fractions_with_spt(coeffs, spt):
    if len(spt) == 1:
        return spt[0].parent()(coeffs[0])
    else:
        left = sum_fractions_with_spt(coeffs[:len(coeffs)//2], spt[1])
        right = sum_fractions_with_spt(coeffs[len(coeffs)//2:], spt[2])
        return left*spt[2][0] + right*spt[1][0]



class EvaluationInterpolation:
    """Perform basic evaluation and interpolation operations."""
    def __init__(self, polring, points):
        """Args:
        - polring: a univariate polynomial ring
        - points: a list of distinct elements of the basering
        """
        self.points = points
        self.polring = polring
        self.spt = None

    def _compute_spt(self):
        if self.spt is None:
            self.spt = self.polring.subproduct_tree(self.points)

    def evaluate(self, pol):
        """Return the list of values of `pol` at the elements of `self.points`."""
        self._compute_spt()
        return polynomial_multi_evaluation_with_spt(pol, self.spt)

    def interpolate(self, values):
        """Return a polynomial which evaluate to `values[i]` at `self.points[i]`."""
        assert len(values) == len(self.points), "The number of values must match the number of points."
        self._compute_spt()
        A = self.spt[0]
        der = self.evaluate(A.derivative())
        if any(d == 0 for d in der):
            return None

        br = A.base_ring()
        coeffs = [br(values[i])/der[i] for i in range(len(der))]
        return sum_fractions_with_spt(coeffs, self.spt)

    def _rational_interpolate_gen(self, values):
        """Returns a pair of polynomials (n,d) such that n/d interpolates the pairs.
        May fail and return None.
        """
        if len(values) == 0:
            return self.zero(), self.one()

        self._compute_spt()
        A = self.spt[0]
        B = self.interpolate(values)
        try:
            numer, denom = B.rational_reconstruct(A)
            if numer.degree() + denom.degree() + 1 < len(values):
                return numer, denom
            else:
                return None
        except:                 # rational_reconstruct fails with an exception.
            return None

    def _rational_interpolate_qq(self, values):
        def ev(prime):
            gf = FiniteField(prime)
            modpolring = self.polring.change_ring(gf)
            ei = EvaluationInterpolation(modpolring, self.points)
            return ei._rational_interpolate_gen(values)

        return ModularReconstruction(ev).recons()

    def rational_interpolate(self, values):
        if self.polring.base_ring().is_subring(QQ) and len(self.points) > 8:
            return self._rational_interpolate_qq(values)
        else:
            return self._rational_interpolate_gen(values)


def interpolation(self, pairs):
    """Same as `lagrange_polynomial` but faster."""
    if len(pairs) == 0:
        return self.zero()

    points = [p[0] for p in pairs]
    evs = [p[1] for p in pairs]
    return EvaluationInterpolation(self, points).interpolate(evs)

PolynomialRing_field.interpolation = interpolation


def rational_interpolation(self, pairs):
    """Returns a pair of polynomials (n,d) such that n/d interpolates the pairs.
    May fail and return None.
    """
    if len(pairs) == 0:
        return self.zero(), self.one()

    points = [p[0] for p in pairs]
    evs = [p[1] for p in pairs]
    return EvaluationInterpolation(self, points).rational_interpolate(evs)

PolynomialRing_field.rational_interpolation = rational_interpolation



class Serial:
    def __init__(self, polring=None):
        self.polring = polring
        if not polring is None:
            self.dopring = DifferentialOperators(polring.base_ring(), var=polring.variable_name())

        self.polrings = {}

    def _explode(self, elt, data, struct):
        if isinstance(elt, list):
            struct.append("list")
            struct.append(len(elt))
            for e in elt:
                self._explode(e, data, struct)
        elif isinstance(elt, tuple):
            struct.append("tuple")
            self._explode(list(elt), data, struct)
        elif isinstance(elt, dict):
            struct.append("dict")
            struct.append(tuple(elt.keys()))
            self._explode(list(elt.values()), data, struct)
        elif isinstance(elt, sage.structure.element.Matrix):
            struct.append("matrix")
            self._explode(elt.rows(), data, struct)
        elif isinstance(elt, sage.structure.element.Vector):
            struct.append("vector")
            self._explode(elt.list(), data, struct)
        elif isinstance(elt, sage.rings.polynomial.polynomial_element.Polynomial):
            struct.append("polynomial")
            struct.append(elt.parent().variable_name())
            self._explode(elt.list(), data, struct)
        elif isinstance(elt, sage.rings.fraction_field_element.FractionFieldElement_1poly_field):
            struct.append("ratfun")
            self._explode(elt.numerator(), data, struct)
            self._explode(elt.denominator(), data, struct)
        elif isinstance(elt, ore_operator.UnivariateOreOperator):
            struct.append("dop")
            struct.append(elt.parent().base_ring().variable_name())
            self._explode(elt.list(), data, struct)
        else:
            struct.append("self")
            data.append(elt)

    def explode(self, elt):
        data = []
        struct = []
        self._explode(elt, data, struct)
        data.reverse()
        struct.reverse()
        return (data, tuple(struct))

    def recons(self, data, struct):
        return self._recons(data, list(struct))

    def _recons(self, data, struct):
        next = struct.pop()
        if next == "list":
            return [self._recons(data, struct) for i in range(struct.pop())]
        elif next == "tuple":
            return tuple(self._recons(data, struct))
        elif next == "dict":
            keys = struct.pop()
            values = self._recons(data, struct)
            return dict(zip(keys, values))
        elif next == "matrix":
            return Matrix(self._recons(data, struct))
        elif next == "vector":
            return vector(self._recons(data, struct))
        elif next == "polynomial":
            name = struct.pop()
            l = self._recons(data, struct)
            if len(l) == 0:
                return 0
            else:
                if not name in self.polrings:
                    self.polrings[name] = PolynomialRing(l[0].parent(), name)
                return self.polrings[name](l)
        elif next == "ratfun":
            numer = self._recons(data, struct)
            denom = self._recons(data, struct)
            return numer/denom
        elif next == "dop":
            name = struct.pop()
            l = self._recons(data, struct)
            if len(l) == 0:
                return 0
            else:
                Dop, _, _ = DifferentialOperators(l[0].parent().base_ring(), var=name)
                return Dop(l)
        elif next == "self":
            return data.pop()
        else:
            raise Exception("Misformed struct")


class Tick:
    def __init__(self, inc=4):
        self.cnt = 1
        self.i = 1
        self.inc = inc

    def tick(self):
        self.i -= 1
        if self.i == 0:
            self.cnt = self.cnt+self.inc
            self.i = self.cnt
            return True
        else:
            return False

    def ticknexttime(self):
        self.i = 1

class ModularReconstruction:
    logger = logging.getLogger('numperiods.interpolation.ModularReconstruction')

    def __init__(self, evaluator, modsize=30):
        self.maxprime = 2**modsize
        self.data = {}
        self.primes = {}
        self.cand0 = None
        self.evaluator = evaluator
        self.serial = Serial()
        self.tick = Tick(inc=1)

    def _next(self, prime):
        if prime in self.primes:
            return

        self.logger.info("Evaluating modulo %i" % prime)

        try:
            ev = self.evaluator(prime)
        except ZeroDivisionError:
            self.logger.info("Bad evaluation, skipping this value.")
            return

        data, struct = self.serial.explode(ev)
        key = struct

        if not key in self.data:
            self.data[key] = data
        else:
            assert len(data) == len(self.data[key]), "Evaluations must have the same length for a given key."
            self.data[key] = [self.data[key][i].crt(data[i]) for i in range(len(data))]

        return key

    def _try_reconstruction(self, key):
        self.logger.info("Trying modular reconstruction.")

        cand = []
        try:
            for c in self.data[key]:
                cand.append(c.rational_reconstruction())
        except ArithmeticError:
            return None

        if cand == self.cand0:
            return self.serial.recons(cand, key)
        else:
            self.logger.info("Possible reconstruction. Computing modulo one more prime to check.")
            self.tick.ticknexttime()
            self.cand0 = cand
            return None

    def recons(self):
        pt = Integer(1)
        while True:
            pt += 1
            prime = random_prime(self.maxprime, lbound=self.maxprime/128)
            key = self._next(prime)

            # We don't always try reconstruction (it is expensive)
            if self.tick.tick():
                cand = self._try_reconstruction(key)
                if not cand is None:
                    return cand


class FunctionReconstruction:
    logger = logging.getLogger('numperiods.interpolation.FunctionReconstruction')

    def __init__(self, polring, evaluator):
        self.polring = polring
        self.serial = Serial()
        self.evaluator = evaluator

        self.tick = Tick()
        self.data = {}
        self.tests = {}
        self.testsmod = {}
        self.rands = {}
        self.basering = polring.base_ring()
        if self.basering.characteristic() == 0:
            self.modring = FiniteField(random_prime(10**9))
            self.modpolring = polring.change_ring(self.modring)
        else:
            self.modring = self.basering
            self.modpolring = polring

    def _next(self, pt):
        self.logger.info("Evaluating at %i" % pt)
        try:
            ev = self.evaluator(pt)
        except ZeroDivisionError:
            self.logger.info("Bad evaluation, skipping this value.")
            return

        data, struct = self.serial.explode(ev)
        key = struct

        if not key in self.rands:
            self.data[key] = {}
            self.tests[key] = {}
            self.testsmod[key] = {}
            self.rands[key] = [ZZ.random_element(1000) for _ in data]
        else:
            assert len(data) == len(self.rands[key]), "Evaluations must have the same length for a given key."

        self.data[key][pt] = data

        try:
            self.tests[key][pt] = sum(r*e for r, e in zip(self.rands[key], data))
            self.testsmod[key][self.modring(pt)] = self.modring(self.tests[key][pt])
        except ZeroDivisionError:
            self.logger.info("Bad evaluation to the finite field, skipping this value.")
            return

        return key

    def recons(self, denomapart=False):
        pt = Integer(100)
        while True:
            pt += 1
            key = self._next(pt)

            # We don't always try reconstruction (it is expensive)
            if self.tick.tick():
                cand = self._try_reconstruction(key, denomapart=denomapart)
                if not cand is None:
                    return cand


    def _try_reconstruction(self, key, denomapart=False):
        self.logger.info("Trying rational reconstruction...")

        reconmod = self.modpolring.rational_interpolation(self.testsmod[key].items())
        if reconmod is None:
            self.logger.info("Reconstruction failed.")
            return None

        self.logger.info("Reconstructing denominator...")

        points = list(self.tests[key].keys())
        ei = EvaluationInterpolation(self.polring, points)
        if self.modring == self.basering:
            recon = reconmod
        else:
            recon = ei.rational_interpolate([self.tests[key][p] for p in points])
            if recon is None:
                self.logger.info("Reconstruction failed surprisingly.")
                return None

        denom = recon[1]
        assert denom.leading_coefficient() == 1

        evdenom = ei.evaluate(denom)
        nfun = len(self.rands[key])
        cand = []

        for i in range(nfun):
            self.logger.info("Reconstructing numerator %d of %d..." % (i+1, nfun))
            elt = ei.interpolate([self.data[key][p][i]*evdenom[idx] for idx, p in enumerate(points)])
            if 3*elt.degree() > 2*len(points):
                self.logger.warn("The random sampling failed. Should happen very rarely.")
                self.__init__(self.polring, self.evaluator)
                return None
            if denomapart:
                cand.append(elt)
            else:
                cand.append(elt/denom)

        if denomapart:
            return self.serial.recons(cand, key), denom
        else:
            return self.serial.recons(cand, key)

