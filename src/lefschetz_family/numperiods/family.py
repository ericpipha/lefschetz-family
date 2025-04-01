# -*- coding: utf-8 -*-

# AUTHORS:
#   - Pierre Lairez (2019): initial implementation
#   - Eric Pichon-Pharabod (2022): adding the coordinates functionality
#   - Eric Pichon-Pharabod (2023): adding the `shift` option


from sage.arith.misc import random_prime
from sage.combinat.integer_vector import IntegerVectors
from sage.geometry.voronoi_diagram import VoronoiDiagram
from sage.graphs.graph import Graph
from sage.matrix.constructor import Matrix
from sage.misc.cachefunc import cached_method
from sage.modules.free_module import FreeModule
from sage.modules.free_module_element import vector
from sage.rings.complex_double import CDF
from sage.rings.complex_interval_field import ComplexIntervalField
from sage.rings.finite_rings.finite_field_constructor import FiniteField
from sage.rings.polynomial.polynomial_ring import *
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ
from sage.rings.real_double import RDF
from sage.rings.integer_ring import ZZ
from sage.rings.real_mpfi import RealIntervalField
from sage.rings.imaginary_unit import I

from ore_algebra import OreAlgebra

import logging
import random
import signal

from . import interpolation
from . import cohomology
from . import config
from ..exceptions import FailFast

logger = logging.getLogger(__name__)

class Family(object):

    def __init__(self, pol, denom=1, path=None, discoverbasis=False, shift=0):
        """pol is an element of a ring of the form K[x1,...,xn][t]

        This class aims at computing in H^n( P^n - V(pol(t)) ).
        Classes in H^n can be differentiated wrt t, this is the Gauss-Manin connection.
        If m is a monomial (not depending on t), then d/dt [m] = [ -pol.derivative()*m ]
        """

        assert isinstance(pol.parent(), sage.rings.polynomial.polynomial_ring.PolynomialRing_integral_domain)
        assert pol.base_ring().base_ring().is_field()
        self.base_field = pol.base_ring().base_ring()

        coeffs = pol.coefficients()
        assert all(c.is_homogeneous() for c in coeffs)
        assert pol(123).is_homogeneous()

        self.pol = pol
        self.shift = shift
        self.upolring = self.pol.parent().change_ring(self.base_field)
        self.denom = self.upolring(denom)

        if path is None:
            self._path = [ZZ(0),ZZ(1)]
            self._explicit_path = False
        else:
            self._path = path
            self._explicit_path = True

        self.coho1 = self.cohomologyAt(self._path[-1])

        # This is crucial that we choose the basis at 1.
        self.discoverbasis = discoverbasis
        if not discoverbasis:
            self.basis = self.coho1.basis()
            self.endpoint = self._path[-1]

        self.dopring = OreAlgebra(self.upolring, 'D' + str(self.upolring.gen()))


    @cached_method
    def cohomologyAt(self, t):
        return cohomology.Cohomology(self.pol(self.pol.base_ring()(t))/self.denom(self.pol.base_ring()(t)), shift=self.shift)

    def modulo(self, prime):
        return Family(FiniteField(prime).one() * self.pol, denom=FiniteField(prime).one()*self.denom, shift=self.shift)

    def _gaussmanin(self, pt):
        logger.debug("Evaluating cohomology at a point %s" % str(pt))
        try:
            co = self.cohomologyAt(pt)
        except cohomology.NotSmoothError:
            raise ZeroDivisionError  # FunctionReconstruction only handles this exception

        der = (self.pol.derivative()(pt)*self.denom(pt) - self.denom.derivative()(pt)*self.pol(pt))/self.denom(pt)**2
        redmul = Matrix([co.coordinates(-b*der) for b in self.basis])
        redb = Matrix([co.coordinates(b) for b in self.basis])

        # Matrices are row-based.
        return redmul*redb.inverse()

    @cached_method
    def gaussmanin(self):
        """Return a pair (mat, denom), where mat is a matrix with polynomial
        coefficients, denom a polynomial and mat/denom the matrix of the Gauss-Manin
        connection in the basis self.basis.

        That is denom*derivative(self.basis) = mat * self.basis. In particular,
        if an element of the homology is given as the scalar product u*basis =
        sum_i u[i]*basis[i], then the derivative of u*basis is (u' +
        u*mat/denom)*basis, where u' is the coefficient-wise derivative.

        """
        

        logger.info("Computing Gauss-Manin connection")
        fr = interpolation.FunctionReconstruction(self.upolring, self._gaussmanin)
        return fr.recons(denomapart=True)

	
    def _coordinates(self, ws, pt):
        logger.debug("Evaluating cohomology at a point %s" % str(pt))
        try:
            co = self.cohomologyAt(pt)
        except cohomology.NotSmoothError:
            raise ZeroDivisionError  # FunctionReconstruction only handles this exception

        redb = Matrix([co.coordinates(b) for b in self.basis])
        coords = Matrix([co.coordinates(w(pt)) for w in ws])

        return coords*redb.inverse()

    def coordinates(self, ws):
        """Returns a list of vectors of coordinates in the basis self.basis, for w in ws

        """
        

        logger.info("Computing coordinates")
        fr = interpolation.FunctionReconstruction(self.upolring, lambda pt: self._coordinates(ws, pt))
        return fr.recons(denomapart=True)
    
    @cached_method
    def picard_fuchs_equation(self, vec=None, form=None):
        """vec is a constant-coefficient vector representing an element omega of
        H^n(P^n - V(pol)) in the basis self.basis.

        """
        #logger.info("Computing a cyclic space.")

        if config.fail_fast:
            signal.alarm(config.time_to_compute_picard_fuchs_equations)

        if form is not None:
            vec = self.coho1.coordinates(form)

        vec = vec.change_ring(self.upolring)
        mat, denom = self.gaussmanin()
        dim = len(self.basis)

        logger.info("Computing Picard-Fuchs equation for %s." % str(vec(1) * vector(self.basis)))

        while True:
            cyclicspace = vec.row()

            rpoint = self.base_field(ZZ.random_element(10000, 100000))
            cyclicspace_at_r = cyclicspace(rpoint)
            var = self.upolring.gen()

            k = 0
            while cyclicspace_at_r.rank() == cyclicspace_at_r.nrows():
                logger.info("Looking for equation of order %d." % (k+1))
                k = k+1
                vec = denom*vec.derivative(var) + vec*mat - (k-1)*denom.derivative(var)*vec
                cyclicspace = denom*cyclicspace
                cyclicspace = cyclicspace.stack(vec)
                cyclicspace_at_r = cyclicspace_at_r.stack(vec(rpoint))

                # The k-th row of cyclicspace is denom^(n-1) * d^k/dt^k [vec], where n is
                # the number of columns. cyclicspace_at_r is the evaluation (up to a row
                # scaling) of cyclicspace at a random point. We test if the rank of cyclicspace is
                # defficient by computing the rank of cyclicspace_at_r. This may fail but we don't
                # care.

            try:
                logger.info("Computing kernel.")
                kernel = cyclicspace.transpose().change_ring(self.upolring.fraction_field()).right_kernel_matrix()
                deq = kernel.row(0)
            except IndexError:
                logger.warn("The matrix equation has no solution, we retry.")
                logger.warn("If this loops for ever, this is an error.")
                continue
            break

        if config.fail_fast:
            signal.alarm(0)

        deq = deq.denominator() * deq

        # This is the differential equation satisfied by the basis element b.
        deq = self.dopring(deq.list())

        logger.info("Found an equation of order %d." % deq.order())
        return deq

    @cached_method
    def picard_fuchs_order(self, vec=None, form=None):
        """vec is a constant-coefficient vector representing an element omega of
        H^n(P^n - V(pol)) in the basis self.basis.

        """
        #logger.info("Computing a cyclic space.")

        if config.fail_fast:
            signal.alarm(config.time_to_compute_picard_fuchs_equations)

        if form is not None:
            vec = self.coho1.coordinates(form)

        vec = vec.change_ring(self.upolring)
        mat, denom = self.gaussmanin()
        dim = len(self.basis)

        logger.info("Computing Picard-Fuchs equation for %s." % str(vec(1) * vector(self.basis)))

        cyclicspace = vec.row()

        rpoint = self.base_field(ZZ.random_element(10000, 100000))
        cyclicspace_at_r = cyclicspace(rpoint)
        var = self.upolring.gen()

        k = 0
        while cyclicspace_at_r.rank() == cyclicspace_at_r.nrows():
            logger.info("Looking for equation of order %d." % (k+1))
            k = k+1
            vec = denom*vec.derivative(var) + vec*mat - (k-1)*denom.derivative(var)*vec
            cyclicspace = denom*cyclicspace
            cyclicspace = cyclicspace.stack(vec)
            cyclicspace_at_r = cyclicspace_at_r.stack(vec(rpoint))

            # The k-th row of cyclicspace is denom^(n-1) * d^k/dt^k [vec], where n is
            # the number of columns. cyclicspace_at_r is the evaluation (up to a row
            # scaling) of cyclicspace at a random point. We test if the rank of cyclicspace is
            # defficient by computing the rank of cyclicspace_at_r. This may fail but we don't
            # care.

        return cyclicspace_at_r.rank()

    def _space_generated_by_derivatives_at_1(self, vec):
        vec = vec.change_ring(self.upolring)
        mat, denom = self.gaussmanin()

        rpoint = self.base_field(ZZ.random_element(100000, 10000000))
        cyclicspace_at_r = vec.row()
        cyclicspace_at_1 = vec.row()

        var = self.upolring.gen()
        k = 0
        while True:
            k = k+1
            if config.fail_fast and k > config.max_dimension_of_a_cyclic_space:
                logger.info("Skipping this cyclic space, dimension %d too high." % k)
                raise FailFast()

            vec = denom*vec.derivative(var) + vec*mat - (k-1)*denom.derivative(var)*vec
            cyclicspace_at_r = cyclicspace_at_r.stack(vec(rpoint))
            logger.debug("Cyclic space grows to dimension %d." % k)
            if cyclicspace_at_r.rank() < cyclicspace_at_r.nrows():
                break
            cyclicspace_at_1 = cyclicspace_at_1.stack(vec(self.endpoint))

        return cyclicspace_at_1

    @cached_method
    def generators_of_cyclic_decomposition(self, only_holomorphic_forms=False):
        """Return a dictionary.

        The keys are elements of self.basis. The value associated to b is a
        differential operator that annihilates b.

        Moreover, it is guaranteed that the keys and their relevant derivatives
        generate the cohomoogy at 1.

        """

        logger.info("Computing generators of a cyclic decomposition (only_holomorphic_forms=%s)." % str(only_holomorphic_forms))

        if config.unsafe_cyclic_decomposition and self.base_field.characteristic() == 0:
            logger.info("Computing generators of a cyclic decomposition modulo a random prime.")
            modp = self.modulo(random_prime(2**30, lbound=2**25))
            cydec = modp.generators_of_cyclic_decomposition(only_holomorphic_forms)
            return [r.change_ring(self.base_field) for r in cydec]


        ambient_space = FreeModule(self.base_field, len(self.basis))
        if only_holomorphic_forms:
            target_basis = [ambient_space.gen(self.coho1.index_of_basis_elt(b))
                            for b in self.coho1.holomorphic_forms()]
            target_space = ambient_space.submodule(target_basis)
        else:
            target_space = ambient_space
            target_basis = ambient_space.basis()

        spaces_generated_at_1 = []
        for idx, vec in enumerate(target_basis):
            try:
                sp = self._space_generated_by_derivatives_at_1(vec)
                spaces_generated_at_1.append((sp.nrows(), idx, sp))
            except FailFast:
                pass

        spaces_generated_at_1.sort()

        def filter_in_order(list):
            selection = []
            current_space = ambient_space.submodule([])
            for dim, i, sp in spaces_generated_at_1:
                current_space += ambient_space.submodule(sp.rows())
                selection.append((dim, i, sp))
                if target_space.is_submodule(current_space):
                    break

            if not target_space.is_submodule(current_space):
                raise FailFast('Not enough small cyclic spaces.')
            return selection

        #spaces_generated_at_1.reverse()
        selection = filter_in_order(spaces_generated_at_1)
        selection.reverse()
        selection = filter_in_order(selection)
        selection.reverse()

        #Is this loop useful?
        for _ in range(6):
            random.shuffle(selection)
            selection = filter_in_order(selection)

        selection.sort(key=lambda s: s[1])

        return [target_basis[s[1]] for s in selection]


    @cached_method
    def _singularities(self, only_holomorphic_forms=False):
        # The path computation must account for the singularities of ALL
        # equations, otherwise, the analytic continuations may not be
        # compatible.
        roots = []
        for vec in self.generators_of_cyclic_decomposition(only_holomorphic_forms):
            deq = self.picard_fuchs_equation(vec)
            pol = deq.leading_coefficient().radical()
            roots.extend(pol.roots(ComplexIntervalField(53), multiplicities=False))

        if len(roots) > 0:
            self._precision_for_isolating_singularities = roots[0].parent().precision()
        else:
            self._precision_for_isolating_singularities = 53

        return roots


    @cached_method
    def _path_graph(self, only_holomorphic_forms=False):
        rootapprox = set((r.real().simplest_rational(), r.imag().simplest_rational())
                         for r in self._singularities(only_holomorphic_forms))
        rootapprox.add((QQ(0), QQ(0)))
        rootapprox.add((QQ(1), QQ(0)))
        rootapprox.add((QQ(1), QQ(0)))
        rootapprox.add((QQ(0), QQ(10))) # To ensure that there is always a path.
        rootapprox.add((QQ(0), QQ(10)))

        vd = VoronoiDiagram(rootapprox)

        # We fill a graph. The vertices are points in the complex plane (including 0 and 1).
        # Edges are edges of the Voronoi diagram and special edges to reach 0 and 1.
        gr = Graph()

        # This is slow
        for pt_, reg in vd.regions().items():
            pt = tuple(pt_)
            pt = pt[0] + I*pt[1]
            ptc = CDF(pt)
            for edge in reg.bounded_edges():
                u = edge[0][0]+I*edge[0][1]
                v = edge[1][0]+I*edge[1][1]
                uc, vc = CDF(u), CDF(v)
                ratio = (uc-vc).abs()/min((ptc-uc).abs(), (ptc-vc).abs(), (ptc-(uc+vc)/2).abs())
                gr.add_edge(u, v, label=float(ratio))

            if pt == 0 or pt == 1:
                for v in reg.vertices():
                    u = v[0]+I*v[1]
                    gr.add_edge(pt, u, 1.0)

        return gr

    @cached_method
    def _nice_path(self, only_holomorphic_forms=False):
        logger.info("Computing a nice path for integration.")
        if all(self.picard_fuchs_equation(vec).leading_coefficient().radical().number_of_roots_in_interval(0,1) < 2
               for vec in self.generators_of_cyclic_decomposition(only_holomorphic_forms)):
            return [0,1]

        gr = self._path_graph(only_holomorphic_forms)

        RIF = RealIntervalField(self._precision_for_isolating_singularities)
        def simplify_complex(z, radius):
            return RIF(z.real()-radius,z.real()+radius).simplest_rational() + I*RIF(z.imag()-radius,z.imag()+radius).simplest_rational()

        shortpath = gr.shortest_path(QQ(0), QQ(1), by_weight=True)
        nicepath = [shortpath[0]]

        for i in range(1,len(shortpath)-1):
            ratio = min(gr.edge_label(shortpath[i-1], shortpath[i]),
                        gr.edge_label(shortpath[i], shortpath[i+1]))

            if 10*ratio > 1:
                dist = max(CDF(shortpath[i]-nicepath[-1]).abs(), CDF(shortpath[i]-shortpath[i+1]).abs())
                next = simplify_complex(shortpath[i], dist/RDF(ratio)/15)
                if not next == shortpath[-1]:
                    nicepath.append(next)

        nicepath.append(shortpath[-1])

        return nicepath

    def path(self, only_holomorphic_forms=False):
        if self._explicit_path or not config.nice_paths:
            return self._path
        else:
            return self._nice_path(only_holomorphic_forms)