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