# -*- coding: utf-8 -*-

# lefschetz-family
# Copyright (C) 2021  Eric Pichon-Pharabod

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

try:
    import sage.all
except ImportError:
    import sage.all__sagemath_modules


from .numperiods.family import Family
from .numperiods.integerRelations import IntegerRelations
from ore_algebra import *

from sage.modules.free_module_element import vector
from sage.rings.qqbar import QQbar
from sage.functions.other import factorial
from sage.functions.other import floor
from sage.matrix.constructor import matrix
from sage.rings.integer_ring import ZZ
from sage.matrix.special import identity_matrix
from sage.matrix.special import diagonal_matrix
from sage.matrix.special import block_matrix
from sage.matrix.special import block_diagonal_matrix
from sage.matrix.special import zero_matrix
from sage.arith.functions import lcm


from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ
from sage.schemes.toric.weierstrass import WeierstrassForm
from sage.misc.flatten import flatten

from sage.modules.free_quadratic_module_integer_symmetric import IntegralLattice

from sage.functions.other import ceil

from .voronoi import FundamentalGroupVoronoi
from .integrator import Integrator
from .util import Util
from .context import Context
from .monodromyRepresentation import MonodromyRepresentation
from .monodromyRepresentationFiberedProduct import MonodromyRepresentationFibreProduct
from sage.functions.other import binomial


import logging
import time

logger = logging.getLogger(__name__)

def tens1(M):
    return block_diagonal_matrix([M, M], subdivide=False)
def tens2(M):
    return block_matrix(list(map(lambda r:list(map(lambda c: c*identity_matrix(M.nrows()), r)), M.rows())), subdivide=False)
def tensor_prod(a,b):
    return vector([a[0]*b[0], a[1]*b[0], a[0]*b[1], a[1]*b[1]])

def derivatives_coords(S, w, k):
    derivatives = [S.P.parent()(0), w]
    for k in range(k):
        derivatives += [S._derivative(derivatives[-1], S.P)] 
    return S.family._coordinates(derivatives, S.basepoint)

def derivative_of_product(a, b, n):
    return sum([binomial(n, i) * tensor_prod(a.row(i+1), b.row(n-i+1)) for i in range(n+1)])

class FibreProduct(object):
    def __init__(self, S1, S2, correction=None, **kwds) -> None:
        """S1 and S2 are two elliptic surfaces with the same basepoint
        """
        
        self.ctx = Context(**kwds)
        
        self._S1 = S1
        self._S2 = S2

        if correction!=None:
            self._correction = correction

        assert S1.basepoint == S2.basepoint, "the basepoint of the input elliptic surfaces should be the same"
        self._basepoint=S1.basepoint
    
    @property
    def correction(self):
        if not hasattr(self, "_correction"):
            pmin=None
            L1 = self.S1.family.picard_fuchs_equation(vector([1,0]))
            L2 = self.S2.family.picard_fuchs_equation(vector([1,0]))
            L = L1.symmetric_product(L2)
            for v in L.local_basis_monomials(0):
                if "log" in str(v):
                    continue
                if str(v)=="1":
                    p = 0
                elif str(v)==str(L.base_ring().gen(0)):
                    p = 1
                elif "/sqrt" in str(v):
                    p=-1/2
                elif "sqrt" in str(v):
                    p=1/2
                else:
                    p = QQ(str(v)[2:].replace(")","").replace("(",""))
                if pmin==None or p<pmin:
                    pmin = p
            correction = 1/L.base_ring().gen(0)**ceil(pmin)
            self._correction = correction
        return self._correction
    
    @property
    def S1(self):
        return self._S1
    @property
    def S2(self):
        return self._S2
    
    @property
    def basepoint(self):
        return self._basepoint

    @property
    def critical_values(self):
        if not hasattr(self, "_critical_values"):
            self._critical_values =[c for c in Util.remove_duplicates(self.S1.critical_values + self.S2.critical_values) if c != "infinity"]
        return self._critical_values

    @property
    def fundamental_group(self):
        if not hasattr(self,'_fundamental_group'):
            fundamental_group = FundamentalGroupVoronoi([e for e in self.critical_values if e!= 'infinity'], self.basepoint)
            fundamental_group.sort_loops()
            self._critical_values = fundamental_group.points[1:]
            self._fundamental_group = fundamental_group
        return self._fundamental_group
    
    @property
    def paths(self):
        if not hasattr(self, '_paths'):
            self._paths = self.fundamental_group.pointed_loops_vertices
        return self._paths

    @property
    def thimbles(self):
        return self.monodromy_representation.thimbles

    @property
    def permuting_cycles(self):
        return self.monodromy_representation.permuting_cycles
    
    @property
    def extensions(self):
        """Representants of the extensions of the elliptic surface."""
        return self.monodromy_representation.extensions

    @property
    def borders_of_thimbles(self):
        return self.monodromy_representation.borders_of_thimbles

    @property
    def infinity_loops(self):
        """The linear combinations of thimbles that correspond to extensions along the (trivial) loop around infinity."""
        return self.monodromy_representation.infinity_loops
        
    @property
    def vanishing_cycles(self):
        if not hasattr(self, "_vanishing_cycles"):
            self._vanishing_cycles = [[(M-1)*v for v in permuting_cycles_of_M] for permuting_cycles_of_M, M in zip(self.permuting_cycles, self.monodromy_matrices)]
        return self._vanishing_cycles

    @property
    def infinity_loops(self):
        """The linear combinations of thimbles that correspond to extensions along the (trivial) loop around infinity."""
        return self.monodromy_representation.infinity_loops
    
    def lift(self, v):
        return self.monodromy_representation.resolve(self.monodromy_representation.lift(self.monodromy_representation.desingularise(v)))

    @property
    def homology(self):
        return self.monodromy_representation.homology
    
    def integrate(self, L):
        logger.info("Computing numerical transition matrices of operator of order %d and degree %d (%d edges total)."% (L.order(), L.degree(), len(self.fundamental_group.edges)))
        begin = time.time()

        integrator = Integrator(self.fundamental_group, L, self.ctx.nbits)
        transition_matrices = integrator.transition_matrices
        
        end = time.time()
        duration_str = time.strftime("%H:%M:%S",time.gmtime(end-begin))
        if end-begin >= 24*60*60:
            ndays = (end-begin)//24*60*60
            duration_str = str(ndays)+"d "+duration_str
        logger.info("Integration finished -- total time: %s."% (duration_str))

        return transition_matrices
    
    def cyclic_form_and_vectors(self):
        L1s = [self.S1.family.picard_fuchs_equation(v) for v in identity_matrix(2)]
        L2s = [self.S2.family.picard_fuchs_equation(v) for v in identity_matrix(2)]
        found = False
        for i1, L1 in enumerate(L1s):
            for i2, L2 in enumerate(L2s):
                Ltot = L1.symmetric_product(L2)
                if Ltot.order() ==4:
                    return self.S1.family.basis[i1], self.S1.family.basis[i2], Ltot

    @property
    def monodromy_matrices(self):
        if not hasattr(self,'_monodromy_matrices'):
            logger.info("Computing monodromy matrices")
            w1, w2, Ltot = self.cyclic_form_and_vectors()
            w1, w2 = self.S1.P.parent()(w1), self.S2.P.parent()(w2)

            Dt, = Ltot.parent().gens()
            
            transition_matrices = self.integrate(Ltot*Dt)
            
            d1 = derivatives_coords(self.S1, w1, 3)
            d2 = derivatives_coords(self.S2, w2, 3)
            derivatives_tensor = matrix([vector([0]*4)] + [derivative_of_product(d1, d2, i) for i in range(4)])
            
            pM = tens1(self.S1.fibre.period_matrix)*tens2(self.S2.fibre.period_matrix)
            
            integration_correction = diagonal_matrix([1/ZZ(factorial(k)) for k in range(5)])
            init_cond = (integration_correction * derivatives_tensor).submatrix(1,0)
            
            monodromy_matrices = [pM.inverse() * init_cond.inverse() * M.submatrix(1,1) * init_cond * pM for M in transition_matrices]
            monodromy_matrices = [M.change_ring(ZZ) for M in monodromy_matrices]


            Mtot = identity_matrix(4)
            for M in monodromy_matrices:
                Mtot = M * Mtot
            if Mtot != identity_matrix(4):
                self._critical_values = self.critical_values + ["infinity"]

                transition_matrix_infinity = 1
                for M in transition_matrices:
                    transition_matrix_infinity = M * transition_matrix_infinity
                transition_matrices += [transition_matrix_infinity.inverse()]
                
                monodromy_matrices += [(Mtot.inverse()).change_ring(ZZ)]
                
                path_infinity = -sum(self.paths)
                self._paths += [path_infinity]

            self._monodromy_matrices = monodromy_matrices
        return self._monodromy_matrices

    @property
    def monodromy_matrices_morsification(self):
        return [[Ms[2*i]*Ms[2*i+1] for i in range(len(Ms)/2)] for Ms in self.monodromy_representation.monodromy_matrices_desingularisation]
    
    @property
    def monodromy_representation(self):
        if not hasattr(self,'_monodromy_representation'):
            monodromy_matrices = self.monodromy_matrices
            expected_types = []
            for c in self.critical_values:
                if c in self.S1.critical_values:
                    expected_types += [self.S1.types[self.S1.critical_values.index(c)]]
                else:
                    expected_types += ["I0"]
            fibre_intersection_product = tens1(self.S1.fibre.intersection_product)*tens2(self.S2.fibre.intersection_product)
            self._monodromy_representation = MonodromyRepresentationFibreProduct(monodromy_matrices, fibre_intersection_product, expected_types)
        return self._monodromy_representation

    @property
    def cohomology_internal(self):
        """a cohomology class is represented by `(w1, w2, denom)` where `w1` is a form of `self.S1`, `w2` is a form of `self.S2` and `denom` is a rational function of the parameter."""
        if not hasattr(self,"_cohomology"):
            S = self.S1.P.parent()
            R = S.base_ring()
            
            Swithu = PolynomialRing(R, ['t', 'u'])
            t,u = Swithu.gens() 
            phi = S.hom([t*u])
            phii = Swithu.hom([S.gens()[0], 1])
            f1 = Swithu(1)/phi(self.S1.P) # f1 is the rational function of which the residue is the holomorphic form of S1
            
            derivatives = [f1]
            for i in range(3):
                derivatives += [derivatives[-1].derivative(u)]
            nums = [phii(phi(self.S1.P**(i+1))*w)/factorial(i) for i, w in enumerate(derivatives)]

            w2 = vector([1,0])
            w1s = [S(Swithu(n)) for n in nums]
            w1s, denom = self.S1.family.coordinates(w1s)

            self._cohomology = [(w1, w2, denom) for w1 in w1s]
        return self._cohomology

    @property
    def picard_fuchs_equations(self):
        if not hasattr(self,"_picard_fuchs_operators"):
            picard_fuchs_equations = []
            for w1, w2, denom in self.cohomology_internal:
                L1 = self.S1.family.picard_fuchs_equation(w1)
                L2 = self.S2.family.picard_fuchs_equation(w2)
                L = L1.symmetric_product(L2)*denom
                L = L*(1/self.correction)
                mul = lcm([c.denominator() for c in L.coefficients()])
                L = mul*L
                L = L.change_ring(L.base_ring().ring_of_integers())
                picard_fuchs_equations += [L]
            self._picard_fuchs_equations = picard_fuchs_equations
        return self._picard_fuchs_equations
    
    @property
    def transition_matrices(self):
        if not hasattr(self, '_transition_matrices'):
            transition_matrices = []
            for L in self.picard_fuchs_equations:
                L = L* L.parent().gens()[0]
                transition_matrices += [self.integrate(L)]
                if "infinity" in self.critical_values:
                    transition_matrix_infinity = 1
                    for M in transition_matrices[-1]:
                        transition_matrix_infinity = M*transition_matrix_infinity
                    transition_matrices[-1] += [transition_matrix_infinity**(-1)]
            self._transition_matrices = transition_matrices
        return self._transition_matrices
    
    @property
    def integrated_thimbles(self):
        if not hasattr(self, '_integrated_thimbles'):
            integration_correction = diagonal_matrix([1/ZZ(factorial(k)) for k in range(5)])
            pM = tens1(self.S1.fibre.period_matrix)*tens2(self.S2.fibre.period_matrix)

            _integrated_thimbles_all = []

            for transition_matrices, w in zip(self.transition_matrices, self.cohomology_internal):
                w1, w2, denom = w

                numerator1 = (w1[0]*self.S1.P + w1[1]*self.S1.family.pol.parent()(self.S1.family.coho1.basis()[1]))*self.correction/denom
                numerator2 = (w2[0]*self.S2.P + w2[1]*self.S2.family.pol.parent()(self.S2.family.coho1.basis()[1]))
                d1 = derivatives_coords(self.S1, numerator1, 3)
                d2 = derivatives_coords(self.S2, numerator2, 3)
                derivatives_tensor = matrix([vector([0]*4)] + [derivative_of_product(d1, d2, i) for i in range(4)])
                initial_conditions = integration_correction * derivatives_tensor * pM

                _integrated_thimbles = []
                for i, ps in enumerate(self.permuting_cycles):
                    for p in ps:
                        _integrated_thimbles += [(transition_matrices[i] * initial_conditions.submatrix(0,0,transition_matrices[i].nrows()) * p)[0]]
                _integrated_thimbles_all += [_integrated_thimbles]
            self._integrated_thimbles = _integrated_thimbles_all
        return self._integrated_thimbles
    
    @property
    def primary_lattice(self):
        return self.monodromy_representation.primary_lattice
    
    @property
    def primary_periods(self):
        if not hasattr(self, "_primary_periods"):
            homology_mat = matrix(self.extensions).transpose()
            integrated_thimbles =  matrix(self.integrated_thimbles)
            self._primary_periods = integrated_thimbles * homology_mat
        return self._primary_periods
    

    @property
    def components_of_singular_fibres(self):
        return self.monodromy_representation.components_of_singular_fibres

    @property
    def period_matrix(self):
        if not hasattr(self, '_period_matrix'):
            periods_tot = block_matrix([[self.primary_periods, zero_matrix(len(self.cohomology_internal), len(flatten(self.components_of_singular_fibres)))]])
            
            res = self.primary_lattice.solve_right(matrix([self.monodromy_representation.proj(v) for v in self.homology]).transpose())
            self._period_matrix = periods_tot * res
        return self._period_matrix
    
    @property
    def intersection_product(self):
        return -self.monodromy_representation.intersection_product_resolution
    

    @property
    def types(self):
        return self.monodromy_representation.types