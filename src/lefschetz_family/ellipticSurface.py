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

from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ
from sage.schemes.toric.weierstrass import WeierstrassForm
from sage.misc.flatten import flatten

from sage.modules.free_quadratic_module_integer_symmetric import IntegralLattice

from .voronoi import FundamentalGroupVoronoi
from .integrator_simultaneous import IntegratorSimultaneous
from .integrator import Integrator
from .util import Util
from .context import Context
from .hypersurface import Hypersurface
from .monodromyRepresentationEllipticSurface import MonodromyRepresentationEllipticSurface
from .ellipticSingularity import EllipticSingularities

import logging
import time

logger = logging.getLogger(__name__)


class EllipticSurface(object):
    def __init__(self, P, basepoint=None, fibration=None, **kwds) -> None:
        """P, a homogeneous polynomial defining an elliptic surface.

        This class aims at computing an effective basis of the homology group H_n(X), 
        given as lifts of paths through a Lefschetz fibration.
        """
        
        self.ctx = Context(**kwds)
        
        # maybe put P in Weierstrass form ?
        # flatPolRing = PolynomialRing(QQ, ['a','b','c','t'])
        # [a,b,c,t] = flatPolRing.gens()
        # weierstrass_coefs = WeierstrassForm(P(t,a,b,c), [a,b,c])
        # Qt = PolynomialRing(QQ, 't')
        # t= P.parent().gens()[0]
        # weierstrass_coefs =  [c(t=t) for c in weierstrass_coefs]
        # t= P.parent().gens()[0]
        # X,Y,Z = P.base_ring().gens()
        # P = -Y**2*Z + X**3 + weierstrass_coefs[0]*X*Z**2 + weierstrass_coefs[1]*Z**3

        self._P = P
        self._fibration = fibration
        
        if basepoint!= None and not self.ctx.debug: # it is useful to be able to specify the basepoint to avoid being stuck in arithmetic computations if critical values have very large modulus
            assert basepoint not in self.critical_values, "basepoint is not regular"
            self._basepoint = basepoint

        if not self.ctx.debug:
            fg = self.fundamental_group # this allows reordering the critical points straight away and prevents shenanigans. There should be a better way to do this

        self._family = Family(self.P, path=[self.basepoint-1, self.basepoint])
    
    def __str__(self):
        sP= str(self.P)
        if len(sP) >40:
            sP = sP[:20] +"<...>"+ sP[-20:]
        s = "Elliptic surface with defining equation " + sP
        return s
    
    def __repr__(self):
        sP= str(self.P)
        if len(sP) >40:
            sP = sP[:20] +"<...>"+ sP[-20:]
        s = "Elliptic surface with defining equation " + sP
        return s

    @property
    def monodromy_representation(self):
        if not hasattr(self,'_monodromy_representation'):
            self._monodromy_representation = MonodromyRepresentationEllipticSurface(self.monodromy_matrices, self.fibre.intersection_product)
        return self._monodromy_representation
    
    @property
    def intersection_product(self):
        return self.monodromy_representation.intersection_product

    @property
    def primary_periods(self):
        if not hasattr(self, '_primary_periods'):
            homology_mat = matrix(self.extensions).transpose()
            integrated_thimbles =  matrix(self.integrated_thimbles)
            self._primary_periods = integrated_thimbles * homology_mat
        return self._primary_periods
    
    @property
    def period_matrix(self):
        if not hasattr(self, '_period_matrix'):
            periods_tot = block_matrix([[self.primary_periods, zero_matrix(len(self.holomorphic_forms), len(flatten(self.components_of_singular_fibres))+2)]])
            self._period_matrix = periods_tot * matrix(self.primary_lattice).inverse()
        return self._period_matrix

    @property
    def P(self):
        return self._P

    @property
    def picard_fuchs_equations(self):
        if not hasattr(self,'_picard_fuchs_equations'):
            self._picard_fuchs_equations = [self.family.picard_fuchs_equation(vector([w,0])) for w in self.holomorphic_forms]
        return self._picard_fuchs_equations
    
    @property
    def family(self):
        return self._family
    
    @property
    def discriminant(self):
        if not hasattr(self,'_discriminant'):
            flatPolRing = PolynomialRing(QQ, ['a','b','c','t'])
            [a,b,c,t] = flatPolRing.gens()
            weierstrass_coefs = WeierstrassForm(self.P(t,a,b,c), [a,b,c])
            Qt = PolynomialRing(QQ, 't')
            t = Qt.gens()[0]
            weierstrass_coefs =  [c(t=t) for c in weierstrass_coefs]
            self._discriminant=Qt(4*weierstrass_coefs[0](t=t)**3 + 27*weierstrass_coefs[1](t=t)**2)
        return self._discriminant
    
    @property
    def critical_values(self):
        if not hasattr(self,'_critical_values'):
            self._critical_values=self.discriminant.roots(QQbar, multiplicities=False)
        return self._critical_values
    
    @property
    def monodromy_matrices(self):
        if not hasattr(self, '_monodromy_matrices'):
            n = len(self.fibre.extensions) 
            
            cyclic_form = self.cyclic_form
            w = cyclic_form[0]*self.P + cyclic_form[1]*self.family.coho1.basis()[1]

            integration_correction = diagonal_matrix([1/ZZ(factorial(k)) for k in range(n+1)])
            derivatives_at_basepoint = self.derivatives_values_at_basepoint(w)
            cohomology_fibre_to_family = self.family._coordinates([self.family.pol.parent()(w) for w in self.fibre.cohomology_internal], self.basepoint)

            initial_conditions = integration_correction * derivatives_at_basepoint * cohomology_fibre_to_family.inverse()
            initial_conditions = initial_conditions.submatrix(1,0)

            cohomology_monodromies = [initial_conditions.inverse() * M.submatrix(1,1) * initial_conditions for M in self.cyclic_transition_matrices]

            Ms = [(self.fibre.period_matrix.inverse() * M * self.fibre.period_matrix) for M in cohomology_monodromies]
            if not self.ctx.debug:
                Ms = [M.change_ring(ZZ) for M in Ms]
            
            Mtot = identity_matrix(2)
            for M in Ms:
                Mtot = M * Mtot
            if Mtot != identity_matrix(2):
                self._critical_values = self.critical_values+["infinity"]
                transition_matrix_infinity = 1
                for M in self.cyclic_transition_matrices:
                    transition_matrix_infinity = M*transition_matrix_infinity
                self._cyclic_transition_matrices += [transition_matrix_infinity**(-1)]
                Ms += [(Mtot.inverse()).change_ring(ZZ)]
                
                pathinfinity = -sum(self.paths)
                self._paths+=[pathinfinity]
            
            self._monodromy_matrices = Ms
        return self._monodromy_matrices
    
    @property
    def thimbles_confluence(self):
        if not hasattr(self, '_thimbles_confluence'):
            blocks =[]
            for i, pcs in enumerate(self.permuting_cycles):
                decompositions = []
                for p in pcs:
                    decomposition = []
                    for M, v in zip(self.monodromy_matrices_morsification[i], self.vanishing_cycles_morsification[i]):
                        decomposition += [(M-1)*p/v]
                        p = M*p
                    decompositions+=[decomposition]
                blocks+= [matrix(decompositions)]
            self._thimbles_confluence = block_diagonal_matrix(blocks).change_ring(ZZ)
        return self._thimbles_confluence
    
    def morsify(self, v):
        """Given an extension of the surface, yields its description as an extension of the morsification."""
        return self.monodromy_representation.desingularise(v)

    @property
    def vanishing_cycles_morsification(self):
        if not hasattr(self, '_vanishing_cycles_morsification'):
            self._vanishing_cycles_morsification = [[(M-1).transpose().image().gens()[0] for M in Ms] for Ms in self.monodromy_matrices_morsification]
        return self._vanishing_cycles_morsification
    
    @property
    def components_of_singular_fibres(self):
        return self.monodromy_representation.components_of_singular_fibres

    
    @property
    def monodromy_matrices_morsification(self):
        return self.monodromy_representation.monodromy_matrices_desingularisation

    @property
    def fibre(self):
        if not hasattr(self,'_fibre'):
            self._fibre = Hypersurface(self.P(self.basepoint), nbits=self.ctx.nbits, fibration=self._fibration)
            if self._fibre.intersection_product == matrix([[0,-1], [1,0]]):
                del self._fibre._monodromy_representation
                self._fibre.monodromy_representation._extensions_desingularisation = list(reversed(self._fibre.monodromy_representation.extensions_desingularisation))
                self._fibre.monodromy_representation._extensions = list(reversed(self._fibre.monodromy_representation.extensions))
                del self._fibre._intersection_product
                del self._fibre._intersection_product_modification
            assert self._fibre.intersection_product == matrix([[0,1], [-1,0]])
        return self._fibre

    @property
    def thimbles(self):
        return self.monodromy_representation.thimbles

    @property
    def permuting_cycles(self):
        return self.monodromy_representation.permuting_cycles
    
    @property
    def permuting_cycles_morsification(self):
        return self.monodromy_representation.permuting_cycles_desingularisation

    @property
    def borders_of_thimbles(self):
        return self.monodromy_representation.borders_of_thimbles

    @property
    def infinity_loops(self):
        """The linear combinations of thimbles that correspond to extensions along the (trivial) loop around infinity."""
        return self.monodromy_representation.infinity_loops

    @property
    def extensions_morsification(self):
        """Representant of the extensions of the morsification of the elliptic surface. 
        Along with the fibre and section, this constitutes a basis for the second homology group of the surface. 
        The singular fibre components are identified at the end of the list."""
        return self.monodromy_representation.extensions_desingularisation
    
    @property
    def extensions(self):
        """Representants of the extensions of the elliptic surface."""
        return self.monodromy_representation.extensions

    @property
    def primary_lattice(self):
        return self.monodromy_representation.primary_lattice
   
    def lift(self, v):
        """Given a combination of thimbles of morsification, gives the corresponding homology class"""
        return self.monodromy_representation.lift(v)

    @property
    def homology(self):
        return self.monodromy_representation.homology


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
    def cyclic_form(self):
        if not hasattr(self, '_cyclic_form'):
            for v in [[1,0], [0,1], [1,1]]:
                L = self.family.picard_fuchs_equation(vector(v))
                if L.order() == 2:
                    break
            assert L.order() == 2, "could not find cyclic  Picard-Fuchs equation"
            self._cyclic_form = v
            self._cyclic_picard_fuchs_equation = L
        return self._cyclic_form
    
    @property
    def cyclic_picard_fuchs_equation(self):
        if not hasattr(self, '_cyclic_picard_fuchs_equation'):
            self.cyclic_form
        return self._cyclic_picard_fuchs_equation
    
    @property
    def cyclic_transition_matrices(self):
        if not hasattr(self, '_cyclic_transition_matrices'):
            L = self.cyclic_picard_fuchs_equation
            L = L* L.parent().gens()[0]
            self._cyclic_transition_matrices = self.integrate(L)
        return self._cyclic_transition_matrices
    
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

    def forget_transition_matrices(self):
        del self._transition_matrices
        del self._integrated_thimbles
        
    @property
    def integrated_thimbles(self):
        if not hasattr(self, '_integrated_thimbles'):
        
            s=len(self.fibre.extensions)
            r=len(self.thimbles)
            
            pM = self.fibre.period_matrix
            integration_correction = diagonal_matrix([1/ZZ(factorial(k)) for k in range(s+1)])

            _integrated_thimbles_all=[]
            for transition_matrices, w in zip(self.transition_matrices, self.holomorphic_forms):
                derivatives_at_basepoint = self.derivatives_values_at_basepoint(w)
                cohomology_fibre_to_family = self.family._coordinates([self.family.pol.parent()(w) for w in self.fibre.cohomology_internal], self.basepoint)
                
                initial_conditions = integration_correction * derivatives_at_basepoint * cohomology_fibre_to_family.inverse() * pM
                initial_conditions = initial_conditions.submatrix(0,0,transition_matrices[0].ncols())
                _integrated_thimbles = []
                for i, ps in enumerate(self.permuting_cycles):
                    _integrated_thimbles += [(transition_matrices[i] * initial_conditions * p)[0] for p in ps]
                _integrated_thimbles_all += [_integrated_thimbles]
            self._integrated_thimbles = _integrated_thimbles_all
        return self._integrated_thimbles


    def derivatives_values_at_basepoint(self, w):
        s = len(self.fibre.extensions)
        derivatives = [self.P.parent()(0), w]
        for k in range(s-1):
            derivatives += [self._derivative(derivatives[-1], self.P)] 
        return self.family._coordinates(derivatives, self.basepoint)


    @staticmethod
    def _derivative(A, P): 
        """computes the numerator of the derivative of A/P^k"""
        field = P.parent().fraction_field()
        return field(A).derivative() - A*P.derivative()         

    @property
    def fundamental_group(self):
        if not hasattr(self,'_fundamental_group'):
            begin = time.time()

            fundamental_group = FundamentalGroupVoronoi(self.critical_values, self.basepoint) # access future delaunay implem here
            fundamental_group.sort_loops()

            end = time.time()
            duration_str = time.strftime("%H:%M:%S",time.gmtime(end-begin))
            if end-begin >= 24*60*60:
                ndays = (end-begin)//24*60*60
                duration_str = str(ndays)+"d "+duration_str
            logger.info("Fundamental group computed in %s."% (duration_str))

            self._critical_values = fundamental_group.points[1:]
            self._fundamental_group = fundamental_group
        return self._fundamental_group

    @property
    def paths(self):
        if not hasattr(self, "_paths"):
            self._paths = self.fundamental_group.pointed_loops_vertices
        return self._paths

    @property
    def basepoint(self):
        if  not hasattr(self, '_basepoint'):
            shift = 1
            reals = [self.ctx.CF(c).real() for c in self.critical_values]
            xmin, xmax = min(reals), max(reals)
            self._basepoint = Util.simple_rational(xmin - (xmax-xmin)*shift, (xmax-xmin)/10)
        return self._basepoint


    @property
    def neron_severi(self):
        if  not hasattr(self, '_neron_severi'):
            self._neron_severi = IntegerRelations(self.period_matrix.transpose()).basis.rows()
        return self._neron_severi
    
    @property
    def transcendental_lattice(self):
        if  not hasattr(self, '_transcendental_lattice'):
            IL = IntegralLattice(self.intersection_product)
            self._transcendental_lattice = IL.orthogonal_complement(self.neron_severi).basis()
        return self._transcendental_lattice

    @property
    def trivial_lattice(self):
        if  not hasattr(self, '_trivial_lattice'):
            components_of_singular_fibres = flatten(self.components_of_singular_fibres)
            self._trivial_lattice = [self.lift(v) for v in components_of_singular_fibres] + [self.fibre_class, self.section]
        return self._trivial_lattice
    
    @property
    def fibre_class(self):
        return self.monodromy_representation.fibre_class
    @property
    def section(self):
        return self.monodromy_representation.section
    
    @property
    def mordell_weil(self):
        if  not hasattr(self, '_mordell_weil'):
            NS = matrix(self.neron_severi).change_ring(ZZ).image()
            Triv = NS.submodule(self.trivial_lattice).change_ring(ZZ)
            self._mordell_weil = NS/Triv
        return self._mordell_weil
    
    @property
    def essential_lattice(self):
        if  not hasattr(self, '_essential_lattice'):
            IL = IntegralLattice(self.intersection_product)
            self._essential_lattice = IL.sublattice(self.neron_severi).orthogonal_complement(self.trivial_lattice).basis_matrix()
        return self._essential_lattice
    
    @property
    def mordell_weil_lattice(self):
        ess_coords = matrix(self.neron_severi).solve_left(self.essential_lattice).change_ring(ZZ)
        triv_coords = matrix(self.neron_severi).solve_left(matrix(self.trivial_lattice)).change_ring(ZZ)
        coords = block_matrix([[ess_coords],[triv_coords]])
        projection_temp = block_diagonal_matrix([identity_matrix(len(self.essential_lattice.rows())), zero_matrix(len(self.trivial_lattice))])
        orth_proj = coords.inverse() * projection_temp * coords

        quotient_basis = Util.find_complement(triv_coords, primitive=False)
        # quotient_basis = ess_coords
        coordsMW = quotient_basis*orth_proj
        A = coordsMW*matrix(self.neron_severi)
        return A*self.intersection_product*A.transpose()

    @property
    def types(self):
        return self.monodromy_representation.types

    @property
    def holomorphic_forms(self):
        if not hasattr(self, "_holomorphic_forms"):
            L = self.family.picard_fuchs_equation(vector([1,0]))
            if L.order()==1:
                return self._holomorphic_form_order_1(L)
            
            t = L.base_ring().gens()[0]

            bs = []
            rs = []
            roots = L.leading_coefficient().roots(QQbar, multiplicities=False)
            for r in roots:
                if r in self.critical_values:
                    i = self.critical_values.index(r)
                    ty, _, n = EllipticSingularities.monodromy_class(self.monodromy_matrices[i])
                    bs += [self._b(L, r, ty, n)]
                else:
                    bs += [self._b(L, r, "I", 0)]
                rs += [self._rnorm(L, r)]

            L2 = L.annihilator_of_composition(1/t)
            if L2.leading_coefficient()(0) ==0:
                r = "infinity"
                roots += [r]
                if r in self.critical_values:
                    i = self.critical_values.index(r)
                    ty, _, n = EllipticSingularities.monodromy_class(self.monodromy_matrices[i])
                    bs += [self._b(L2, 0, ty, n)]
                else:
                    bs += [self._b(L2, 0, "I", 0)]
                rs += [self._rnorm(L2, 0)]
            ords = [0  if r!="infinity" else -2*2 for r in roots]
            
            div = - vector(rs) - vector(bs) + vector(ords)

            Z = 1
            pols = []
            degrees = []
            for i, r in enumerate(roots):
                if r=="infinity":
                    continue
                pol = r.minpoly()
                if pol in pols:
                    assert degrees[pols.index(pol)] == div[i]
                    continue
                pols += [pol]
                degrees += [div[i]]
                Z = Z*pol**(-div[i])
            Z = Z(t)

            Dt = L.parent().gens()[0]
            W = (Dt + L.coefficients()[1]/L.coefficients()[2]).rational_solutions()[0][0]

            # assert sum(div) ==0, "Multiple or no holomorphic forms, not implemented yet"
            res = [-Z/W*t**i for i in range(0, sum(div)+1)]
            res = [f/(f.numerator().leading_coefficient()/f.denominator().leading_coefficient()) for f in res]
            self._holomorphic_forms = res
        return self._holomorphic_forms
    
    @staticmethod
    def _holomorphic_form_order_1(L):
        return [L.base_ring()(1)]

    @staticmethod
    def _rnorm(L, p):
        R = L.base_ring()
        t = R.gens()[0]
        return floor((L.local_basis_monomials(p)[0]**12)(t=t).degree(t)/12)
    
    @staticmethod
    def _b(L, p, ty, n):
        if ty=="I" and n>0:
            return -1
        R = L.base_ring()
        t = R.gens()[0]
        m = L.local_basis_monomials(p)[1] / L.local_basis_monomials(p)[0]
        m=m(t=t+p)
        if ty=="I":
            l = (R(m).degree()-2)
            if l==-1:
                return 0
            else:
                return l+1
        if ty=="II":
            return (R(m**6).degree()-2)/6
        if ty=="III":
            return (R(m**4).degree()-2)/4
        if ty=="IV":
            return (R(m**3).degree()-2)/3
        if ty=="I*":
            if n==0:
                return (R(m**2).degree()-2)/2
            else:
                return -1
        if ty=="II*":
            return (R(m**6).degree()-4)/6 - 1
        if ty=="III*":
            return (R(m**4).degree()-2)/4 - 1
        if ty=="IV*":
            return (R(m**3).degree()-1)/3 - 1

    def integrate_forms_on_thimbles(self, forms):
        transition_matrices = self.transition_matrices_of_forms(forms)
        if "infinity" in self.critical_values:
            transition_matrix_infinity = 1
            for M in transition_matrices:
                transition_matrix_infinity = M*transition_matrix_infinity
            transition_matrices += [transition_matrix_infinity.inverse()]
    
        s = len(self.fibre.extensions)
        R = len(forms)
        
        expand = zero_matrix(R,s).stack(identity_matrix(s))

        integrated_thimbles = []
        for tM, ps in zip(transition_matrices, self.permuting_cycles):
            integrated_thimbles += [(tM * expand * self.fibre.period_matrix * p)[:R] for p in ps]

        return matrix(integrated_thimbles).transpose()

    def integrate_forms(self, forms):
        primary_periods = self.integrate_forms_on_thimbles(forms) * matrix(self.extensions).transpose()
        periods_tot = block_matrix([[primary_periods, zero_matrix(primary_periods.nrows(), len(flatten(self.components_of_singular_fibres))+2)]])
        periods = periods_tot * matrix(self.primary_lattice).inverse()
        return periods


    def transition_matrices_of_forms(self, forms):
        rat_coefs = self.family.coordinates(forms)
        logger.info("Computing transition matrices of all forms (%d rational vector(s))."% (rat_coefs[0].nrows()))
        transition_matrices = self._compute_transition_matrices_simultaneous(rat_coefs)
        return transition_matrices

    def _compute_transition_matrices_simultaneous(self, rat_coefs):
        gaussmanin = self.family.gaussmanin()
        begin = time.time()
        integrator = IntegratorSimultaneous(self.fundamental_group, rat_coefs, gaussmanin, nbits=self.ctx.nbits)
        transition_matrices = integrator.transition_matrices
        if hasattr(self, '_transition_matrices_holomorphic'):
            Rholo = len(self.holomorphic_forms)
            R = len(self.cohomology) - Rholo
            r = len(self.fibre.cohomology_internal)
            intold = [M.submatrix(0,Rholo,Rholo,r) for M in self.transition_matrices_holomorphic]
            intnew = [M.submatrix(0,R,R,r) for M in transition_matrices]
            GM = [M.submatrix(R,R) for M in transition_matrices]
            transition_matrices = [block_matrix([[1,0, a],[0,1, b], [0,0,c]]) for a,b,c in zip(intold, intnew, GM)]
        end = time.time()
        duration_str = time.strftime("%H:%M:%S",time.gmtime(end-begin))
        if end-begin >= 24*60*60:
            ndays = (end-begin)//24*60*60
            duration_str = str(ndays)+"d "+duration_str
        logger.info("Integration finished -- total time: %s."% (duration_str))
        return transition_matrices