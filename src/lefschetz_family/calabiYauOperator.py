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

from .numperiods.integerRelations import IntegerRelations
from ore_algebra import *

from sage.modules.free_module_element import vector
from sage.rings.qqbar import QQbar
from sage.rings.integer_ring import ZZ
from sage.rings.number_field.number_field import NumberField
from sage.rings.imaginary_unit import I
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ
from sage.rings.finite_rings.integer_mod_ring import IntegerModRing
from sage.functions.other import floor
from sage.matrix.constructor import matrix
from sage.matrix.special import diagonal_matrix
from sage.matrix.special import zero_matrix
from sage.arith.functions import lcm
from sage.arith.misc import factor
from sage.symbolic.constants import pi
from sage.functions.transcendental import zeta
from sage.misc.misc_c import prod
from sage.groups.matrix_gps.symplectic import Sp
from sage.matrix.matrix_space import MatrixSpace

from sage.misc.flatten import flatten
from sage.misc.functional import log

from .voronoi import FundamentalGroupVoronoi
from .integrator import Integrator
from .util import Util
from .context import Context

import logging

logger = logging.getLogger(__name__)


class CalabiYauOperator(object):
    def __init__(self, L, basepoint=None, **kwds):
        """L, a differential equation 
        """
        
        self.ctx = Context(**kwds)

        self._L = L
        
        if basepoint!= None: # it is useful to be able to specify the basepoint to avoid being stuck in arithmetic computations if critical values have very large modulus
            assert basepoint not in self.singular_values, "basepoint is not regular"
            self._basepoint = basepoint

        if not self.ctx.debug:
            fg = self.fundamental_group # this allows reordering the critical points straight away and prevents shenanigans. There should be a better way to do this
    
    @property
    def L(self):
        """returns the Calabi-Yau operator"""
        return self._L
    
    @property
    def order(self):
        return self.L.order()
    
    @property
    def basepoint(self):
        if not hasattr(self, "_basepoint"):
            self._basepoint = QQ(10)**(min([floor(log(abs(r),10)) for r in self.singular_values if r!=0])-1)
        return self._basepoint
   
    @property
    def singular_values(self):
        if not hasattr(self, "_singular_values"):
            self._singular_values = self.L.leading_coefficient().roots(QQbar, multiplicities=False)
        return self._singular_values
 
    @property
    def fundamental_group(self):
        if not hasattr(self, "_fundamental_group"):
            fundamental_group = FundamentalGroupVoronoi(self.singular_values, self.basepoint)
            self._singular_values = [self._singular_values[i] for i in fundamental_group.sort_loops()]
            self._fundamental_group = fundamental_group
        return self._fundamental_group
    

    @property
    def maximal_unipotent_monodromy_index(self):
        """returns the Calabi-Yau operator"""
        return self._fundamental_group.points.index(0)-1 # TODO : what if we want a different MUM_point ?



    @property
    def transition_matrices(self):
        if not hasattr(self, "_transition_matrices"):
            integrator = Integrator(self.fundamental_group, self.L, self.ctx.nbits)
            transition_matrices = integrator.transition_matrices
            if self.L.annihilator_of_composition(1/self.L.base_ring().gen()).leading_coefficient()(0)==0:
                transition_matrices += [prod(list(reversed(transition_matrices))).inverse()]
                self._singular_values = self.singular_values + ["infinity"]
            self._transition_matrices = transition_matrices
        return self._transition_matrices
    
    @property
    def basis_change_to_mum_point(self):
        if not hasattr(self, "_basis_change_to_mum_point"): # performance can be gained here (redundant computation with self.transition_matrices)
            path = [self.fundamental_group.vertices[i] for i in self.fundamental_group.paths[self.maximal_unipotent_monodromy_index]] + [0]
            self._basis_change_to_mum_point = self.L.numerical_transition_matrix(path, ZZ(2)**-self.ctx.nbits, assume_analytic=True)
        return self._basis_change_to_mum_point
    

    def _discover_rational_basis(self, starting_vector, Ms=None):
        if Ms == None:
            Ms = self.transition_matrices
        vs = [starting_vector]
        while len(vs)!=4:
            found = False
            for M in self.transition_matrices:
                for v in vs:
                    Pi = matrix(vs + [M*v]).transpose()
                    if any([m!=0 for m in Pi.minors(Pi.ncols())]):
                        vs += [M*v]
                        found = True
            if not found:
                self._is_semi_simple = False
                break
        if found:
            self._is_semi_simple = True
        return matrix(vs).transpose()

    def rational_monodromy_matrices(self, Mmum, Ms):
        assert Mmum in MatrixSpace(QQ,4,4), "non-integral monodromy around MUM"
        res = [Mmum]
        all_rational = True
        for M in Ms:
            try:
                newM = M.change_ring(ZZ)
                res += [newM]
            except:
                all_rational = False
                continue
        if all_rational:
            return res
        
        res = flatten([[M2.inverse()*M*M2 for M2 in Ms] for M in res] + [[M2*M*M2.inverse() for M2 in Ms] for M in res])
        res2 = []
        for M in res:
            try:
                res2 += [M.change_ring(ZZ)]
            except KeyboardInterrupt:
                raise KeyboardInterrupt
            except:
                continue
        return res2


    def saturate(self, Ms):
        if self.has_integral_monodromy:
            Pi =  Util.saturate(Ms)

        else:
            Msbig = [M.apply_map(lambda c: M.base_ring()(c).matrix()) for M in Ms]
            Msbig = [Util.flatten_matrix_of_matrices(M).change_ring(QQ) for M in Msbig]
            o = self.number_field[0].degree()
            indices_to_keep = [o*k+o-1 for k in range(4)]
            Pi =  Util.saturate(Msbig).matrix_from_rows_and_columns(indices_to_keep,indices_to_keep)
        return Pi

    @property
    def period_matrix(self):
        if not hasattr(self, "_period_matrix"):
            Mmum = self.transition_matrices[self.maximal_unipotent_monodromy_index]
            for starting_vector in ((Mmum-1)**3).columns():
                if starting_vector!=0:
                    break
            Pi = self._discover_rational_basis(starting_vector)
            
            for generator_MUM in Pi.columns():
                if (self.basis_change_to_mum_point * generator_MUM)[0] != 0:
                    break
            Pi = matrix([(Mmum-1)**k*generator_MUM for k in [0,1,3,2]]).transpose()
            Pi = Pi * self.saturate(self.monodromy_from_periods(Pi))

            self._period_matrix =  Pi 
        return self._period_matrix

    def rationalise_periods(self, periods):
        twopiI = self.ctx.CBF(ZZ(2)*pi*I)
        finalCB = (diagonal_matrix([1, twopiI**-1, twopiI**-2, twopiI**-3]) * matrix(ZZ, 4, 4, {(0,3):1, (1,2):1, (2,1):1, (3,0):1}) * diagonal_matrix([6,2,1,1])).transpose()
        period_matrix = self.basis_change_to_mum_point * periods

        
        M = (finalCB.inverse()*period_matrix).transpose()

        SF, r = self.number_field
        nu = SF.gen(0)
        R = PolynomialRing(SF, 'lambda3')
        constants = [1, self.ctx.CBF(zeta(3))/twopiI**3]
        variables = [1, R.gen(0)]

        constantsall, variablesall = [], []
        for i in range(SF.degree()):
            constantsall += [self.ctx.CBF(r)**i * v for v in constants]
            variablesall += [nu**i * v for v in variables]

        formal_matrix = M.apply_map(lambda c: Util.get_coefficient(c, constantsall, variablesall))

        return formal_matrix

    @property
    def number_field(self):
        if not hasattr(self, "_number_field"):
            for starting_vector in ((self.transition_matrices[self.maximal_unipotent_monodromy_index]-1)**3).columns():
                if starting_vector!=0:
                    break
            Pi = self._discover_rational_basis(starting_vector)
            t = self.L.base_ring().gen(0)
            coefs = flatten([(Pi.inverse() * M * Pi).coefficients() for M in self.transition_matrices])
            unknowns = [1]
            for c in coefs:
                if IntegerRelations(matrix(unknowns+[c]).transpose()).basis.nrows()==0:
                    unknowns += [c]

            self._has_integral_monodromy = len(unknowns) == 1

            if not self.has_integral_monodromy:
                P = lcm([sum([c*t**i for i, c in enumerate(Util.check_if_algebraic(u))]) for u in unknowns[1:]])
                SF = P.splitting_field("nu").optimized_representation(name="nu")[0]
                P = SF.defining_polynomial()

                r = P.roots(QQbar, multiplicities=False)[1]
                SF = NumberField(P,"nu", embedding=r)
                self._number_field = (SF, r)
            else: 
                self._number_field = (QQ, 1)
        return self._number_field
    

    @property # todo: get intersection product from top invariants and check it is correct (i.e. invariant under monodromy).
    def intersection_product(self):
        Mmum = self.transition_matrices[self.maximal_unipotent_monodromy_index]
        Pi = self.period_matrix
        Ms = [(Pi.inverse() * M.inverse() * Mmum * M * Pi).apply_map(Util.rationalize) for M in self.transition_matrices]
        return self.intersection_product_from_monodromy(Ms)

    def intersection_product_from_monodromy(self, Ms):
        Ms = self.rational_monodromy_matrices(Ms[self.maximal_unipotent_monodromy_index], Ms)
        R = PolynomialRing(QQ, self.order**2, 'a')
        IP = matrix(self.order,self.order,R.gens())
        I = R.ideal(flatten((IP+IP.transpose()).coefficients()+[(M.transpose()*IP*M-IP).coefficients() for M in Ms]))
        gens = I.groebner_basis()
        for a in R.gens():
            if a not in gens:
                break
        I2 = R.ideal(flatten([a-1] + (IP+IP.transpose()).coefficients()+[(M.transpose()*IP*M-IP).coefficients() for M in Ms]))
        IP = IP.apply_map(lambda c: I2.reduce(c)).change_ring(QQ)
        IP = IP * lcm([c.denominator() for c in IP.coefficients()])
        IP = IP.change_ring(ZZ)
        return IP

    @property
    def types(self):
        if not hasattr(self, "_types"):
            types = [self._monodromy_type(M) for M in self.transition_matrices]
            self._types = types
        return self._types
    
    @staticmethod
    def _monodromy_type(M):
        for i in range(1,12*8+1):
            for j in range(1,5):
                try:
                    if ((M**i-1)**j).change_ring(ZZ) == 0:
                        return (i,j)
                except KeyboardInterrupt:
                    raise KeyboardInterrupt
                except:
                    continue
        raise Exception("Monodromy type not identified")

    @property
    def maximal_unipotent_monodromy_fibres(self):
        if not hasattr(self, "_maximal_unipotent_monodromy_fibres"):
            self._maximal_unipotent_monodromy_fibres = [i for i, t in enumerate(self.types) if t == (1,4)]
        return self._maximal_unipotent_monodromy_fibres
    
    @property
    def conifold_fibres(self):
        if not hasattr(self, "_conifold_fibres"):
            conifold_fibres = [i for i, t in enumerate(self.types) if t == (1,2)]
            conifold_fibres.sort(key = lambda i: abs(self.ctx.CBF(self.singular_values[i]))if self.singular_values[i]!="infinity" else max([abs(self.ctx.CBF(c)) for c in self.singular_values if c!="infinity"])+1)
            self._conifold_fibres = conifold_fibres
        return self._conifold_fibres

    @property
    def laddered_basis(self):
        if not hasattr(self, "_laddered_basis"):
            monodromy_matrices = self.monodromy_from_periods(self.period_matrix)
            Mmum = monodromy_matrices[self.maximal_unipotent_monodromy_index]
            holo = ((Mmum-1)).right_kernel().gen(0)
            
            found = False
            for i in self.conifold_fibres:
                M = monodromy_matrices[i]
                if M*holo not in ((Mmum-1)**3).right_kernel():
                    log4 = M*holo
                    found = True
                    break
            
            if not found:
                for M in monodromy_matrices:
                    if M*holo not in ((Mmum-1)**3).right_kernel():
                        log4 = M*holo
                        found = True
                        break
            if found:
                holo, log2, log3 = (Mmum-1)**3*log4, (Mmum-1)**2*log4, (Mmum-1)*log4
            
            if not found:
                vs = [holo]
                log2ker =((Mmum-1)**2).right_kernel_matrix()
                log2 = vector(Util.find_complement(log2ker.solve_left(matrix(vs)), primitive=False) * log2ker)
                vs += [log2]
                
                log3ker =((Mmum-1)**3).right_kernel_matrix()
                log3 = vector(Util.find_complement(log3ker.solve_left(matrix(vs)), primitive=False) * log3ker)
                vs += [log3]
                
                log4 = vector(Util.find_complement(matrix(vs), primitive=False))
                vs += [log4]
            
            vs = [log4, log3, log2, holo]
            vs = matrix(vs).transpose()
            
            CB = self.saturate([vs.inverse() * M * vs for M in monodromy_matrices])
            perm = matrix(ZZ, 4, 4, {(0,0):1, (1,1):1, (2,3):1, (3,2):1})
            self._laddered_basis = (vs * CB * perm).change_ring(QQ)
        return self._laddered_basis

    ### gamma class ###
    
    def monodromy_from_periods(self, periods):
        return [(periods.inverse() * M * periods).apply_map(self.formalise) for M in self.transition_matrices]
    
    def periods_from_gamma_class(self, gamma_class):
        twopiI = self.ctx.CBF(ZZ(2)*pi*I)
        lambda3 = self.ctx.CBF(zeta(3))/twopiI**3
        finalCB = (diagonal_matrix([1, twopiI**-1, twopiI**-2, twopiI**-3]) * matrix(ZZ, 4, 4, {(0,3):1, (1,2):1, (2,1):1, (3,0):1}) * diagonal_matrix([6,2,1,1])).transpose()

        return self.basis_change_to_mum_point.inverse() * finalCB * gamma_class.transpose()(lambda3)

    def gamma_class_from_periods(self, periods):
        twopiI = self.ctx.CBF(ZZ(2)*pi*I)
        finalCB = (diagonal_matrix([1, twopiI**-1, twopiI**-2, twopiI**-3]) * matrix(ZZ, 4, 4, {(0,3):1, (1,2):1, (2,1):1, (3,0):1}) * diagonal_matrix([6,2,1,1])).transpose()
        period_matrix = self.basis_change_to_mum_point * periods

        Mmum = (self.monodromy_from_periods(periods)[self.maximal_unipotent_monodromy_index]-1)
        if self.has_integral_monodromy:
            Mmum = Mmum.change_ring(ZZ)
        c = period_matrix * Mmum.right_kernel().gen(0)
        period_matrix = period_matrix / c[-1]
        M = (finalCB.inverse()*period_matrix).transpose()

        formal_matrix = M.apply_map(lambda c: self.formalise(c, [self.ctx.CBF(zeta(3))/twopiI**3], expect_rational=True))
        return formal_matrix
    
    def gamma_class_from_topological_invariants(self, N, M, chi, c2H, H3, alpha, delta, sigma):
        R = PolynomialRing(QQ, 'lambda3')
        rhoconj = matrix([
            [chi*R.gen() - alpha/2*c2H/24-delta/2, M*c2H/24,  alpha/2*H3/2, M*H3/6],
            [c2H/24, sigma*N/2, -H3/2, 0],
            [1, 0, 0, 0],
            [alpha/2*N/M, N, 0, 0],
        ])
        return rhoconj




    def formalise(self, c, constants=[], expect_rational=False):
        if constants!=[]:
            R = PolynomialRing(QQ, 'c', len(constants))
            constants = [1] + constants
            variables = [1] + list(R.gens())
        else:
            constants = [1]
            variables = [1]
        
        if expect_rational:
            return Util.get_coefficient(c, constants, variables)

        SF, r = self.number_field
        nu = SF.gen(0)
        if constants!=[1]:
            R = PolynomialRing(SF, 'c', len(constants)-1)
            variables = [1] + list(R.gens())

        constantsall, variablesall = [], []
        for i in range(SF.degree()):
            constantsall += [self.ctx.CBF(r)**i * v for v in constants]
            variablesall += [nu**i * v for v in variables]

        return  Util.get_coefficient(c, constantsall, variablesall)



    ### misc ###

    @property
    def monodromy_in_scaled_frobenius_basis(self):
        twopiI = self.ctx.CBF(ZZ(2)*pi*I)
        scaled_frobenius_basis = (diagonal_matrix([1, twopiI**-1, twopiI**-2, twopiI**-3]) * matrix(ZZ, 4, 4, {(0,3):1, (1,2):1, (2,1):1, (3,0):1}) * diagonal_matrix([6,2,1,1])).transpose()
        period_matrix = self.basis_change_to_mum_point.inverse() * scaled_frobenius_basis

        monodromy_matrices = [period_matrix.inverse() * M * period_matrix for M in self.transition_matrices]
        
        SF, r = self.number_field
        nu = SF.gen(0)
        R = PolynomialRing(SF, 'lambda3')
        l = R.gen(0)
        variables = [1, l, l**2]
        hom = R.hom([self.ctx.CBF(zeta(3))/twopiI**3])
        constants = [hom(v) for v in variables]

        constantsall, variablesall = [], []
        for i in range(SF.degree()):
            constantsall += [self.ctx.CBF(r)**i * v for v in constants]
            variablesall += [nu**i * v for v in variables]

        monodromy_matrices = [M.apply_map(lambda c: Util.get_coefficient(c, constantsall, variablesall)) for M in monodromy_matrices]

        return monodromy_matrices
    
    @property
    def is_semi_simple(self):
        """returns whether the monodromy group is semi-simple"""
        if not hasattr(self, "_is_semi_simple"):
            for starting_vector in ((self.transition_matrices[self.maximal_unipotent_monodromy_index]-1)**3).columns():
                if starting_vector!=0:
                    break
            self._discover_rational_basis(starting_vector)
        return self._is_semi_simple
    
    @property
    def has_conifold(self):
        if not hasattr(self, "_has_conifold"):
            self._has_conifold = len(self.conifold_fibres)>0
        return self._has_conifold
    
    @property
    def is_symplectic(self):
        if not hasattr(self, "_is_symplectic"):
            self._is_symplectic = self.intersection_product == matrix(ZZ, 4, 4, {(0,2):1, (1,3):1, (2,0):-1, (3,1):-1})
        return self._is_symplectic
    
    @property
    def has_two_maximal_unipotent_monodromy_points(self):
        if not hasattr(self, "_has_two_maximal_unipotent_monodromy_points"):
            self._has_two_maximal_unipotent_monodromy_points = len(self.maximal_unipotent_monodromy_fibres)>1
        return self._has_two_maximal_unipotent_monodromy_points
    
    @property
    def has_integral_monodromy(self):
        if not hasattr(self, "_has_integral_monodromy"):
            self.number_field
        return self._has_integral_monodromy

    @property
    def canonical_topological_invariants(self):
        """ returns (H3, c2H, chi, p) where H3 is the triple intersection number, c2H is the second Chern class, chi is the top Chern class (the Euler characteristic), """
        raise NotImplemented


    @property
    def paths(self):
        if not hasattr(self, "_paths"):
            paths = self.fundamental_group.pointed_loops_vertices
            self.transition_matrices
            if "infinity" in self.singular_values:
                paths += [-sum(paths)]
            self._paths = paths
        return self._paths
    
    ### Monodromy index investigations ###

    def monodromy_index_mod_n(self, n):
        if not hasattr(self, "_reduction_indices"):
            self._reduction_indices = {}
        res = 1
        for p, power in factor(n):
            q = p**power
            if q not in self._reduction_indices.keys():
                self._reduction_indices[q] = self._monodromy_index_mod_q(q)
            res *= self._reduction_indices[q]
        return res

    def _monodromy_index_mod_q(self, q):
        R = IntegerModRing(q)
        monodromy_matrices_mod_q = [M.change_ring(R) for M in self.monodromy_matrices]
        Sp4 = Sp(4, R)
        if Sp4.invariant_form() == matrix(R, 4, 4, {(0,3):1, (1,2):1, (2,1):-1, (3,0):-1}):
            CB = matrix(R, 4, 4, {(0,0):1, (1,1):1, (2,3):1, (3,2):1})
            monodromy_matrices_mod_q = [CB.inverse()*M*CB for M in monodromy_matrices_mod_q]
        monodromy_group = Sp4.subgroup(monodromy_matrices_mod_q)
        return Sp4.cardinality()/monodromy_group.cardinality()
    

    def cleanup(self, gamma_class):
        IP = self.intersection_product_from_monodromy(self.monodromy_from_periods(self.periods_from_gamma_class(gamma_class)))
        M = (gamma_class).submatrix(0,3)
        vanishing = matrix([Util.xgcd_list(list((M.column(0)*lcm([c.denominator() for c in M.column(0)])).change_ring(ZZ)))[1]])
        ker = M.change_ring(QQ).left_kernel_matrix()
        d = lcm([c.denominator() for c in ker.coefficients()])
        others = (ker*d).change_ring(ZZ).image().saturation().basis_matrix()
        basis = vanishing.stack(others)

        M = (basis * gamma_class).submatrix(1,2)
        vanishing2 = matrix([[0]+Util.xgcd_list(list((M.column(0)*lcm([c.denominator() for c in M.column(0)])).change_ring(ZZ)))[1]]) * basis
        ker = M.change_ring(QQ).left_kernel_matrix()
        d = lcm([c.denominator() for c in ker.coefficients()])
        others = zero_matrix(2,1).augment(ker*d).change_ring(ZZ).image().saturation().basis_matrix()
        basis = vanishing.stack(vanishing2).stack(others*basis)
        
        M = (basis * gamma_class).submatrix(2,1)
        vanishing3 = matrix([[0,0]+Util.xgcd_list(list((M.column(0)*lcm([c.denominator() for c in M.column(0)])).change_ring(ZZ)))[1]])* basis
        ker = M.change_ring(QQ).left_kernel_matrix()
        d = lcm([c.denominator() for c in ker.coefficients()])
        others = zero_matrix(1,2).augment(ker * d).change_ring(ZZ).image().saturation().basis_matrix()
        basis = vanishing.stack(vanishing2).stack(vanishing3).stack(others*basis)

        basis = basis.matrix_from_rows([0,1,3,2])

        basis = basis.rows()
        a = QQ((basis[0]*gamma_class)[0].monomial_coefficient(gamma_class.base_ring()(1)))
        b = QQ((basis[2]*gamma_class)[0])
        d = lcm([a.denominator(), b.denominator()])
        a,b= ZZ(a*d), ZZ(b*d)
        basis[0] += -basis[2] * (a//b)
        
        a  = QQ((basis[1]*gamma_class)[0])
        a2 = QQ((basis[3]*gamma_class)[0])
        b  = QQ((basis[2]*gamma_class)[0])
        d = lcm([a.denominator(), a2.denominator(), b.denominator()])
        a,a2, b= ZZ(a*d), ZZ(a2*d), ZZ(b*d)
        basis[1] += -basis[2] * (a//b)
        basis[3] += -basis[2] * (a2//b)
        
        a = QQ((basis[1]*gamma_class)[1])
        b = QQ((basis[3]*gamma_class)[1])
        d = lcm([a.denominator(), b.denominator()])
        a,b= ZZ(a*d), ZZ(b*d)
        basis[1] += -basis[3] * (a//b)
        
        a = QQ((basis[0]*gamma_class)[2])
        b = QQ((basis[1]*gamma_class)[2])
        d = lcm([a.denominator(), b.denominator()])
        a,b= ZZ(a*d), ZZ(b*d)
        basis[0] += -basis[1] * (a//b)
        
        basis[3] += -basis[2] * ((basis[0] * IP * basis[3]) // (basis[0] * IP * basis[2]))
        basis[1] += -basis[2] * ((basis[0] * IP * basis[1]) // (basis[0] * IP * basis[2]))

        basis[1] = -basis[1]

        return matrix(basis)