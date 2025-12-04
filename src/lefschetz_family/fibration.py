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
from ore_algebra import *

from sage.modules.free_module_element import vector
from sage.rings.qqbar import QQbar
from sage.functions.other import factorial
from sage.matrix.constructor import matrix
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.matrix.special import identity_matrix
from sage.matrix.special import diagonal_matrix
from sage.matrix.special import block_diagonal_matrix
from sage.matrix.special import block_matrix

from sage.misc.misc_c import prod
from sage.matrix.special import zero_matrix

from .voronoi import FundamentalGroupVoronoi
from .integrator import Integrator
from .util import Util
from .context import Context
from .hypersurface import Hypersurface
from .monodromyRepresentation import MonodromyRepresentation

import logging
import time

logger = logging.getLogger(__name__)


class Fibration(object):
    def __init__(self, P, basepoint=None, fibration=None, fibre=None, cyclic_forms=None, single_integration=True, family=None, **kwds):
        """P, a homogeneous polynomial defining a family of hypersurfaces.
        """
        
        self.ctx = Context(**kwds)

        self._P = P
        self._fibration = fibration
        
        if family!=None:
            assert family.pol == self.P, "family is not for correct polynomial"
            # if basepoint!=None:
            #     assert family.basepoint == basepoint, "family is not centered at basepoint"
            self._family = family
        else:
            self._family = Family(self.P, basepoint=basepoint)

        _, denom = self._family.gaussmanin()
        self._critical_values = denom.roots(QQbar, multiplicities=False)

        if cyclic_forms!= None: 
            # L = self.family.picard_fuchs_equation(cyclic_forms)
            # assert L.order() == len(self.fibre.cohomology_internal), "cyclic_form is not cyclic"
            if type(cyclic_forms) != list:
                cyclic_forms = [cyclic_forms]
            self._cyclic_forms = cyclic_forms
            # self._cyclic_picard_fuchs_equations = L
        
        

        if fibre!=None:
            assert basepoint!=None, "Cannot specify fibre without specifying basepoint"
            assert P(basepoint) == fibre.P, "Fibre and P(basepoint) do not match"
            self._fibre = fibre

        if basepoint != None: # it is useful to be able to specify the basepoint to avoid being stuck in arithmetic computations if critical values have very large modulus
            assert basepoint not in self.critical_values, "basepoint is not regular"
            self._basepoint = basepoint
        
        if not self.ctx.debug:
            fg = self.fundamental_group # this allows reordering the critical points straight away and prevents shenanigans. There should be a better way to do this
        
    
    @property
    def monodromy_representation(self):
        if not hasattr(self,'_monodromy_representation'):
            self._monodromy_representation = MonodromyRepresentation(self.monodromy_matrices, self.fibre.intersection_product)
        return self._monodromy_representation
    
    @property
    def intersection_product(self):
        return self.monodromy_representation.intersection_product

    @property
    def P(self):
        return self._P

    @property
    def family(self):
        return self._family
    
    @property
    def critical_values(self):
        if not hasattr(self,'_critical_values'):
            _, denom = self.family.gaussmanin
            self._critical_values = denom.roots(QQbar, multiplicities=False)
        return self._critical_values

    def vector_to_form(self, v):
        dmax = max([w.degree() for w in self.fibre.cohomology_internal])
        dim = self.fibre.dim
        deg = self.fibre.degree
        res = 0
        smax = (dmax + dim + 1) // deg
        for c, w in zip(v, self.fibre.cohomology_internal):
            s = (w.degree() + dim + 1) // deg
            res += self.P.parent()(factorial(s) * self.P**(smax-s) * w) * self.P.parent(c)
        return res


    @property
    def monodromy_matrices(self):
        if not hasattr(self, '_monodromy_matrices'):
            r = len(self.fibre.cohomology_internal) 

            initial_conditions_all = []
            for w, L in zip(self.cyclic_forms, self.cyclic_picard_fuchs_equations):
                integration_correction = diagonal_matrix([1]+[1/ZZ(factorial(k)) for k in range(L.order())])
                derivatives_at_basepoint = self.derivatives_values_at_basepoint(w, L.order())
                cohomology_fibre_to_family = self.family._coordinates([self.family.pol.parent()(w) for w in self.fibre.cohomology_internal], self.basepoint)

                initial_conditions = integration_correction * derivatives_at_basepoint * cohomology_fibre_to_family.inverse()
                initial_conditions = initial_conditions.submatrix(1,0)
                initial_conditions_all += [initial_conditions]

            CB = block_matrix([[v.transpose() for v in initial_conditions_all]]).transpose()
            assert CB.rank() == len(self.fibre.cohomology_internal), "cyclic forms do not generate full cohomology"
            if self.fibre.dim%2 == 0:
                CB = block_diagonal_matrix([CB, identity_matrix(1)])
            CBi = (CB.transpose() * CB).inverse() * CB.transpose() 



            cohomology_monodromies = [block_diagonal_matrix([Ms[i] for Ms in self.cyclic_transition_matrices]) for i in range(len(self.cyclic_transition_matrices[0]))]
            if self.fibre.dim%2 == 0:
                cohomology_monodromies = [block_diagonal_matrix([M, identity_matrix(1)]) for M in cohomology_monodromies]
            cohomology_monodromies = [CBi * M * CB for M in cohomology_monodromies]

            Ms = [(self.fibre.period_matrix.inverse() * M * self.fibre.period_matrix) for M in cohomology_monodromies]

            try:
                Ms = [M.change_ring(ZZ) for M in Ms]
            except Exception as e:
                if not self.ctx.debug:
                    raise e
            
            Mtot = prod(list(reversed(Ms)))
            if Mtot != 1:
                self._critical_values = self.critical_values + ["infinity"]
                transition_matrix_infinity = [prod([M.inverse() for M in Ms]) for Ms in self.cyclic_transition_matrices]
                self._cyclic_transition_matrices += [transition_matrix_infinity]
                Ms += [(Mtot.inverse()).change_ring(ZZ)]
                
                pathinfinity = -sum(self.paths)
                self._paths += [pathinfinity]
            
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

    @property
    def fibre(self):
        if not hasattr(self,'_fibre'):
            self._fibre = Hypersurface(self.P(self.basepoint), nbits=self.ctx.nbits, fibration=self._fibration)
        return self._fibre
    
    @property
    def cyclic_forms(self):
        if not hasattr(self, '_cyclic_forms'):
            r = len(self.fibre.cohomology_internal)
            t = self.family.upolring.gen(0)
            for v in identity_matrix(r).rows()+[vector([t**i for i in range(r)])]:
                L = self.family.picard_fuchs_equation(v)
                if L.order() == r:
                    break
            assert L.order() == r, "could not find cyclic form"
            self._cyclic_forms = [v]
            self._cyclic_picard_fuchs_equations = [L]
        return self._cyclic_forms
    
    @property
    def cyclic_picard_fuchs_equations(self):
        if not hasattr(self, '_cyclic_picard_fuchs_equations'):
            self._cyclic_picard_fuchs_equations = [self.family.picard_fuchs_equation(v) for v in self.cyclic_forms]
        return self._cyclic_picard_fuchs_equations
    
    @property
    def cyclic_transition_matrices(self):
        if not hasattr(self, '_cyclic_transition_matrices'):
            self._cyclic_transition_matrices = [self.integrate(L) for L in self.cyclic_picard_fuchs_equations]
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


    def derivatives_values_at_basepoint(self, w, s):
        # s=len(self.fibre.cohomology_internal)
        w = w.change_ring(self.family.upolring)
        GM, denom = self.family.gaussmanin()
        Dt = self.family.dopring.gen(0)
        t = self.family.upolring.gen(0)

        derivatives = [w]
        for _ in range(s-1):
            derivatives += [denom*derivatives[-1].derivative(t) +  derivatives[-1]*GM]
        derivatives_at_basepoint2 = [w(self.basepoint) for w in derivatives]        
        matders = []
        for i in range(s):
            matders += [[c(self.basepoint) for c in ((denom * Dt)**i).coefficients(sparse=False)]+[0]*(s-1-i)]
        matders = matrix(matders)

        derivatives_at_basepoint = matders.inverse() * matrix(derivatives_at_basepoint2).change_ring(QQ)
        return zero_matrix(1,derivatives_at_basepoint.ncols()).stack(derivatives_at_basepoint, subdivide=False)    

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
        if not hasattr(self,'_paths'):
            self._paths= self.fundamental_group.pointed_loops_vertices
        return self._paths

    @property
    def basepoint(self):
        if  not hasattr(self, '_basepoint'):
            shift = 1
            reals = [self.ctx.CF(c).real() for c in self.critical_values]
            xmin, xmax = min(reals), max(reals)
            self._basepoint = Util.simple_rational(xmin - (xmax-xmin)*shift, (xmax-xmin)/10)
        return self._basepoint
