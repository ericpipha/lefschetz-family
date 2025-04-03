# -*- coding: utf-8 -*-

import sage.all

from .numperiods.family import Family
from ore_algebra import *

from sage.modules.free_module_element import vector
from sage.rings.qqbar import QQbar
from sage.functions.other import factorial
from sage.matrix.constructor import matrix
from sage.rings.integer_ring import ZZ
from sage.matrix.special import identity_matrix
from sage.matrix.special import diagonal_matrix
from sage.matrix.special import block_diagonal_matrix
from sage.misc.misc_c import prod

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
    def __init__(self, P, basepoint=None, fibration=None, cyclic_form = None, **kwds):
        """P, a homogeneous polynomial defining a family of hypersurfaces.
        """
        
        self.ctx = Context(**kwds)

        self._P = P
        self._fibration = fibration
        
        _, denom = Family(self.P, path=[-1, 0]).gaussmanin()
        self._critical_values = denom.roots(QQbar, multiplicities=False)

        if cyclic_form!= None: 
            L = self.family.picard_fuchs_equation(cyclic_form)
            assert L.order() == len(self.fibre.cohomology), "cyclic_form is not cyclic"
            self._cyclic_form = cyclic_form
            self._cyclic_picard_fuchs_equation = L
        
        self._family = Family(self.P, basepoint=basepoint)

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
    def picard_fuchs_equations(self):
        if not hasattr(self,'_picard_fuchs_equations'):
            self._picard_fuchs_equations = [self.family.picard_fuchs_equation(vector([w,0])) for w in self.holomorphic_forms]
        return self._picard_fuchs_equations
    
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
        dmax = max([w.degree() for w in self.fibre.cohomology])
        dim = self.fibre.dim
        deg = self.fibre.degree
        res = 0
        smax = (dmax + dim + 1) // deg
        for c, w in zip(v, self.fibre.cohomology):
            s = (w.degree() + dim + 1) // deg
            res += self.P.parent()(factorial(s) * self.P**(smax-s) * w) * self.P.parent(c)
        return res


    @property
    def monodromy_matrices(self):
        if not hasattr(self, '_monodromy_matrices'):
            r = len(self.fibre.cohomology) 
            
            cyclic_form = self.cyclic_form
            w = self.vector_to_form(cyclic_form)

            integration_correction = diagonal_matrix([1]+[1/ZZ(factorial(k)) for k in range(r)])
            derivatives_at_basepoint = self.derivatives_values_at_basepoint(w)
            cohomology_fibre_to_family = self.family._coordinates([self.family.pol.parent()(w) for w in self.fibre.cohomology], self.basepoint)

            initial_conditions = integration_correction * derivatives_at_basepoint * cohomology_fibre_to_family.inverse()
            initial_conditions = initial_conditions.submatrix(1,0)

            cohomology_monodromies = [initial_conditions.inverse() * M * initial_conditions for M in self.cyclic_transition_matrices]
            if self.fibre.dim%2 == 0:
                cohomology_monodromies = [block_diagonal_matrix([M, identity_matrix(1)]) for M in cohomology_monodromies]

            Ms = [(self.fibre.period_matrix.inverse() * M * self.fibre.period_matrix) for M in cohomology_monodromies]

            try:
                Ms = [M.change_ring(ZZ) for M in Ms]
            except Exception as e:
                if not self.ctx.debug:
                    raise e
            
            Mtot = prod(list(reversed(Ms)))
            if Mtot != 1:
                self._critical_values = self.critical_values + ["infinity"]
                transition_matrix_infinity = prod(list(reversed(self.cyclic_transition_matrices))).inverse()
                self._cyclic_transition_matrices += [transition_matrix_infinity]
                Ms += [(Mtot.inverse()).change_ring(ZZ)]
                pathtot = []
                for path in self.paths:
                    pathtot = pathtot+path
                self._paths += [list(reversed(Util.simplify_path(pathtot)))]
            
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
    def cyclic_form(self):
        if not hasattr(self, '_cyclic_form'):
            r = len(self.fibre.cohomology)
            t = self.family.upolring.gen(0)
            for v in identity_matrix(r).rows()+[vector([t**i for i in range(r)])]:
                L = self.family.picard_fuchs_equation(v)
                if L.order() == r:
                    break
            assert L.order() == r, "could not find cyclic form"
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
            self._cyclic_transition_matrices = self.integrate(L)
        return self._cyclic_transition_matrices
    
    def integrate(self, L):
        logger.info("Computing numerical transition matrices of operator of order %d and degree %d (%d edges total)."% (L.order(), L.degree(), len(self.fundamental_group.edges)))
        begin = time.time()

        integrator = Integrator(self.fundamental_group, L, self.ctx.nbits)
        transition_matrices = integrator.transition_matrices
        
        end = time.time()
        duration_str = time.strftime("%H:%M:%S",time.gmtime(end-begin))
        logger.info("Integration finished -- total time: %s."% (duration_str))

        return transition_matrices


    def derivatives_values_at_basepoint(self, w):
        s = len(self.fibre.cohomology)
        derivatives = [self.P.parent()(0), w]
        for k in range(s-1):
            derivatives += [self._derivative(derivatives[-1], self.P)] 
        return self.family._coordinates(derivatives, self.basepoint)

    @classmethod
    def _derivative(self, A, P): 
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
            logger.info("Fundamental group computed in %s."% (duration_str))

            self._critical_values = fundamental_group.points[1:]
            self._fundamental_group = fundamental_group
        return self._fundamental_group

    @property
    def paths(self):
        if not hasattr(self,'_paths'):
            paths = []
            for path in self.fundamental_group.pointed_loops:
                paths += [[self.fundamental_group.vertices[v] for v in path]]
            self._paths= paths
        return self._paths

    @property
    def basepoint(self):
        if  not hasattr(self, '_basepoint'):
            shift = 1
            reals = [self.ctx.CF(c).real() for c in self.critical_values]
            xmin, xmax = min(reals), max(reals)
            self._basepoint = Util.simple_rational(xmin - (xmax-xmin)*shift, (xmax-xmin)/10)
        return self._basepoint
