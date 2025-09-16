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

from sage.modules.free_module_element import vector
from sage.matrix.constructor import matrix
from sage.rings.integer_ring import ZZ
from sage.matrix.special import identity_matrix
from sage.matrix.special import block_diagonal_matrix
from sage.matrix.special import zero_matrix
from sage.misc.misc_c import prod
from sage.misc.flatten import flatten


from .util import Util

import logging
import time

logger = logging.getLogger(__name__)


class MonodromyRepresentation(object):
    def __init__(self, monodromy_matrices, intersection_product):
        """`monodromy_matrices` is a list of matrices defining a monodromy representation
        """
        
        assert prod(list(reversed(monodromy_matrices)))==1, "monodromy representation is badly defined"
        self._monodromy_matrices = monodromy_matrices
        self._fibre_intersection_product = intersection_product
        self._dim = monodromy_matrices[0].nrows()
    
    
    @property
    def monodromy_matrices(self):
        return self._monodromy_matrices

    @property
    def fibre_intersection_product(self):
        return self._fibre_intersection_product
    
    @property
    def dim(self):
        return self._dim
    
    @property
    def homology(self): 
        if not hasattr(self, '_homology'):
            self._homology = identity_matrix(len(self.extensions_desingularisation) + self.add).rows()
        return self._homology

    def lift(self, v): 
        """Given a combination of thimbles of desingularisation, gives the corresponding homology class"""
        infinity_loops = matrix(self.infinity_loops).image().basis()
        infinity_loops = [self.desingularise(v) for v in infinity_loops]
        v = matrix(self.extensions_desingularisation + infinity_loops).solve_left(v)
        return vector(list(v)[:-len(infinity_loops)] + [0 for i in range(self.add)])

    @property
    def intersection_product(self):
        if not hasattr(self,'_intersection_product'):
            self._intersection_product = self._compute_intersection_product()
        return self._intersection_product
    
    @property
    def intersection_product_extensions(self):
        if not hasattr(self,'_intersection_product_extensions'):
            self._intersection_product_extensions = self._compute_intersection_product_extensions()
        return self._intersection_product_extensions

    @property
    def thimbles(self):
        if not hasattr(self,'_thimbles'):
            self._thimbles=[]
            for i, pcs in enumerate(self.permuting_cycles):
                for pc in pcs:
                    self._thimbles+=[(pc, i)]
        return self._thimbles
    
    @property
    def permuting_cycles(self):
        if not hasattr(self, '_permuting_cycles'):
            permuting_cycles = [[] for i in range(len(self.monodromy_matrices))]
            for i in range(len(self.monodromy_matrices)):
                M = self.monodromy_matrices[i]
                D, U, V = (M-1).smith_form()
                for j in range(self.dim):
                    if D[j,j]!=0:
                        permuting_cycles[i] += [ V * vector([1 if k==j else 0 for k in range(self.dim)]) ]
                permuting_cycles[i] = matrix(permuting_cycles[i]).image().gens()
            self._permuting_cycles = permuting_cycles
        return self._permuting_cycles

    @property
    def infinity_loops(self):
        """The linear combinations of thimbles that correspond to extensions along the (trivial) loop around infinity."""
        if not hasattr(self, '_infinity_loops'):
            infinity_cycles = []
            for i in range(self.dim):
                v = vector([1 if k==i else 0 for k in range(self.dim)])
                coefs = []
                for j in range(len(self.monodromy_matrices)):
                    M = self.monodromy_matrices[j]
                    if len(self.permuting_cycles[j])==0:
                        continue
                    coefs += list(matrix([ (M-1) * t for t in self.permuting_cycles[j]]).solve_left( (M-1) * v ))
                    v = self.monodromy_matrices[j]*v
                infinity_cycles+=[vector(coefs)]
            self._infinity_loops = matrix(infinity_cycles).change_ring(ZZ).rows()
        return self._infinity_loops
    
    @property
    def kernel_boundary(self):
        if not hasattr(self, '_kernel_boundary'):
            delta = matrix(self.vanishing_cycles).change_ring(ZZ)
            self._kernel_boundary = delta.kernel()
        return self._kernel_boundary
    

    @property
    def extensions(self):
        """Representants of the extensions of the elliptic surface."""
        if not hasattr(self, '_extensions'):
            delta = matrix(self.borders_of_thimbles).change_ring(ZZ)
            kerdelta = delta.kernel().matrix()
            D, U, V = kerdelta.smith_form()
            infinity_loops = matrix(self.infinity_loops).image().saturation().basis() # taking saturation here. This should in principle not be necessary
            B = D.solve_left(matrix(infinity_loops) * V).change_ring(ZZ)*U
            quotient_basis = Util.find_complement(B)
            if quotient_basis.nrows()==0:
                self._extensions = kerdelta.submatrix(0,0,0).rows()
            else:
                self._extensions = (quotient_basis*kerdelta).rows()
        return self._extensions
    
    @property
    def extensions_desingularisation(self):
        """Representant of the extensions of the desingularisation of the elliptic surface. 
        Along with the fibre and section, this constitutes a basis for the second homology group of the surface. 
        The singular fibre components are identified at the end of the list."""
        if not hasattr(self, '_extensions_desingularisation'):
            infinity_loops = matrix(self.infinity_loops).image().basis()
            infinity_loops = [self.desingularise(v) for v in infinity_loops]
            delta = matrix(flatten(self.vanishing_cycles_desingularisation)).change_ring(ZZ)
            kerdelta = delta.kernel().matrix()
            D, U, V = kerdelta.smith_form()
            B = D.solve_left(matrix(infinity_loops) * V).change_ring(ZZ)*U
            quotient_basis = Util.find_complement(B)
            if quotient_basis.nrows()==0:
                self._extensions_desingularisation = kerdelta.submatrix(0,0,0).change_ring(ZZ).rows()
            else:
                self._extensions_desingularisation = (quotient_basis*kerdelta).change_ring(ZZ).rows()
        return self._extensions_desingularisation


    def _compute_intersection_product_extensions(self):
        r=len(self.thimbles)
        extensions = matrix(self.extensions)
        inter_prod_thimbles = matrix([[self._compute_intersection_product_thimbles_extensions(i,j) for j in range(r)] for i in range(r)])
        intersection_11 = (extensions * inter_prod_thimbles * extensions.transpose()).change_ring(ZZ)
        return intersection_11

    def _compute_intersection_product_thimbles_extensions(self, i, j):
        vi, loopi = self.thimbles[i]
        vj, loopj = self.thimbles[j]

        Mi = self.monodromy_matrices[loopi]
        Mj = self.monodromy_matrices[loopj]

        di, dj = (Mi-1)*vi, (Mj-1)*vj

        res = di * self.fibre_intersection_product * dj
        resid = -vi * self.fibre_intersection_product * dj

        if loopi == loopj:
            return resid
        if loopi < loopj:
            return res
        else:
            return 0


    def _compute_intersection_product(self):
        r=len(flatten(self.vanishing_cycles_desingularisation))
        extensions = matrix(self.extensions_desingularisation)
        inter_prod_thimbles = matrix([[self._compute_intersection_product_thimbles(i,j) for j in range(r)] for i in range(r)])
        intersection_11 = (-1 if self.add==2 else 1) * (extensions * inter_prod_thimbles * extensions.transpose()).change_ring(ZZ)
        if self.add==2:
            intersection_02 = zero_matrix(2,2)
            intersection_02[0,1], intersection_02[1,0] = 1,1
            intersection_02[1,1] = self.self_intersection_section
            return block_diagonal_matrix(intersection_11, intersection_02)
        return intersection_11
        
    def _compute_intersection_product_thimbles(self,i,j):
        vi = self.permuting_cycles_desingularisation[i]
        Mi = flatten(self.monodromy_matrices_desingularisation)[i]
        vj = self.permuting_cycles_desingularisation[j]
        Mj = flatten(self.monodromy_matrices_desingularisation)[j]
        di, dj = (Mi-1) * vi, (Mj-1) * vj
        res = di*self.fibre_intersection_product*dj
        resid = -vi*self.fibre_intersection_product*di

        if i==j:
            return resid
        if i<j:
            return res
        else:
            return 0

    
    @property
    def primary_lattice(self):
        if not hasattr(self, '_primary_lattice'):
            extensions = [self.lift(self.desingularise(v)) for v in self.extensions]
            components_of_singular_fibres = [self.lift(v) for v in flatten(self.components_of_singular_fibres, max_level=2)]
            primary_lattice = extensions + components_of_singular_fibres
            if self.add==2:
                primary_lattice += [self.fibre_class, self.section]
            self._primary_lattice = matrix(primary_lattice).transpose()
        return self._primary_lattice

    def desingularise(self, v):
        """Given an extension of the surface, yields its description as an extension of the desingularisation."""
        return v * self.thimbles_confluence
    
    @property
    def permuting_cycles_desingularisation(self):
        if not hasattr(self, '_permuting_cycles_desingularisation'):
            monodromy_matrices = flatten(self.monodromy_matrices_desingularisation)
            vanishing = flatten(self.vanishing_cycles_desingularisation)
            _permuting_cycles_desingularisation = []
            for i in range(len(monodromy_matrices)):
                M = monodromy_matrices[i]
                D, U, V = (M-1).smith_form()
                p = V.column(0)
                if (M-1) * p != vanishing[i]:
                    p = -p
                assert (M-1) * p == vanishing[i]
                _permuting_cycles_desingularisation += [ p ]
            self._permuting_cycles_desingularisation = _permuting_cycles_desingularisation
        return self._permuting_cycles_desingularisation

    def lift(self, v):
            """Given a combination of thimbles of desingularisation, gives the corresponding homology class"""
            infinity_loops = matrix(self.infinity_loops).image().basis()
            infinity_loops = [self.desingularise(v) for v in infinity_loops]
            v = matrix(self.extensions_desingularisation + infinity_loops).solve_left(v)
            add = [0,0] if self.add==2 else []
            return vector(list(v)[:-len(infinity_loops)] + add)

    @property
    def thimbles_confluence(self):
        if not hasattr(self, '_thimbles_confluence'):
            blocks =[]
            for i, pcs in enumerate(self.permuting_cycles):
                decompositions = []
                for p in pcs:
                    decomposition = []
                    for M, v in zip(self.monodromy_matrices_desingularisation[i], self.vanishing_cycles_desingularisation[i]):
                        decomposition += [(M-1) * p / v]
                        p = M * p
                    decompositions+=[decomposition]
                blocks+= [matrix(decompositions)]
            self._thimbles_confluence = block_diagonal_matrix(blocks).change_ring(ZZ)
        return self._thimbles_confluence

    @property
    def vanishing_cycles_desingularisation(self):
        if not hasattr(self, '_vanishing_cycles_desingularisation'):
            self._vanishing_cycles_desingularisation = [[(M-1).transpose().image().gens()[0] for M in Ms] for Ms in self.monodromy_matrices_desingularisation]
        return self._vanishing_cycles_desingularisation
    
    @property
    def borders_of_thimbles(self):
        if not hasattr(self, '_borders_of_thimbles'):
            self._borders_of_thimbles = []
            for ps, M in zip(self.permuting_cycles, self.monodromy_matrices):
                self._borders_of_thimbles += [ (M-1) * p for p in ps]
        return self._borders_of_thimbles

    @property
    def components_of_singular_fibres(self):
        if not hasattr(self, '_components_of_singular_fibres'):
            ranktot = 0
            rankmax = sum([len(Ms) for Ms in self.monodromy_matrices_desingularisation])
            sing_comps = []
            for M in self.vanishing_cycles_desingularisation:
                M = matrix(M)
                rank = M.dimensions()[0]
                sing_comps += [[vector([0]*ranktot+list(v) + [0]*(rankmax-ranktot-rank)) for v in M.kernel().gens()]]
                ranktot+=rank
            self._components_of_singular_fibres = sing_comps
        return self._components_of_singular_fibres
    
    @property
    def fibre_class(self):
        assert self.add == 2, "no fibre class in odd dimensions"
        return vector([0] * len(self.extensions + flatten(self.components_of_singular_fibres)) + [1,0])
    
    @property
    def section(self):
        assert self.add == 2, "no section in odd dimensions"
        return vector([0] * len(self.extensions + flatten(self.components_of_singular_fibres)) + [0,1])
    
    @property
    def monodromy_matrices_desingularisation(self):
        if not hasattr(self, '_monodromy_matrices_desingularisation'):
            monodromy_matrices_desingularisation = []
            for M in self.monodromy_matrices:
                decomposition = self.desingularise_matrix(M)
                assert prod(list(reversed(decomposition))) == M
                monodromy_matrices_desingularisation += [decomposition]
            self._monodromy_matrices_desingularisation = monodromy_matrices_desingularisation
        return self._monodromy_matrices_desingularisation

    def desingularise_matrix(self, M):
        raise NotImplementedError("`desingularise_matrix` not implemented")