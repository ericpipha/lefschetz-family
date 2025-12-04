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

from ore_algebra import *

from sage.modules.free_module_element import vector
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ
from sage.rings.qqbar import QQbar
from sage.matrix.special import zero_matrix

from .numperiods import interpolation

from sage.rings.imaginary_unit import I
from sage.groups.free_group import FreeGroup

from .voronoi import FundamentalGroupVoronoi
from .util import Util
from .translator import Translator
from .rootsBraid import RootsBraid


import logging
import time

logger = logging.getLogger(__name__)


class ExceptionalDivisorComputer(object):
    def __init__(self, variety):
        """
        """
        self.variety = variety
        self.Qt = PolynomialRing(QQ, 't')
        self.Qu = PolynomialRing(QQ, ['u', 't'])

    def _compute_coefs(self, b):
        R = self.variety.family.pol(b).parent()
        _vars = [v for v in R.gens()]
        forms=[v.dot_product(vector(_vars)) for v in self.variety.fibre.fibration[:2]]
        f=forms[0]/forms[1]
        S = PolynomialRing(QQ, _vars+['k','t'])
        k,t= S.gens()[-2:]
        eqs = [
            self.variety.family.pol(b), 
            forms[1]-1, 
            t*forms[1]-forms[0]
        ] + [(f.derivative(var).numerator()*k-self.variety.family.pol(b).derivative(var)*f.derivative(var).denominator()) for var in _vars]

        ideal = S.ideal(eqs).elimination_ideal(S.gens()[:-1])
        Qt = PolynomialRing(QQ, 't')

        return Qt(ideal.groebner_basis()[0]).coefficients(sparse=False)
    
    @property
    def critical_values_polynomial(self):
        if not hasattr(self, "_critical_values_polynomial"):
            u, t = self.Qu.gens()
            fr = interpolation.FunctionReconstruction(self.Qt, self._compute_coefs)
            coefs, denom = fr.recons(denomapart=True)
            self._critical_values_polynomial = sum([c(u)*t**i for i,c in zip(range(len(coefs)),coefs)])
        return self._critical_values_polynomial
    
    @property
    def fundamental_group_critical(self):
        """This is the fundamental group of C punctured at the points where the critical polynomial has multiple roots."""
        if not hasattr(self, "_fundamental_group_critical"):
            u, t = self.Qu.gens()
            double_roots = self.Qt((self.critical_values_polynomial*(t-self.variety.fibre.basepoint)).discriminant(t)(u=t)).roots(QQbar, multiplicities=False)
            fg= FundamentalGroupVoronoi(double_roots,self.variety.basepoint)
            fg.sort_loops()
            self._fundamental_group_critical = fg
        return self._fundamental_group_critical
    
    @property
    def adapted_paths(self):
        if not hasattr(self, "_adapted_paths"):
            translator = Translator(self.variety.fundamental_group,self.fundamental_group_critical)
            adapted_paths = [translator.specialize_path(path) for path in self.variety.fundamental_group.pointed_loops]

            # the following lines are here to remove loops around infinity. They are not really mandatory.
            looptot = []
            for path in adapted_paths:
                looptot += path
            looptot = Util.simplify_path(looptot)
            while looptot[0] == looptot[-1]:
                v = looptot[0]
                looptot = looptot[1:-1]
            looptot = [v]+looptot +[v]

            n = len(looptot)
            for j, path in enumerate(adapted_paths):
                for i in range(len(path)-n, 0, -1):
                    if path[i:i+n] in [looptot, list(reversed(looptot))]:
                        path = path[:i] + path[i+n-1:]
                adapted_paths[j] = path

            self._adapted_paths = adapted_paths
        return self._adapted_paths
    
    @property
    def edges(self):
        if not hasattr(self, "_edges"):
            _edges = []
            for path in self.adapted_paths:
                for i in range(len(path)-1):
                    e = path[i:i+2]
                    if e not in _edges and list(reversed(e)) not in _edges: 
                        _edges += [e]
            edges_spec = [[self.fundamental_group_critical.vertices[c] for c in e] for e in _edges]
            self._edges = edges_spec
        return self._edges

    @property
    def roots_braid(self):
        if not hasattr(self, "_roots_braid"):
            self._roots_braid = RootsBraid(self.critical_values_polynomial, self.edges, additional_points=[QQ(self.variety.fibre.basepoint)])
        return self._roots_braid

    @property
    def marking_init(self):
        """This is the initial marking at the basepoint"""
        if not hasattr(self, "_marking_init"):
            i = Util.select_closest_index(self.roots_braid.vertices, self.fundamental_group_critical.points[0])
            self._marking_init = self.roots_braid.system(i) + self.roots_braid.additional_points
        return self._marking_init
    
    @property
    def fundamental_group_fibre(self):
        if not hasattr(self, "_fundamental_group_fibre"):
            xmax=Util.simple_rational(max([s.real() for s in self.marking_init]), 0.000001)
            xmin=Util.simple_rational(min([s.real() for s in self.marking_init]), 0.000001)
            ymax=Util.simple_rational(max([s.imag() for s in self.marking_init]), 0.000001)
            fake_basepoint = 2*xmin-xmax+ymax*I/5
            fundamental_group_fibre = FundamentalGroupVoronoi(self.variety.fibre.critical_values + [self.variety.fibre.basepoint], fake_basepoint)
            fundamental_group_fibre.sort_loops()
            self._fundamental_group_fibre = fundamental_group_fibre
        return self._fundamental_group_fibre
    
    @property
    def words_fibre(self):
        if not hasattr(self, "_words_fibre"):
            fibre_translator = Translator(self.variety.fibre.fundamental_group, self.fundamental_group_fibre)
            spec_f = [fibre_translator.specialize_path(path) for path in self.variety.fibre.fundamental_group.pointed_loops]
            fakebp = self.fundamental_group_fibre.points[0]
            
            s_to_FG = [Util.select_closest_index(self.fundamental_group_fibre.points, s) for s in self.marking_init+[fakebp]]
            edges = [list(e[:2]) for e in self.roots_braid.minimal_cover_tree(self.marking_init).edges()]
            for i, e in enumerate(edges): # orient the edges away from basepoint
                if self.roots_braid.minimal_cover_tree(self.marking_init).distance(e[1], self.roots_braid.npoints) < self.roots_braid.minimal_cover_tree(self.marking_init).distance(e[0],self.roots_braid.npoints):
                    edges[i] = list(reversed(e))
            mtc_init = [[s_to_FG[i] for i in e] for e in edges]

            edges = [[c,p] for c, p in self.fundamental_group_fibre.polygons if c==self.variety.fibre.basepoint][0][1]
            cycle = [i for i in edges[0]]
            while cycle[0] != cycle[-1]:
                for e in edges:
                    if cycle[-1] in e and cycle[-2] not in e:
                        if e[0] == cycle[-1]:
                            cycle+=[e[1]]
                        else:
                            cycle+=[e[0]]
                        break
            cycle = list(reversed(cycle)) if Util.is_clockwise([self.fundamental_group_fibre.vertices[i] for i in cycle[:-1]]) else cycle
            cycle = cycle[:-1]

            for path in spec_f:
                for v in path:
                    if v in cycle:
                        i = cycle.index(v)
                        j = path.index(v)
                        cycle = cycle[i:] + cycle[:i]
                        res = path[:j] + cycle + list(reversed(path[:j+1]))
                        break
                else:
                    continue
                break
            spec_f = [res] + spec_f
            self._spec_f  = spec_f # it's nice to have this for plotting purposes

            self._words_fibre = [Translator.word(path, self.fundamental_group_fibre.duality, mtc_init, self.roots_braid.freeGroup) for path in spec_f]

        return self._words_fibre 
    
    @property
    def thimble_monodromy(self):
        if not hasattr(self, "_thimble_monodromy"):
            thimblegroup = FreeGroup(len(self.words_fibre), 't')
            ts = thimblegroup.gens()
            ttox = thimblegroup.hom(self.words_fibre)
            xtot = Util.invert_morphism(ttox)
            
            isos = []
            thimble_monodromy = []
            adapted_paths_z = [[self.fundamental_group_critical.vertices[v] for v in path] for path in self.adapted_paths]
            
            begin=time.time()
            logger.info("Computing the braid action.")
            self.roots_braid.compute_all_isomorphisms()
            logger.info("There are %d edges in total."% len(self.roots_braid.edges))
            for index_thimble, thimble_path in enumerate(adapted_paths_z):
                logger.info("Computing monodromy of path between blowups along loop %d/%d: %d edges "% (index_thimble+1,len(adapted_paths_z), len(thimble_path)))
                iso = self.roots_braid.isomorphism_along_path(thimble_path)
                isos += [iso]
                monodromy = zero_matrix(len(ts)-1)
                
                conjtobp = Util.middle(xtot(iso(ttox(ts[0]))))
                
                for tinit, chain in zip(ts[1:], self.variety.fibre.thimbles):
                    v = chain[0]
                    ttilde = xtot(iso(ttox(tinit)))
                    ttilde = conjtobp**-1*ttilde*conjtobp
                    
                    j = ts.index(tinit)-1
                    for t, p in list(reversed(ttilde.syllables())):
                        assert p in [-1,1]
                        i = ts.index(t)
                        if i==0:
                            continue
                        i-=1
                        monodromy[i, j]+=(self.variety.fibre.monodromy_matrices[i]**p-1)*v / self.variety.fibre.vanishing_cycles[i]
                        v = self.variety.fibre.monodromy_matrices[i]**p*v
                thimble_monodromy += [monodromy]
                assert v-chain[0] == self.variety.fibre.vanishing_cycles[j], "boundaries not matching"
            self._thimble_monodromy = thimble_monodromy
            self._isos = isos
            end = time.time()
            duration_str = time.strftime("%H:%M:%S",time.gmtime(end-begin))
            if end-begin >= 24*60*60:
                ndays = (end-begin)//24*60*60
                duration_str = str(ndays)+"d "+duration_str
            logger.info("Braid action computed in %s.", duration_str)
        return self._thimble_monodromy

            