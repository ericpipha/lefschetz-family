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


from sage.misc.flatten import flatten
from sage.graphs.graph import Graph
from sage.groups.free_group import FreeGroup
from sage.misc.lazy_attribute import lazy_attribute

from sage.rings.complex_mpfr import ComplexField

from .util import Util

import logging

logger = logging.getLogger(__name__)


CC = ComplexField(53)

class Translator(object):
    def __init__(self, A, B):
        """A and B are fundamental group classes, such that the points of A are a subset of the points of B
        The basepoint can be distinct. The goal of this class is to find paths of B that represent the same homotopy classes as the paths of A.
        If the basepoints are distinct, then the homotopy class of the loop around A.basepoint is also computed as a path of B.
        """
        
        self.A = A
        self.B = B


    @lazy_attribute
    def AtoB(self):
        return [Util.select_closest_index(self.B.qpoints, p) for p in self.A.qpoints]

    
    @lazy_attribute
    def edges_tree(self):
        """This tree will serve as the alphabet for the fundamental group"""
        minimal_cover_tree = Graph(len(self.A.qpoints)) 
        edges = flatten([[(i,j) for i in range(j)] for j in range(len(self.A.qpoints))], max_level=1) 
        edges.sort(key=(lambda e: Util.simple_rational(abs(CC(self.A.qpoints[e[0]]-self.A.qpoints[e[1]])), 10e-10))) # we sort edges by length
        for e in edges:
            if len(minimal_cover_tree.shortest_path(e[0], e[1]))==0:
                minimal_cover_tree.add_edge(e)
        return [list(e)[:2] for e in minimal_cover_tree.edges()]
    
    @lazy_attribute
    def alphabet(self):
        return FreeGroup(len(self.edges_tree))
    
    @property
    def letters(self):
        return self.alphabet.gens()
    
    @property
    def Bduality(self):
        if not hasattr(self, "_Bduality"):
            edgesB = []
            for e,d in self.B.duality:
                if d not in edgesB and list(reversed(d)) not in edgesB:
                    edgesB += [d]

            delaunay = Graph()
            for e in edgesB:
                dist = Util.simple_rational(abs(CC(self.B.qpoints[e[0]]-self.B.qpoints[e[1]])), 10**-10)
                delaunay.add_edge(e + [dist])

            edgesA = [[self.AtoB[i] for i in e] for e in self.edges_tree]
            paths = []
            for e in edgesA:
                paths += [delaunay.shortest_path(e[0], e[1], by_weight=True)] 

            Bduality = []
            for dA, path in zip(self.edges_tree, paths):
                for i in range(len(path)-1):
                    e = path[i:i+2]
                    for e2,d2 in self.B.duality:
                        if d2 == e:
                            Bduality += [[e2, dA]]
                            break
            self._Bduality = Bduality
        return self._Bduality

    def wordA(self, path):
        """Given a path of A, return its word in terms of the tree"""
        return self.word(path, self.A.duality, self.edges_tree, self.alphabet)
    def wordB(self, path):
        """Given a path of B, return its word in terms of the tree"""
        return self.word(path, self.Bduality, self.edges_tree, self.alphabet)
    
    @staticmethod
    def word(path, duality, edges, alphabet=None):
        dual_temp = [[e,d] for e,d in duality if d in edges]
        dual_temp.sort(key=lambda e: edges.index(e[1]))
        edges_temp = [e for e,_ in dual_temp]
        if alphabet==None:
            alphabet = FreeGroup(len(edges))
        w = alphabet(1)
        letters = alphabet.gens()
        for i in range(len(path)-1):
            e = path[i:i+2]
            if e in edges_temp:
                dual = dual_temp[edges_temp.index(e)][1]
                w = letters[edges.index(dual)]**-1 * w
            e = list(reversed(e))
            if e in edges_temp:
                dual = dual_temp[edges_temp.index(e)][1]
                w = letters[edges.index(dual)] * w
        return w
    
    @lazy_attribute
    def thin_gens(self):
        return [self.B.pointed_loops[i-1] for i in self.AtoB[1:]]
    
    @lazy_attribute
    def fat_gens(self):
        points = [i-1 for i in self.AtoB[1:]]
        paths = [[]]
        first=True
        for i, path in enumerate(self.B.pointed_loops):
            if i in points:
                if first:
                    first = False
                else:
                    paths += [[]]
            if i!=self.AtoB[0]-1:
                paths[-1] += path
        return [Util.simplify_path(path) for path in paths]
    
    @property
    def lift(self):
        if not hasattr(self, "_lift"):
            words = [self.wordB(path) for path in self.fat_gens]
            proj = self.alphabet.hom(words)
            self._lift = Util.invert_morphism(proj)
        return self._lift
    
    def specialize_path(self, path):
        """Take a path of A and yield a path B with the same homotopy class"""
        w = self.lift(self.wordA(path))
        # conj = Util.middle(w)
        
        path = []
        for l, p in list(reversed(w.syllables())):
            assert p in [-1,1]
            i = self.letters.index(l)
            if p==1:
                path = path + self.fat_gens[i]
            if p==-1:
                path = path + list(reversed(self.fat_gens[i]))
        return Util.simplify_path(path)
        