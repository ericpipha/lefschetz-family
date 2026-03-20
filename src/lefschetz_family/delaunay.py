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

from sage.rings.complex_mpfr import ComplexField
from sage.graphs.graph import Graph
from sage.rings.imaginary_unit import I
from sage.functions.other import arg

from sage.misc.flatten import flatten

class FundamentalGroupDelaunay(object):
    def __init__(self, points, basepoint):
        assert basepoint not in points

        self._points = [basepoint] + points

        self.CC = ComplexField(500)


    @property
    def points(self):
        return self._points

    @property
    def basepoint(self):
        return self.points[0]

    @property
    def npoints(self):
        return len(self.points)
    

    @property
    def minimal_graph(self):
        if not hasattr(self, '_minimal_graph'):
            tree = Graph(self.npoints) 
            edges = flatten([[(i,j) for i in range(j)] for j in range(self.npoints)], max_level=1) 
            edges.sort(key=(lambda e: abs(self.CC(self.points[e[0]])-self.CC(self.points[e[1]])))) # we sort edges by length
            for e in edges:
                if len(tree.shortest_path(e[0], e[1]))==0:
                    tree.add_edge(e)
            self._minimal_graph = tree

        return self._minimal_graph

    
    @property
    def neighbours(self):
        if not hasattr(self, '_neighbours'):
            smallangleshift = -I/100000000000 # this assumes there are no angle very close to -pi, so we can send angles equal to -pi below the line
            neighbours=[[] for vertex in self.minimal_graph.vertices()]
            for vertex in self.minimal_graph.vertices():
                l = self.minimal_graph.neighbors(vertex)
                l.sort(key=lambda v2:arg(self.CC(self.points[v2] - self.points[vertex] + smallangleshift/abs(self.CC(self.points[v2] - self.points[vertex])))))
                neighbours[vertex] = l
            self._neighbours = neighbours
        return self._neighbours

    def _visit_neighbours(self, vertex, parent):
        neighbours = self.neighbours[vertex]
        if len(neighbours) == 1:
            return [[vertex]]
        assert parent in neighbours, "parent node is not a neighbour"

        prefix=[vertex]
        index_parent = neighbours.index(parent)

        i=index_parent+1
        if i==len(neighbours):
            i=0
            prefix=[vertex, "loop"]
        paths=[]
        while i != index_parent:
            paths = paths+[prefix+path_child for path_child in self._visit_neighbours(neighbours[i], vertex)]
            i=i+1
            if i == len(neighbours):
                i=0
                prefix=[vertex, "loop"]
        return paths + [[vertex]]

    @property
    def paths(self):
        if not hasattr(self, "_paths"):
            paths = []
            for vertex in self.neighbours[0]:
                paths= paths + self._visit_neighbours(vertex, 0)
            paths = [[0]+path for path in paths]
            self._paths = paths
        return self._paths