# -*- coding: utf-8 -*-

import sage.all

from sage.rings.rational_field import QQ
from sage.rings.complex_mpfr import ComplexField
from sage.graphs.graph import Graph
from sage.rings.imaginary_unit import I
from sage.functions.other import arg

from sage.misc.flatten import flatten

from sage.graphs.spanning_tree import boruvka
from delaunay_triangulation import triangulate

import os

from .util import Util

class FundamentalGroupDelaunayDual(object):
    def __init__(self, points, basepoint, border=5):
        assert basepoint not in points

        self._points = [basepoint] + points
        self._border = border

        self.CC = ComplexField(50) # ultimately this should be dropped for certified precision


    def rationalize(self, z):
        zcc = self.CC(z)
        zr, zi = zcc.real(), zcc.imag()
        zq = Util.simple_rational(zr, self.prec) + I*Util.simple_rational(zi, self.prec)
        return zq

    def point_to_complex_number(self, pt):
        return pt[0] + I*pt[1]
    def complex_number_to_point(self, z):
        return (QQ(z.real()), QQ(z.imag()))

    @property
    def prec(self):
        if not hasattr(self, "_prec"):
            points_differences = flatten([[self.CC(self._points[i]) - self.CC(self._points[j]) for j in range(i)] for i in range(len(self._points))])
            self._prec = Util.simple_rational(min([abs(p) for p in points_differences]), min([abs(p) for p in points_differences])/100)/100
        return self._prec
    
    @property
    def points(self):
        return self._points
    

    @property
    def vertices(self):
        if not hasattr(self, "_vertices"):
            polygons = self.polygons 
            # calling self.polygons defines self._vertices -- this prevents unecessary 
            # loops, but there is likely a better way to achieve the same goal
        return self._vertices
    
    @property
    def duality(self):
        if not hasattr(self, "_duality"):
            polygons = self.polygons 
            # calling self.polygons defines self._duality -- this prevents unecessary 
            # loops, but there is likely a better way to achieve the same goal
        return self._duality

    @property
    def edges(self):
        """ returns the edges of the Voronoi graph given as pairs of indices of self.vertices, in decreasing length
        """
        if not hasattr(self, "_edges"):
            edges = []
            for center, polygon in self.polygons:
                for e in polygon:
                    if e not in edges and [e[1], e[0]] not in edges:
                        edges += [e]
            connection_to_basepoint = min([i for i in range(1, len(self.vertices))], key=lambda i: abs(self.vertices[0] - self.vertices[i]))
            edges += [[0, connection_to_basepoint]]
            edges.sort(reverse=True, key=lambda e:(self.vertices[e[0]].real()-self.vertices[e[1]].real())**2 + (self.vertices[e[0]].imag()-self.vertices[e[1]].imag())**2)
            self._edges = edges
        return self._edges

    @property
    def border(self):
        return self._border

    @property
    def qpoints(self):
        if not hasattr(self, "_qpoints"):
            self._qpoints = [self.rationalize(p) for p in self.points]
        return self._qpoints


    @property
    def graph(self):
        if not hasattr(self, "_graph"):
            self._graph = Graph([(e[0], e[1], self.rationalize(abs(self.vertices[e[0]] - self.vertices[e[1]]))) for e in self.edges])
        return self._graph

    @property
    def tree(self):
        if not hasattr(self, "_tree"):
            tree_edges = boruvka(self.graph)
            self._tree = Graph(tree_edges)
        return self._tree

    @property
    def loop_points(self):
        if not hasattr(self, "_loop_points"):
            loop_points = []
            for i, loop in enumerate(self.loops):
                loop_point = min(loop[1:], key=lambda v:self.tree.distance(v,0))
                index = loop.index(loop_point)
                if index!=0:
                    loop = loop[index:-1] + loop[:index] + [loop[index]]
                self.loops[i] = loop
                loop_points+=[loop_point]
            self._loop_points = loop_points
        return self._loop_points

    @property
    def paths(self):
        if not hasattr(self, "_paths"):
            self._paths = [self.tree.all_paths(0, v)[0] for v in self.loop_points]
        return self._paths
    
    @property
    def pointed_loops(self):
        if not hasattr(self, "_pointed_loops"):
            pointed_loops = []
            for i in range(len(self.points)-1):
                pointed_loops += [self.paths[i][:-1] + self.loops[i] + list(reversed(self.paths[i][:-1]))]
            self._pointed_loops = pointed_loops
        return self._pointed_loops
    
    

    @property
    def loops(self):
        if not hasattr(self, "_loops"):
            loops = []
            for center, polygon in self.polygons:
                polygon = [[v for v in e] for e in polygon]
                loop = polygon.pop()
                while len(polygon) > 0:
                    for i in range(len(polygon)):
                        e = polygon[i]
                        if e[0] == loop[-1]:
                            loop += [e[1]]
                        elif e[1] == loop[-1]:
                            loop += [e[0]]
                        else:
                            assert i!= len(polygon), "polygon is not a loop, possibly because the voronoi cell is not bounded"
                            continue
                        polygon.pop(i)
                        break

                loops += [list(reversed(loop))] if Util.is_clockwise([self.vertices[i] for i in loop[:-1]]) else [loop]
            self._loops = loops
        return self._loops

    @property
    def minimal_tree(self):
        if not hasattr(self, "_minimal_tree"):
            edges = []
            for path in self.paths:
                for i in range(len(path)-1):
                    e0 = path[i]
                    e1 = path[i+1]
                    if [e0,e1] not in edges and [e1,e0] not in edges:
                        edges+=[[e0, e1]]
            self._minimal_tree = Graph(edges)
        return self._minimal_tree

    def neighbours(self, v): # maybe this shoudl be done only once?
        neighbours = self.graph.neighbors(v)
        neighbours.sort(key=lambda v2:arg(self.vertices[v2] - self.vertices[v]))
        return neighbours

    def sort_loops(self):
        order = self._sort_loops_rec(0)
        self._points = [self.points[0]] + [self.points[i+1] for i in order]
        self._qpoints = [self.qpoints[0]] + [self.qpoints[i+1] for i in order]
        self._rootapprox = self._qpoints + self._rootapprox[len(self._qpoints):]
        self._loops = [self.loops[i] for i in order]
        self._paths = [self.paths[i] for i in order]
        self._duality = [[edge, [order.index(i-1)+1 if i!=0 and i<len(self.points) else i for i in dual]] for [edge, dual] in self._duality]
        if hasattr(self, "_pointed_loops"):
            self._pointed_loops = [self.pointed_loops[i] for i in order]
        return order

    def adapted_loops(self, subvoronoi): # This is broken.
        for v in subvoronoi.points:
            assert v in self.points
        correspondance = []
        for v in subvoronoi.vertices:
            correspondance += [Util.select_closest_index(self.vertices,v)]
        adapted_loops = []
        for loop in subvoronoi.pointed_loops:
            adapted_loop = [correspondance[loop[0]]]
            for v in loop[1:]:
                adapted_loop += self.graph.shortest_path(adapted_loop[-1], correspondance[v])[1:]
            adapted_loops += [adapted_loop]
        return adapted_loops


    def _sort_loops_rec(self, v, parent=None, depth=0):
        neighbours = self.neighbours(v)
        tree_neighbours = self.minimal_tree.neighbors(v)
        loops = [(i, loop[1]) for i, loop in enumerate(self.loops) if loop[0]==v]
        if parent!=None:
            index = neighbours.index(parent)
            neighbours = neighbours[index:] + neighbours[:index]

        order = []
        for child in neighbours:
            if child!= parent and child in tree_neighbours:
                order+=self._sort_loops_rec(child, v, depth+1)
            for loop in loops:
                if loop[1] == child:
                    order+=[loop[0]]
        return order


    @property
    def polygons(self): # this interfacing with VoronoiDiagram is so ugly
        if not hasattr(self, "_polygons"):
            vertices = [self.points[0]]
            rootapprox = [p for p in self.qpoints] # there should be a `copy` function

            qpoints = [self.complex_number_to_point(z) for z in self.qpoints]
            reals = [s[0] for s in qpoints]
            imags = [s[1] for s in qpoints]
            xmin, xmax, ymin, ymax = min(reals), max(reals), min(imags), max(imags)
            shift = max(ymax-ymin, xmax-xmin)/2 # there is likely something more clever to do here
            xmax, ymax = max(xmax, ymax),max(xmax, ymax)
            xmin, ymin = min(xmin, ymin),min(xmin, ymin)
            xmin, xmax, ymin, ymax = xmin - shift, xmax + shift, ymin - shift, ymax + shift
            
            for i in range(self.border):
                step = QQ(i)/QQ(self.border)
                rootapprox += [xmin + step*(xmax-xmin) + I*ymax]
                rootapprox += [xmax + step*(xmin-xmax) + I*ymin]
                rootapprox += [xmin + I*(ymin + step*(ymax-ymin))]
                rootapprox += [xmax + I*(ymax + step*(ymin-ymax))]
            
            list_of_rational_points = [] # why is this necessary? I do not know, but otherwise VoronoiDiagram throws a fit
            for z in rootapprox:
                p = self.complex_number_to_point(z)
                list_of_rational_points+= [[QQ(p[0]), QQ([p[1]])]]

            delvertices = [triangulate.Vertex(p.real(), p.imag()) for p in rootapprox]
            dt = triangulate.delaunay(delvertices)

            self._delaunay_triangulation = dt
            self._rootapprox = rootapprox
            
            polygons_temp = [[p, []] for p in rootapprox]
            
            for triangle in dt:
                ts = [t.x+I*t.y for t in triangle]
                center = sum(ts)/3
                for i1, i2 in [[0,1],[1,2], [2,0]]:
                    p1 = ts[i1]
                    p2 = ts[i2]
                    middle = (p1+p2)/2
                    edge = [center, middle]

                    v1, v2 = Util.select_closest_index(rootapprox, p1), Util.select_closest_index(rootapprox, p2)
                    

                    for v in [v1, v2]:
                        polygons_temp[v][1]+=[[edge, [v1,v2]]]

            # we are only interested in cells around elements of self.points
            indices = [Util.select_closest_index([center for center, polygon in polygons_temp], c) for c in self.qpoints[1:]]
            polygons_temp = [polygons_temp[i] for i in indices]

            # then we translate the edges in rational coordinate as well
            polygons = []
            duality = []
            all_edges = []
            for center, polygon in polygons_temp:
                edges = []
                for edge, dual in polygon:
                    e0 = self.rationalize(edge[0])
                    if e0 not in vertices:
                        vertices += [e0]
                    e1 = self.rationalize(edge[1])
                    if e1 not in vertices:
                        vertices += [e1]
                    if e0 != e1:
                        e = [vertices.index(e0),vertices.index(e1)]
                        edges += [e]
                        if e not in all_edges and (dual[0] < len(self.points) and dual[1] < len(self.points)):
                            duality += [[e, dual]]
                            all_edges += [e]
                polygons += [[center, edges]]

            self._vertices = vertices
            self._polygons = polygons
            self._duality = duality

        return self._polygons





