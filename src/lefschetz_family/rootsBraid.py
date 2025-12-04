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

from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ
from sage.rings.qqbar import QQbar
from sage.graphs.graph import Graph
from sage.rings.imaginary_unit import I

from sage.rings.complex_mpfr import ComplexField
from sage.groups.free_group import FreeGroup
from sage.misc.flatten import flatten
from sage.schemes.curves.zariski_vankampen import followstrand
from sage.functions.other import arg

from sage.parallel.decorate import parallel


from .util import Util

import logging
import time
import os
from copy import copy

logger = logging.getLogger(__name__)


class RootsBraid(object):
    def __init__(self, P, edges, basepoint=None, additional_points=[]):
        """P, a polynomial in two variables u and t.

        This class computes the braid group of roots (in t) of P(u) as u moves along a path
        """
        
        R = PolynomialRing(QQ, ['u','t'])
        u,t = R.gens()
        self.P = P(u,t)
        self.additional_points=additional_points
        self.npoints = self.P.degree(self.P.parent().gens()[1]) + len(self.additional_points)
        self._maximalstep = 1/1000

        self.freeGroup = FreeGroup(self.npoints)
        self.xs = list(self.freeGroup.gens())
        # self.additional_points=additional_points

        self.hasbasepoint = (basepoint != None)
        self.basepoint = basepoint

        self.edges = []
        self.vertices = []
        for e in edges:
            if e[0] not in self.vertices:
                self.vertices += [e[0]]
            if e[1] not in self.vertices:
                self.vertices += [e[1]]
            e2 = [self.vertices.index(v) for v in e]
            if e2 not in self.edges and list(reversed(e2)) not in self.edges:
                self.edges+=[e2]



    @property
    def singularities(self):
        if not hasattr(self,'_singularities'):
            t = self.P.parent()('t')
            discrP = self.P.discriminant(t)
            Qu=PolynomialRing(QQ[I], 'u')
            self._singularities = Qu(discrP).roots(QQbar, multiplicities=False)
        return self._singularities
    
    def system(self, i):
        """The configuration of roots at self.vertices[i]"""
        if not hasattr(self,'_systems'):
            self._systemsQ = [False]*len(self.vertices)
            self._systems = [None]*len(self.vertices)
        if not self._systemsQ[i]:
            CC=ComplexField(500)
            Qt=PolynomialRing(QQ[I], 't')
            p = self.vertices[i]
            u,t = self.P.parent()('u'),self.P.parent()('t')
            roots = Qt(self.P(u=p)).roots(QQbar, multiplicities=False)
            roots = [CC(r)for r in roots]
            roots.sort(key=lambda z: (z.real(), z.imag()))
            self._systems[i] = roots
            self._systemsQ[i] = True
        return self._systems[i]

    def compute_all_braids(self):
        if not hasattr(self,'_braid'):
            self._braid = [(None, None)]*len(self.edges)
            self._braidQ = [False]*len(self.edges)
        begin = time.time()
        logger.info("Computing all braids (%d in total).", (len(self.edges)))
        result = self._compute_braid([(e,i) for i, e in enumerate(self.edges) if not self._braidQ[i]])
        for arg, res in result:
            braid, braidinverse = res
            i, _ =  self.edge(arg[0][0])
            self._braid[i] = braid, braidinverse
            self._braidQ[i] = True
        end = time.time()
        duration_str = time.strftime("%H:%M:%S",time.gmtime(end-begin))
        if end-begin >= 24*60*60:
            ndays = (end-begin)//24*60*60
            duration_str = str(ndays)+"d "+duration_str
        logger.info("Braids computed in %s."% (duration_str))

    def braid(self, e):
        if not hasattr(self,'_braid'):
            self._braid = [(None, None)]*len(self.edges)
            self._braidQ = [False]*len(self.edges)

        i, inverse = self.edge(e)
        if not self._braidQ[i]:
            logger.info("[%d] Computing braid along edge %d."% (os.getpid(), i))

            res, resinverse = self._compute_braid(e)
            
            self._braid[i] = (resinverse, res) if inverse else (res, resinverse)
            self._braidQ[i] = True

        return self._braid[i][1 if inverse else 0]

    @parallel
    def _compute_braid(self, e, i):
        from sage.schemes.curves.zariski_vankampen import followstrand
        logger.info("[%d] Computing braid along edge %d"% (os.getpid(), i))
        begin = time.time()
        roots = self.system(e[0])
        res=[]
        j=0
        steps = [begin]
        for r in roots:   
            j+=1
            # logger.info("[%d] Computing thread %d of edge %d."% (os.getpid(), j, i))
            line = followstrand(self.P, [z.minpoly()(self.P.parent().gens()[1]) for z in self.additional_points], self.vertices[e[0]], self.vertices[e[1]],r, 50)
            res+=  [[[c[0], c[1]+I*c[2]] for c in line]]
            steps += [time.time()]
        
        end = time.time()
        duration = end-begin
        duration_str = time.strftime("%H:%M:%S",time.gmtime(duration))
        if end-begin >= 24*60*60:
            ndays = (end-begin)//24*60*60
            duration_str = str(ndays)+"d "+duration_str
        duration_str_steps = ' '.join([time.strftime("%H:%M:%S",time.gmtime(steps[i]-steps[i-1])) for i in range(1, len(steps))])
        logger.info("[%d] Finished computation of braid along edge %d. [total time:%s], [per root: %s]."% (os.getpid(), i, duration_str, duration_str_steps))

        resinverse = [list(reversed([[1-t, x] for t, x in thread])) for thread in res]
        rootsinverse = self.system(e[1])
        endthreads = [thread[0][1] for thread in resinverse]
        order = [Util.select_closest_index(endthreads, r) for r in rootsinverse]
        resinverse = [resinverse[i] for i in order]
        return res,resinverse

    def interpolate(self, thread, t):
        if t==1:
            return thread[-1][1]
        for i in range(len(thread)-1,-1,-1):
            if t>=thread[i][0]:
                break
        t0,x0, t1,x1 = thread[i][0], thread[i][1], thread[i+1][0], thread[i+1][1]
        return ((t1-t)*x0+ (t-t0)*x1)/(t1-t0)


    def minimal_cover_tree(self, section):
        CC=ComplexField(500)
        mtc=Graph(self.npoints+1) 
        edges = flatten([[(i,j) for i in range(j)] for j in range(self.npoints)], max_level=1) 
        edges.sort(key=(lambda e: Util.simple_rational(abs(CC(section[e[0]]-section[e[1]])), 10e-10))) # we sort edges by length
        for e in edges:
            if len(mtc.shortest_path(e[0], e[1]))==0:
                mtc.add_edge(e)
        # then we add the path to the basepoint
        vertices = [i for i in range(self.npoints)]
        if self.hasbasepoint:
            vertices.sort(key=(lambda v: Util.simple_rational(abs(CC(section[v]-self.basepoint)), 10e-10)))
        else:
            vertices.sort(key=(lambda v: (section[v].real(), -section[v].imag()))) # the fixed basepoint is also specific to example
        mtc.add_edge([self.npoints,vertices[0]])
        return mtc

    def edge(self, e):
        """Given an edge e, returns (i, False) if self.edges[i]==e and (i, True) if self.edges[i]==list(reversed(e))"""
        if [e[0], e[1]] in self.edges:
            return self.edges.index([e[0], e[1]]), False
        if [e[1], e[0]] in self.edges:
            return self.edges.index([e[1], e[0]]), True
        raise Exception("edge is not in edge list")

    def braid_section(self, braid, t):
        """Given a braid (a list of threads) and 0<t<1, returns the section of the braid at t."""
        section = []
        for thread in braid:
            section += [self.interpolate(thread, t)]
        return section+self.additional_points

    def raffine_braid(self, braid):
        ts=[]
        for thread in braid:
            for p in thread:
                ts+=[p[0]]
        ts = list(set(ts))
        ts.sort()
        for t0,t1 in zip(ts[:-1], ts[1:]):
            while t1-t0>1.1*self._maximalstep:
                t0+=self._maximalstep
                ts.append(t0)
        ts.sort()
        return [self.braid_section(braid, t) for t in ts]


    def isomorphisms(self, e):
        if not hasattr(self,'_isomorphisms'):
            self._isomorphisms = [[None, None] for i in range(len(self.edges))]
            self._isomorphismsQ = [False]*len(self.edges)
        i, inverse = self.edge(e)
        if not self._isomorphismsQ[i]:
            logger.info("[%d] Computing isomorphism of edge %d."% (os.getpid(), i))
            CC=ComplexField(500)

            iso = self._compute_isomorphism(e)

            self._isomorphisms[i][1 if inverse else 0] = iso
            self._isomorphismsQ[i] = True

        if self._isomorphisms[i][1 if inverse else 0] == None:
            logger.info("[%d] Inverting isomorphism of edge %d."% (os.getpid(), i))
            self._isomorphisms[i][1 if inverse else 0] = Util.invert_morphism(self._isomorphisms[i][0 if inverse else 1])

        return self._isomorphisms[i][1 if inverse else 0]

    def compute_all_isomorphisms(self):
        if not hasattr(self,'_isomorphisms'):
            self._isomorphisms = [[None, None] for i in range(len(self.edges))]
            self._isomorphismsQ = [False]*len(self.edges)
        self.compute_all_braids()
        begin = time.time()
        logger.info("Computing all isomorphisms.")
        result = self._compute_isomorphism([e for i, e in enumerate(self.edges) if not self._isomorphismsQ[i]])
        for arg, res in result:
            iso = res
            i, _ =  self.edge(arg[0][0])
            self._isomorphisms[i][0] = iso
            self._isomorphismsQ[i] = True
        end = time.time()
        duration_str = time.strftime("%H:%M:%S",time.gmtime(end-begin))
        if end-begin >= 24*60*60:
            ndays = (end-begin)//24*60*60
            duration_str = str(ndays)+"d "+duration_str
        logger.info("Isomorphisms computed in %s."% (duration_str))

    @parallel
    def _compute_isomorphism(self, e):
        i, inverse = self.edge(e)
        braid = self.braid(e)
        sections = self.raffine_braid(braid)

        mtcs = [self.minimal_cover_tree(section) for section in sections]

        mtcinit = self.minimal_cover_tree(self.system(e[0]) + self.additional_points)

        iso = self.freeGroup.hom(self.xs)
        if mtcs[0] != mtcinit:
            logger.info("[%d] Encountered distinct minimal covering trees between beginning of braid %d and standard configuration."% (os.getpid(), i))
            iso = self.braid_action(mtcinit, mtcs[0], sections[0])

        for k in range(len(mtcs)-1):
            mtc1 = mtcs[k]
            mtcfin = mtcs[k+1]
            if mtc1!=mtcfin:
                logger.info("[%d] Encountered distinct minimal covering trees between sections %d and %d (out of %d)."% (os.getpid(), k, k+1, len(mtcs)))
                iso = self.braid_action(mtc1, mtcfin, sections[k])*iso
                iso = self.freeGroup.hom([iso(x) for x in self.xs])

        section1 = sections[-1]
        section2 = self.system(e[1]) + self.additional_points

        perm = [Util.select_closest_index(section2,c) for c in section1]+[self.npoints] # this is fine because they are equal (although their presentation might differ)
            
        mtc1 = mtcs[-1]
        mtcfin = self.minimal_cover_tree(section2)

        mtcn = Graph(self.npoints+1)
        for e in mtc1.edges():
            mtcn.add_edge((perm[e[0]], perm[e[1]]))

        oe1, oe2 = self.ordered_edges(mtc1), self.ordered_edges(mtcn)
        perm_edge = [oe2.index(self.normalize_edge((perm[e[0]],perm[e[1]]))) for e in oe1]
        transition_iso = self.freeGroup.hom([self.xs[i] for i in perm_edge])
        if mtcn!=mtcfin:
            logger.info("[%d] Encountered distinct minimal covering trees between end of braid %d and standard configuration."% (os.getpid(), i))
            transition_iso = self.braid_action(mtcn, mtcfin, section2)*transition_iso

        iso = transition_iso*iso
        iso = self.freeGroup.hom([iso(x) for x in self.xs])
        return iso
    
    def isomorphism_along_path(self,path):
        """Given a path `path`, computes the braid (as an isomorphism on the fundamental group of the punctured plane) along `path`"""
        path = [Util.select_closest_index(self.vertices, p)  for p in path]
        edges = [path[i:i+2] for i in range(len(path)-1)] # TODO try product([self.isomorphism(e) for e in list(reversed(path_edges))])
        
        iso = self.isomorphisms(edges[0])
        for e in edges[1:]:
            iso = self.isomorphisms(e)*iso
            iso = self.freeGroup.hom([iso(x) for x in self.xs])
        return iso

    def edge_difference(self, g1, g2):
        """Given two graphs g1, g2, yields the lists `removed_edges, added_edges` such that `removed_edges` is the edges in `g1` and not in `g2`, and `added_edges` the opposite."""
        removed_edges = []
        added_edges = []
        for e in g1.edges():
            if not g2.has_edge(e):
                removed_edges+=[e]
        for e in g2.edges():
            if not g1.has_edge(e):
                added_edges+=[e]
        return removed_edges, added_edges
    
    def braid_action(self,g1,g2, section):
        """ computes the isomorphism elements characterizing the change from graph g1 to graph g2
        """
        iso = self.freeGroup.hom(self.xs)
        removed_edges, added_edges = self.edge_difference(g1, g2)

        # logger.info("Starting from graph with edges (%d, %d), (%d, %d), (%d, %d)."% tuple(flatten([[e[0], e[1]] for e in g1.edges()])))
        for e in removed_edges:
            # logger.info("Removing edge (%d,%d)."%(e[0], e[1]))
            # we add the edge to see what cycle appears
            gx = copy(g1)
            gx.delete_edge(e)

            if not e[0] in gx.connected_component_containing_vertex(self.npoints):
                e = (e[1], e[0])

            for ea in added_edges:
                ga = copy(gx)
                ga.add_edge(ea)
                if ga.connected_components_number()==1:
                    break
            ga = copy(g1)
            ga.add_edge(ea)
            assert ga.connected_components_number()==1
            # logger.info("Adding edge (%d,%d)."%(ea[0], ea[1]))
            ea = self.normalize_edge(ea)

            cycle = ga.cycle_basis()[0]
            # then we normalize the cycle (we want to start at the vertex from the edge that was deleted that's in the same component as the basepoint)

            ci = cycle.index(e[0])
            if cycle[ci+1 if ci+1<len(cycle) else 0] == e[1]:

                cycle.reverse()
            ci = cycle.index(e[0])
            cycle = cycle[ci:] + cycle[:ci]

            if self.hasbasepoint:
                clockwise = Util.is_clockwise([section[i] if i!=self.npoints else self.basepoint for i in cycle])
            else:
                xmax=Util.simple_rational(max([s.real() for s in section]), 0.1)
                xmin=Util.simple_rational(min([s.real() for s in section]), 0.1)
                ymax=Util.simple_rational(max([s.imag() for s in section]), 0.1)
                clockwise = Util.is_clockwise([section[i] if i!=self.npoints else 2*xmin-xmax+ymax*I/5 for i in cycle])

            
            # logger.info("Clockwise cycle" if clockwise else "Counterclockwise cycle")

            beforeLoop = True
            beforeLink = True
            beforeEdges1 = []
            beforeEdges2 = []
            afterEdges = []
            link=min(cycle, key=lambda v:ga.distance(v, self.npoints))

            for j in range(len(cycle)-1):
                e2 = (cycle[j], cycle[j+1])
                if link==cycle[j]:
                    beforeLink = False
                if e2[0]>e2[1]:
                    e2=(e2[1],e2[0])
                if self.normalize_edge(e2) == ea:
                    beforeLoop = False
                    gx.add_edge(ea)
                else:
                    if beforeLink:
                        beforeEdges1+=[e2]
                    elif beforeLoop:
                        beforeEdges2+=[e2]
                    else:
                        afterEdges+=[e2]
            e = self.normalize_edge(e)

            inside = []
            outside = []
            for j in range(len(cycle)):
                before, current, after = [cycle[l%len(cycle)] for l in [j-1, j, j+1]] 
                neighbours = self.neighbours(ga, current, section)
                neighbours = neighbours[neighbours.index(before):] + neighbours[:neighbours.index(before)]
                if clockwise:
                    inside += [[current, v] for v in neighbours[neighbours.index(after)+1:]]
                    outside += [[current, v] for v in neighbours[1:neighbours.index(after)]]
                else:
                    inside += [[current, v] for v in neighbours[1:neighbours.index(after)]]
                    outside += [[current, v] for v in neighbours[neighbours.index(after)+1:]]
            # then add all the edges rooted at points of inside
            inside2 = []
            for ei in inside:
                gtempx = copy(ga)
                gtempx.delete_vertex(ei[0])
                inside2 += self.ordered_edges(gtempx.subgraph(gtempx.connected_component_containing_vertex(ei[1])))
                inside2 += [self.normalize_edge(ei)]

            outside2 = []
            for ei in outside:
                gtempx = copy(ga)
                gtempx.delete_vertex(ei[0])
                outside2 += self.ordered_edges(gtempx.subgraph(gtempx.connected_component_containing_vertex(ei[1])))
                outside2 += [self.normalize_edge(ei)]

            basepointisinside = self.hasbasepoint and self.npoints in flatten(inside2) and self.npoints not in cycle
            otherside = outside2 if basepointisinside else inside2
            sameside = inside2 if basepointisinside else outside2

            res = []
            ini = self.ordered_edges(g1)
            fin = self.ordered_edges(gx)
            xr= self.xs[fin.index(ea)]

            for e2 in ini:
                if (clockwise and not basepointisinside) or (not clockwise and basepointisinside):
                    if e2 in beforeEdges1:
                        res+=[self.xs[fin.index(e2)]*xr]
                    elif e2 in beforeEdges2:
                        res+=[xr**-1*self.xs[fin.index(e2)]]
                    elif e2 in afterEdges:
                        res+=[self.xs[fin.index(e2)]**-1*xr]
                    elif e2 == e:
                        res+=[xr]
                    elif e2 in otherside:
                        res+=[xr**-1*self.xs[fin.index(e2)]*xr]
                    elif e2 in sameside:
                        res+=[self.xs[fin.index(e2)]]
                    else:
                        logger.warning("unrecognized edge")
                else:
                    if e2 in beforeEdges1:
                        res+=[xr*self.xs[fin.index(e2)]]
                    elif e2 in beforeEdges2:
                        res+=[self.xs[fin.index(e2)]*xr**-1]
                    elif e2 in afterEdges:
                        res+=[xr*self.xs[fin.index(e2)]**-1]
                    elif e2 == e:
                        res+=[xr]
                    elif e2 in otherside:
                        res+=[xr*self.xs[fin.index(e2)]*xr**-1]
                    elif e2 in sameside:
                        res+=[self.xs[fin.index(e2)]]
                    else:
                        logger.warning("unrecognized edge")

            iso = self.freeGroup.hom([self.freeGroup.hom(res)(iso(x)) for x in self.xs])
            g1=gx
        # logger.info("Ended with graph with edges (%d, %d), (%d, %d), (%d, %d)."% tuple(flatten([[e[0], e[1]] for e in g1.edges()])))
        assert g1==g2, "Did not recover correct graph"
        return iso

    def normalize_edge(self, e):
        return (e[0], e[1]) if e[0]<=e[1] else (e[1], e[0])

    def ordered_edges(self, gr):
        res = [self.normalize_edge(e) for e in gr.edges()]
        res.sort()
        return res
    
    def neighbours(self, g, v, section):
        neighbours = g.neighbors(v)
        if self.hasbasepoint:
            section2 = section + [self.basepoint]
        else:
            xmax=Util.simple_rational(max([s.real() for s in section]), 0.1)
            xmin=Util.simple_rational(min([s.real() for s in section]), 0.1)
            ymax=Util.simple_rational(max([s.imag() for s in section]), 0.1)
            section2 = section + [2*xmin-xmax+ymax*I/5]
        neighbours.sort(key=lambda v2:-arg(section2[v2] - section2[v]))
        return neighbours