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

from sage.matrix.special import identity_matrix
from sage.parallel.decorate import parallel
from ore_algebra.analytic.differential_operator import DifferentialOperator
from ore_algebra.analytic.analytic_continuation import _process_path, Context
from ore_algebra.analytic.path import IC
from sage.misc.flatten import flatten

from sage.rings.integer_ring import Z

from .util import Util

import logging
import os
import time

logger = logging.getLogger(__name__)


class Integrator(object):
    def __init__(self, path_structure, operator, nbits):
        logger.info("Initialising operator of order %d and degree %d for integration"%(operator.order(), operator.degree()))
        begin = time.time()
        self._operator = DifferentialOperator(operator)
        self.operator._singularities()
        self.operator._singularities(IC)
        end=time.time()
        duration = end-begin
        duration_str = time.strftime("%H:%M:%S",time.gmtime(duration))
        logger.info("Operator initialised in %s"%(duration_str))
        self.nbits = nbits
        self.voronoi = path_structure

    @property
    def operator(self):
        return self._operator
    

    @property
    def transition_matrices(self):
        if not hasattr(self, "_transition_matrices"):
            transition_matrices = []
            for path in self.voronoi.pointed_loops:
                transition_matrix = 1
                N = len(path)
                for i in range(N-1):
                    e = path[i:i+2]
                    if e in self.voronoi.edges:
                        index = self.voronoi.edges.index(e)
                        transition_matrix = self.integrated_edges[index] * transition_matrix
                    else:
                        index = self.voronoi.edges.index([e[1], e[0]])
                        transition_matrix = self.integrated_edges[index]**-1 * transition_matrix
                transition_matrices += [transition_matrix]
            self._transition_matrices = transition_matrices
        return self._transition_matrices

    def find_complex_conjugates(self):
        complex_conjugates = [None]*len(self.voronoi.vertices)
        for i in range(len(self.voronoi.vertices)):
            if complex_conjugates[i]==None:
                if self.voronoi.vertices[i].conjugate() in self.voronoi.vertices:
                    complex_conjugates[i] = self.voronoi.vertices.index(self.voronoi.vertices[i].conjugate())
                    complex_conjugates[complex_conjugates[i]] = i
        return complex_conjugates
    
    def integrate_edges(self, edges):
        N = len(edges)
        logger.info("Fragmenting %d edges to integrate"% (N))
        begin = time.time()
        _fragmented_edges = self.fragment_path([([i,N], e, self.operator, self.nbits) for i, e in list(enumerate(edges))])
        fragmented_edges = [None]*len(edges)
        for [inp, _], fragments in _fragmented_edges:
            if fragments == 'NO DATA':
                raise Exception("Failed fragmentation of edge [%d/%d]."%(inp[0][0], inp[0][1]))
            fragmented_edges[inp[0][0]] = fragments
        end = time.time()
        duration = end-begin
        duration_str = time.strftime("%H:%M:%S",time.gmtime(duration))
        self._fragmented_edges = fragmented_edges
        logger.info("Fragmented edges in %s, starting integration"% (duration_str))
        
        begin = time.time()
        fragmented_edges_flat = flatten(fragmented_edges, max_level=1)
        N = len(fragmented_edges_flat)
        integration_result = self._integrate_edge([([i,N],self.operator,e, self.nbits) for i, e in list(enumerate(fragmented_edges_flat))])

        integration_result_sorted = [None] * N
        for [inp, _], ntm in integration_result:
            if ntm == 'NO DATA':
                raise Exception("Failed to integrate fragment [%d/%d] of operator. Try increasing ``nbits``."%(inp[0][0], inp[0][1]))
            integration_result_sorted[inp[0][0]] = ntm
        end = time.time()
        duration = end-begin
        duration_str = time.strftime("%H:%M:%S",time.gmtime(duration))

        logger.info("Integrated fragments in %s"% (duration_str))

        integrated_edges = []
        j=0
        for fragmented_edge in fragmented_edges:
            integrated_edges += [1]
            for i in range(len(fragmented_edge)):
                integrated_edges[-1] = integration_result_sorted[j] * integrated_edges[-1]
                j+=1
        return integrated_edges

    @property
    def integrated_edges(self):
        if not hasattr(self, "_integrated_edges"):
            complex_conjugates = self.find_complex_conjugates()
            index_of_edges_to_integrate = []
            edges_to_integrate=[]
            for i, e in enumerate(self.voronoi.edges):
                if [e[1], e[0]] not in edges_to_integrate and [complex_conjugates[e[0]], complex_conjugates[e[1]]] not in edges_to_integrate and [complex_conjugates[e[1]], complex_conjugates[e[0]]] not in edges_to_integrate:
                    index_of_edges_to_integrate+=[i]
                    edges_to_integrate+=[e]

            edges_to_integrate = [[self.voronoi.vertices[e[0]], self.voronoi.vertices[e[1]]] for e in edges_to_integrate]
            # self._edges_to_integrate = edges_to_integrate # debugging, to delete later
            N = len(edges_to_integrate)
            
            integration_result = self.integrate_edges(edges_to_integrate)

            # self._integration_result = integration_result # debugging, to delete later

            integrated_edges = [None]*len(self.voronoi.edges)
            for index, i in enumerate(index_of_edges_to_integrate):
                integrated_edges[i] = integration_result[index]
                e = self.voronoi.edges[i]
                if [complex_conjugates[e[0]], complex_conjugates[e[1]]] == e:
                    continue
                if [complex_conjugates[e[0]], complex_conjugates[e[1]]] in self.voronoi.edges:
                    j = self.voronoi.edges.index([complex_conjugates[e[0]], complex_conjugates[e[1]]])
                    integrated_edges[j] = integration_result[index].conjugate()
                if [complex_conjugates[e[1]], complex_conjugates[e[0]]] in self.voronoi.edges:
                    j = self.voronoi.edges.index([complex_conjugates[e[1]], complex_conjugates[e[0]]])
                    integrated_edges[j] = integration_result[index].inverse().conjugate()

            self._integrated_edges = integrated_edges
        return self._integrated_edges
    
    @parallel
    # @staticmethod
    def _integrate_edge(cls, i, L, l, nbits=300, maxtries=5, verbose=False):
        """ Returns the numerical transition matrix of L along l, adapted to computations of Voronoi. Accepts l=[]
        """
        logger.info("[%d] Starting integration along fragment [%d/%d]"% (os.getpid(), i[0]+1,i[1]))
        bounds_prec=256
        begin = time.time()
        eps = Z(2)**(-Z(nbits))
        
        ntm = L.numerical_transition_matrix(l, eps=eps, assume_analytic=True, bounds_prec=bounds_prec) if l!= [] else identity_matrix(L.order()) 

        end = time.time()
        duration = end-begin
        duration_str = time.strftime("%H:%M:%S",time.gmtime(duration))
        prec = str(max([c.rad() for c in  ntm.dense_coefficient_list()]))
        if len(prec)>10:
            cutoff_start = 5 if "." not in prec else prec.index(".") + 2
            cutoff_end = prec.index("e") if "e" in prec else -5
            prec = prec[:cutoff_start] + "..." + prec[cutoff_end:]
        logger.info("[%d] Finished integration along fragment [%d/%d] in %s, recovered precision %s"% (os.getpid(), i[0]+1,i[1], duration_str, prec))
        
        ntmi = ntm**-1
        return ntm
    
    @parallel
    def fragment_path(cls, indices, e, operator, nbits):
        logger.info("[%d] Fragmenting edge [%d/%d]"% (os.getpid(), indices[0]+1,indices[1]))
        begin = time.time()
        fragmented_path = []
        ctx = Context(assume_analytic=True, eps=2^-nbits)
        path = _process_path(operator, e, ctx)
        steps = list(path.steps())
        decomp = []
        i = 0
        while i < len(steps):
            if (ctx.two_point_mode
                    and steps[i].reversed and i + 1 < len(steps)
                    and not steps[i+1].reversed):
                np = 2
            else:
                np = 1
            decomp += [steps[i:i+np]]
            i += np
        for d in decomp:
            r = []
            for v in d:
                a,b = v
                if v.reversed:
                    if r==[]:
                        r = [b.value,a.value]
                    else:
                        assert r[-1] == b.value
                        r += [a.value]
                else:
                    if r==[]:
                        r = [a.value,b.value]
                    else:
                        assert r[-1] ==a.value
                        r += [b.value]
            fragmented_path += [r]
        
        end = time.time()
        duration = end-begin
        duration_str = time.strftime("%H:%M:%S",time.gmtime(duration))

        logger.info("[%d] Finished fragmentation of edge [%d/%d] in %s, split into %d fragments"% (os.getpid(), indices[0]+1,indices[1], duration_str, len(fragmented_path)))
        
        if fragmented_path[0][0] != e[0]:
            fragmented_path = [[e[0], fragmented_path[0][0]]] + fragmented_path
        if fragmented_path[-1][-1] != e[-1]:
            fragmented_path = fragmented_path + [[fragmented_path[-1][-1], e[-1]]]

        return fragmented_path