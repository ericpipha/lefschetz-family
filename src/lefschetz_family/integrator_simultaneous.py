# -*- coding: utf-8 -*-

import sage.all

from ore_algebra import *

from sage.matrix.special import identity_matrix
from sage.parallel.decorate import parallel
from ore_algebra.analytic.differential_operator import DifferentialOperator
from ore_algebra.analytic.context import Context

from sage.rings.integer_ring import Z

from .simul_integrator_function import fundamental_matrices

from .util import Util

import logging
import os
import time

logger = logging.getLogger(__name__)


class IntegratorSimultaneous(object):
    def __init__(self, path_structure, rat_coefs, gaussmanin, nbits):
        self._rat_coefs = rat_coefs
        self._gaussmanin = gaussmanin
        self.nbits = nbits
        self.voronoi = path_structure

    @property
    def gaussmanin(self):
        return self._gaussmanin
    
    @property
    def rat_coefs(self):
        return self._rat_coefs
    

    @property
    def transition_matrices(self):
        if not hasattr(self, "_transition_matrices"):
            transition_matrices = []
            for path in self.voronoi.pointed_loops:
                path = Util.simplify_path(path) # this should most likely be done in voronoi instead ?
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

    @property
    def integrated_edges(self):
        if not hasattr(self, "_integrated_edges"):
            complex_conjugates = self.find_complex_conjugates()
            index_of_edges_to_integrate = []
            edges=[]
            for i, e in enumerate(self.voronoi.edges):
                if [e[1], e[0]] not in edges and [complex_conjugates[e[0]], complex_conjugates[e[1]]] not in edges and [complex_conjugates[e[1]], complex_conjugates[e[0]]] not in edges:
                    index_of_edges_to_integrate+=[i]
                    edges+=[e]

            edges = [[self.voronoi.vertices[e[0]], self.voronoi.vertices[e[1]]] for e in edges]
            N = len(edges)
            A, denA = self._gaussmanin
            R, denR = self._rat_coefs
            integration_result = IntegratorSimultaneous._integrate_edge([([i,N],A, denA, R, denR,[e[0], e[1]], self.nbits) for i, e in list(enumerate(edges))])
            integrated_edges_temp= [None]*N

            for [inp, _], ntm in integration_result:
                if ntm == 'NO DATA': # why is this not a result of @parallel?
                    logger.warning("failed to integrate operator")
                integrated_edges_temp[inp[0][0]] = ntm # there should be a cleaner way to do this

            integrated_edges = [None]*len(self.voronoi.edges)
            for index, i in enumerate(index_of_edges_to_integrate):
                integrated_edges[i] = integrated_edges_temp[index]
                e = self.voronoi.edges[i]
                if [complex_conjugates[e[0]], complex_conjugates[e[1]]] == e:
                    continue
                if [complex_conjugates[e[0]], complex_conjugates[e[1]]] in self.voronoi.edges:
                    j = self.voronoi.edges.index([complex_conjugates[e[0]], complex_conjugates[e[1]]])
                    integrated_edges[j] = integrated_edges_temp[index].conjugate()
                if [complex_conjugates[e[1]], complex_conjugates[e[0]]] in self.voronoi.edges:
                    j = self.voronoi.edges.index([complex_conjugates[e[1]], complex_conjugates[e[0]]])
                    integrated_edges[j] = integrated_edges_temp[index].inverse().conjugate()

            self._integrated_edges = integrated_edges
        return self._integrated_edges
    
    @classmethod
    @parallel
    def _integrate_edge(cls, i, A, denA, R, denR, l, nbits=300):
        """ Returns the numerical transition matrix of L along l, adapted to computations of Voronoi. Accepts l=[]
        """
        logger.info("[%d] Starting integration along edge [%d/%d]"% (os.getpid(), i[0]+1,i[1]))
        tries = 1
        bounds_prec=256
        begin = time.time()
        eps = Z(2)**(-Z(nbits))
        ctx = Context(assume_analytic=True)
        ntm = fundamental_matrices(A, denA, R, denR, l, eps, ctx=ctx) if l!= [] else identity_matrix(A.nrows() + R.nrows()) 
        ntmi = ntm**-1 

        end = time.time()
        duration = end-begin
        duration_str = time.strftime("%H:%M:%S",time.gmtime(duration))
        logger.info("[%d] Finished integration along edge [%d/%d] in %s"% (os.getpid(), i[0]+1,i[1], duration_str))

        return ntm