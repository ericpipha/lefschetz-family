# -*- coding: utf-8 -*-

import sage.all

from numperiods import Family
from numperiods import Cohomology
from ore_algebra import *

from sage.modules.free_module_element import vector
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ
from sage.rings.qqbar import AlgebraicField
from sage.rings.qqbar import QQbar
from sage.functions.other import ceil
from sage.functions.other import floor
from sage.functions.other import arg
from sage.functions.other import factorial
from sage.graphs.graph import Graph
from sage.symbolic.constants import I
from sage.rings.complex_double import CDF
from sage.matrix.constructor import matrix
from sage.arith.misc import xgcd
from sage.rings.integer_ring import ZZ
from sage.matrix.special import identity_matrix
from sage.matrix.special import diagonal_matrix
from sage.matrix.special import block_matrix
from sage.matrix.special import block_diagonal_matrix
from sage.matrix.special import zero_matrix
from sage.parallel.decorate import parallel
from sage.arith.misc import gcd
from sage.arith.functions import lcm
from ore_algebra.analytic.monodromy import formal_monodromy
from ore_algebra.analytic.differential_operator import DifferentialOperator

from sage.misc.prandom import randint

from edges import Edges
from Util import Util
from Context import Context

import logging
import os
import time

logger = logging.getLogger(__name__)


class Integrator(object):
    def __init__(self, path_structure, operator, nbits):
        self._operator = DifferentialOperator(operator)
        self.operator._singularities()
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

    @property
    def integrated_edges(self):
        if not hasattr(self, "_integrated_edges"):
            edges = [[self.voronoi.vertices[e[0]], self.voronoi.vertices[e[1]]] for e in self.voronoi.edges]
            N = len(edges)
            integration_result = Integrator._integrate_edge([([i,N],self.operator,[e[0], e[1]], self.nbits) for i, e in list(enumerate(edges))])
            integrated_edges= [None]*N
            # self._integration_result  = integration_result
            for [inp, _], ntm in integration_result:
                integrated_edges[inp[0][0]] = ntm # there should be a cleaner way to do this
            self._integrated_edges = integrated_edges
        return self._integrated_edges
    
    @classmethod
    @parallel
    def _integrate_edge(cls, i, L, l, nbits=300, maxtries=5, verbose=False):
        """ Returns the numerical transition matrix of L along l, adapted to computations of Voronoi. Accepts l=[]
        """
        logger.info("[%d] Starting integration along edge [%d/%d]"% (os.getpid(), i[0]+1,i[1]))
        tries = 1
        bounds_prec=256
        begin = time.time()
        while True:
            try:
                ntm = L.numerical_transition_matrix(l, eps=2**(-nbits), assume_analytic=True, bounds_prec=bounds_prec) if l!= [] else identity_matrix(L.order()) 
                ntmi = ntm**-1 # checking the matrix is precise enough to be inverted
            except Exception as e: # TODO: manage different types of exceptions
                tries+=1
                if tries<maxtries:
                    bounds_prec *=2
                    nbits*=2
                    logger.info("[%d] Precision error when integrating edge [%d/%d]. Trying again with double bounds_prec (%d) and nbits (%d)."% (os.getpid(), i[0]+1, i[1], bounds_prec, nbits))
                    continue
                else:
                    logger.info("[%d] Too many ValueErrors when integrating edge [%d/%d]. Stopping computation here"% (os.getpid(), i[0]+1, i[1]))
                    raise e
            break

        end = time.time()
        duration = end-begin
        duration_str = time.strftime("%H:%M:%S",time.gmtime(duration))
        logger.info("[%d] Finished integration along edge [%d/%d] in %s"% (os.getpid(), i[0],i[1], duration_str))

        return ntm






















