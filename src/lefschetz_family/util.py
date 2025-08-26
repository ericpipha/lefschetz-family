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

import sage.all

from ore_algebra import *
from sage.rings.complex_mpfr import ComplexField
from sage.functions.other import floor
from sage.arith.misc import gcd
from sage.arith.misc import xgcd
from sage.combinat.integer_vector import IntegerVectors
from sage.matrix.constructor import matrix
from sage.matrix.special import block_matrix
from sage.matrix.special import identity_matrix
from sage.modules.free_module_element import vector
from sage.rings.integer_ring import ZZ

from sage.misc.prandom import randint, shuffle

from .numperiods.integerRelations import IntegerRelations

import logging

logger = logging.getLogger(__name__)


def lazy_attribute(func):
    """
    A decorator that converts a method into a lazy attribute.
    
    The method is called only once, the first time the attribute is accessed.
    The result is cached and returned on subsequent accesses.
    
    This replaces the common pattern:
        @property
        def attr(self):
            if not hasattr(self, '_attr'):
                self._attr = compute_value()
            return self._attr
    
    With the simpler:
        @lazy_attribute
        def attr(self):
            return compute_value()
    """
    attr_name = f'_{func.__name__}'
    
    def wrapper(self):
        if not hasattr(self, attr_name):
            setattr(self, attr_name, func(self))
        return getattr(self, attr_name)
    
    # Copy over the function's metadata
    wrapper.__name__ = func.__name__
    wrapper.__doc__ = func.__doc__
    wrapper.__module__ = func.__module__
    
    return property(wrapper)


class Util(object):

    @staticmethod 
    def simple_rational(p, r):
        """Gives a rational q such that |p-q|<=r"""
        x=p
        l=[floor(x)]
        while abs(p-Util.evaluate_continued_fraction(l))>r:
            x=1/(x-l[-1])
            try:
                l+=[ZZ(x)]
            except:
                l+=[ZZ(floor(x))]
        return Util.evaluate_continued_fraction(l)
    
    @staticmethod
    def evaluate_continued_fraction(l):
        """ Given a list l, evaluates the continued fraction l[0] + 1/(l[1] + 1/(l[2] + ...))"""
        p=l[-1]
        l=l[:-1]
        while len(l)>0:
            p= l[-1] +1/p
            l=l[:-1]
        return p

    @staticmethod
    def invert_permutation(l):
        """Given a list representing a permutation of [0, ..., len(l)-1], l[i] = j, returns the inverse permutation l2[j] = i"""
        return [l.index(x) for x in range(len(l))]

    @staticmethod
    def simplify_path(p):
        """Given a list of numbers p, returns a ``simplification'' of p, removing all the backtracking
        
        For example, `simplify_path([1,2,3,2,1,4,5,1]) == [1,4,5,1]`
        """
        i=1
        res = list(p)
        while i<len(res)-1:
            p = res[i-1]
            a = res[i]
            n = res[i+1] 
            if p==a:
                res = res[:i]+res[i+1:]
                if i!=1:
                    i=i-1
            elif p==n:
                res = res[:i]+res[i+2:]
                if i!=1:
                    i=i-1
            else:
                i=i+1
        return res

    @staticmethod
    def monomials(ring, degree):
        """Given a polynomial ring and an integer d, returns all the monomials of the ring with degree d."""
        return [ring.monomial(*m) for m in list(IntegerVectors(degree, ring.ngens()))]

    @staticmethod
    def xgcd_list(l):
        """Given a list of integers l, return a double consisting of the gcd of these numbers and the coefficients of a Bezout relation."""
        if len(l)==0:
            return 0, []
        if len(l)==1:
            return l[0], [1]
        d = gcd(l)
        result = [1]
        a = l[0]
        for i in range(len(l)-1):
            b = l[i+1]
            d2, u, v = xgcd(a,b)
            result = [k*u for k in result] + [v]
            a=d2
        assert d2==d, "not getting the correct gcd"
        return d2, result


    @staticmethod
    def path(path, x):
        """Given a list of complex numbers path, and a number 0<x<1, return the path(x) where path is seen as a path [0,1]\\to C."""
        CC=ComplexField(500)
        dtot = sum([CC(abs(p1-p2)) for (p1,p2) in zip(path[:-1], path[1:])])
        dmin, dmax = 0, CC(abs(path[0]-path[1]))
        for i in range(len(path)-1):
            if x*dtot<=dmax and x*dtot>=dmin:
                break;
            else:
                dmin, dmax=dmax, dmax+CC(abs(path[i+1]-path[i+2]))
        t = Util.simple_rational((x*dtot -dmin)/(dmax-dmin), 10e-10)
        return (1-t)*path[i] + t*path[i+1]



    @staticmethod
    def select_closest(l, e):
        """Given a list of complex numbers l and a complex number e, return the element e2 of l minimizing abs(e2-e)"""
        # find element in l that is closest to e for abs
        CC=ComplexField(500)
        r = l[0]
        for i in range(1,len(l)):
            if abs(CC(l[i]-e))<abs(CC(r-e)):
                r = l[i]
        return r

    @staticmethod
    def select_closest_index(l, e):
        """Given a list of complex numbers l and a complex number e, return the index i minimizing abs(l[i]-e)"""
        # find index of element in l that is closest to e for abs
        CC=ComplexField(500)
        r = 0
        for i in range(1,len(l)):
            if abs(CC(l[i]-e))<abs(CC(l[r]-e)):
                r = i
        return r

    @staticmethod
    def is_clockwise(l):
        """Given a list of complex numbers describing a convex polygon, return whether the points are clockwise."""
        CC=ComplexField(500)
        smally = min(l, key=lambda v:(CC(v).imag(), CC(v).real()))
        i = l.index(smally)
        n = l[i+1 if i+1<len(l) else 0]
        p = l[i-1]

        x1,x2,x3 = [v.real() for v in [p,smally,n]]
        y1,y2,y3 = [v.imag() for v in [p,smally,n]]

        M = matrix([[1,x1,y1],[1,x2,y2],[1,x3,y3]])
        if abs(CC(M.determinant()))<10e-7:
            logger.info("cross product is very small, not certain about orientation")
        
        return CC(M.determinant())<0

    @staticmethod
    def is_simple(l):
        """Given a list of words l, return whether every word in the list consists of a single letter."""
        for w in l:
            if len(w.syllables()) != 1:
                return False
        return True
    
    @staticmethod
    def letter(w, i):
        """Given a word w and an integer i, yields the i-th letter of w."""
        return w.syllables()[i][0]**(w.syllables()[i][1]/abs(w.syllables()[i][1]))

    @staticmethod
    def compatibility(t1, t2, phi):
        w1, w2 = phi(t1), phi(t2)
        res = []
        if Util.letter(w1, 0) == Util.letter(w2, 0):
            res += [t2**-1*t1]
        if Util.letter(w1, -1) == Util.letter(w2, 0)**-1:
            res += [t1*t2]
        if Util.letter(w1, 0) == Util.letter(w2, -1)**-1:
            res += [t2*t1]
        if Util.letter(w1, -1) == Util.letter(w2, -1):
            res += [t2*t1**-1]
        return res
    
    @staticmethod
    def easy_simplifications(phi, ts=None):
        if ts == None:
            ts = list(phi.domain().gens())
        while not Util.is_simple([phi(t) for t in ts]):
            managed = False
            for i, t in enumerate(ts): 
                others = [t for j,t in enumerate(ts) if i != j]
                while len(phi(t).syllables())!=1:
                    options = [t*t2 for t2 in others if Util.letter(phi(t2),0) == Util.letter(phi(t),-1)**-1]
                    options += [t*t2**-1 for t2 in others if Util.letter(phi(t2**-1),0) == Util.letter(phi(t),-1)**-1]
                    options += [t2*t for t2 in others if Util.letter(phi(t2),-1) == Util.letter(phi(t),0)**-1]
                    options += [t2**-1*t for t2 in others if Util.letter(phi(t2**-1),-1) == Util.letter(phi(t),0)**-1]
                    if len(options)==0:
                        break
                    options = [o for o in options if phi(o)!=phi(1)]
                    options.sort(key = lambda w: len(phi(w).syllables()))

                    if len(phi(options[0]).syllables())< len(phi(t).syllables()):
                        t=options[0]
                        managed=True
                    else:
                        break
                ts[i] = t
            if not managed:
                break
        return ts

    @staticmethod
    def lettersof(w):
        letters = []
        for x, n in w.syllables():
            if x not in letters:
                letters += [x]
        return letters
    
    @staticmethod
    def number_of_occurences(w, x):
        res = 0
        for x2,n in w.syllables():
            if x2 == x:
                res += abs(n)
        return res
    
    @staticmethod
    def invert_morphism(phi):
        """Given an invertible free group morphism phi, computes its inverse. 
        Optionally, you can give generators ts of a subgroup (as a list of words) to compute the inverse of the restriction of phi on \\langle ts \\rangle (assuming it is invertible)."""
        singlets = []
        ts = Util.easy_simplifications(phi)
        xs = list(phi.codomain().gens())
        xs.sort(key = lambda x: len([t for t in ts if x in Util.lettersof(phi(t))]))
        replace = [1]
        while replace != []:
            done_something = False
            for x in xs:
                replace = []
                tsx = [t for t in ts if x in Util.lettersof(phi(t))]
                tsx.sort(key = lambda t: Util.number_of_occurences(phi(t), x))
                for t in tsx[1:]:
                    for newt in Util.compatibility(tsx[0], t, phi):
                        if Util.number_of_occurences(phi(newt), x) < Util.number_of_occurences(phi(t), x):
                            replace += [[t, newt]]
                            done_something = True
                            break
                if done_something:
                    break

            for i, t in enumerate(ts):
                for t2, newt in replace:
                    if t==t2:
                        ts[i]=newt
            for x in xs:
                tsx = [t for t in ts if x in Util.lettersof(phi(t))]
                if len(tsx) == 1:
                    singlets += [ts.pop(ts.index(tsx[0]))]
            xs.sort(key=lambda x: len([t for t in ts if x in Util.lettersof(phi(t))]))
        assert len(ts) == 0, "did not manage inversion"
        res = Util.easy_simplifications(phi, list(reversed(singlets)))

        tfin = [None]*len(res)
        for t in res:
            x, power = phi(t).syllables()[0]
            tfin[phi.codomain().gens().index(x)] = t**power
        return  phi.codomain().hom(tfin)


    @staticmethod
    def find_complement( B, primitive=True):
        """Given an m x n integer valued matrix B with n>m, computes an (n-m) x n matrix A such that the matrix block_matrix([[A],[B]]) is invertible over the integers"""
        D, U, V = B.smith_form()
        quotient = identity_matrix(D.ncols())[D.nrows():] * V.inverse()
        if primitive:
            assert block_matrix([[B],[quotient]]).det() in [-1,1], "cannot find complement, are you sure sublattice is primitive?"
        return quotient
    
    @staticmethod
    def middle(w):
        """Given a word w of odd length 2n+1, yields the word consisting of the first n letters of w."""
        syls = w.syllables()
        syls = syls[:len(syls)//2]
        conj = w.parent(1)
        for l, p in syls:
            conj = conj*l**p
        return conj
    
    @staticmethod
    def remove_duplicates(l):
        l2 = []
        for e in l:
            if e not in l2:
                l2 += [e]
        return l2
    
    @staticmethod
    def get_coefficient(c, values, symbols):
        relations = IntegerRelations(matrix([c] + values).transpose()).basis
        assert relations.nrows()>=1, "could not identify coefficients"
        relation = relations[0]
        return -vector(relation[1:])*vector(symbols)/relation[0]
    
    @staticmethod
    def rationalize(c):
        return Util.get_coefficient(c,[1],[1])

    @staticmethod
    def saturate(Ms):
        dim = Ms[0].nrows()
        span = identity_matrix(dim).image()
        fam = identity_matrix(dim).rows()
        new = True
        while new:
            new=False
            for v in span.span(fam).basis():
                for M in Ms:
                    if M*v not in span.span(fam):
                        new = True
                        fam += [M*v]
        CB = span.span(fam).basis_matrix().transpose()
        return CB
    
    @staticmethod
    def check_if_algebraic(c, order=10):
        try:
            return IntegerRelations(matrix([c**i for i in range(order+1)]).transpose()).basis.row(0)
        except:
            raise NotImplementedError("Non-algebraic number")
        
    @staticmethod
    def flatten_matrix_of_matrices(M):
        res = [[0 for i in range(M.nrows())] for j in range(M.ncols())]
        for i in range(M.nrows()):
            for j in range(M.ncols()):
                res[i][j] = M[i,j]
        return block_matrix(res)