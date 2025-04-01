# -*- coding: utf-8 -*-

# AUTHORS:
#   - Pierre Lairez (2019): initial implementation


from sage.rings.all import *
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.modules.free_module_element import vector
from sage.matrix.constructor import Matrix
from sage.rings.polynomial.polynomial_ring import *

from ..exceptions import NotSmoothError

class Cohomology(object):
    def __init__(self, f, shift=0, basisfor = None):
        """f, a homogeneous polynomial defining a smooth hypersurface in P^n.

        This class aims at computing in the n-th algebraic de Rham cohomology
        space of P^n - V(f), denoted H^n. Elements of H^n are represented as
        polynomials. A homogeneous polynomial p of degree s*deg(f)-n-1
        represents the differential form [p] = (s-1)! * p dx0...dxn / f^s (that is a
        degree 0 (n+1)-form on A^(n+1)-V(f) which induces a n-form on P^n-V(f).
        """

        assert f.is_homogeneous()

        self.nvars = f.parent().ngens()
        self.dim = self.nvars-2
        self.degree = f.degree()
        self.pol = f
        self.shift = shift
        self.R = f.parent()  # Variables x0...xn
        # Variables T x0...xn _x0..._xn
        self._R = PolynomialRing(f.parent().base_ring(), 2*self.nvars+1, ['T'] + [str(v) for v in self.R.gens()] + ['X'+str(v) for v in self.R.gens()], order='degrevlex')
        self._Tvar = self._R.gen(0)
        self._vars = [self._R.gen(i) for i in range(1, self.nvars+1)]
        self._xvars = {self._R.gen(i): self._R.gen(self.nvars+i) for i in range(1, self.nvars+1)}
        self._conv = self.R.hom([self._R.gen(i+1) for i in range(self.nvars)])
        self._iconv = self._R.hom([1] + list(self.R.gens()) + [0 for i in range(self.nvars)])
        self._pol = self._conv(f)

        self._jac = ideal([self._Tvar*self._pol.derivative(v) - self._xvars[v] for v in self._vars] + [v1*v2 for v1 in self._xvars.values() for v2 in self._xvars.values()])


            # We could do the computation in R in a simpler way, but doing it in _R ensures consistency.
        jac = self._pol.jacobian_ideal() + ideal(self._Tvar) + ideal(list(self._xvars.values()))
        if basisfor is None:
            if not f.jacobian_ideal().dimension() == 0:
                raise NotSmoothError()
            self.__basis = sorted([p*self._Tvar for p in jac.normal_basis() if (p.degree() + self.nvars + self.shift) % self.degree == 0])
            self._basis = [self._iconv(p) for p in self.__basis]
            self._basis_indices = {elt: idx for idx, elt in enumerate(self._basis)}
        else:
            f, g = basisfor
            _f = self._conv(f)


    def basis(self):
        """Return a basis of the n-th algebraic de Rham cohomology space of P^n - V(f).
        """
        return self._basis

    def holomorphic_forms(self):
        return [b for b in self._basis if b.degree() + self.dim + 2 + self.shift == self.degree]

    def index_of_basis_elt(self, b):
        return self._basis_indices[b]

    # TODO Add a function for simulatenous reduction
    def _red(self, p):
        redp = self._jac.reduce(p)
        if redp == p:
            return p
        else:
            c0 = redp.coefficient({self._Tvar:1})
            c1 = sum([redp.coefficient({self._xvars[v]:1}).derivative(v) for v in self._vars])
            return self._Tvar*c0 + self._red(self._Tvar*c1)

    def red(self, p):
        """Return the canonical form of p in H^n"""
        return self._iconv(self._red(self._Tvar*self._conv(p)))

    def _integrate(self, p):
        if p==0:
            return []
        else:
            redp = self._jac.reduce(p)
            c0 = redp.coefficient({self._Tvar:1})
            coefs = [redp.coefficient({self._xvars[v]:1}) for v in self._vars]
            c1 = sum([redp.coefficient({self._xvars[v]:1}).derivative(v) for v in self._vars])
            assert c0==0
            return [coefs] + self._integrate(self._Tvar*c1)

    def integrate(self, p):
        """Return w in H^n such that p = dw"""
        return [[self._iconv(v) for v in l] for l in self._integrate(self._Tvar*self._conv(p))]

    def _coordinates(self, p):
        red = self._red(p)
        return vector(red.monomial_coefficient(m) for m in self.__basis)

    def coordinates(self, p):
        """Return the coordinates of the canonical form of p in H^n, in the basis self.basis()."""
        return self._coordinates(self._red(self._Tvar*self._conv(p)))

    def multmat(self, p):
        conv = self._conv(p)
        return Matrix([ self._coordinates(self._red(conv*b)) for b in self.__basis ])


    def weight(self, b):
        deg = b.degree() + self.dim + 2 + self.shift
        assert deg % self.degree == 0
        return deg / self.degree

