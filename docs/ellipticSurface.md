
# `EllipticSurface` documentation

This class allows to compute periods and related quantities of elliptic surfaces.

## Usage

The defining equation for the elliptic surface should be given as a univariate polynomial over a trivariate polynomial ring. The coefficients should be homogeneous of degree $3$.
```python
R.<X,Y,Z> = PolynomialRing(QQ)
S.<t> = PolynomialRing(R)
P = X^2*Y+Y^2*Z+Z^2*X+t*X*Y*Z 
```
Then the following creates an object representing the surface:
```python
from lefschetz_family import EllipticSurface
X = EllipticSurface(P)
```
## Copy-paste ready examples

### New rank records for elliptic curves having rational torsion, $\mathbb Z/2\mathbb Z$
We recover the result of Section 9 of [New rank records for elliptic curves having rational torsion](https://arxiv.org/pdf/2003.00077.pdf) by Noam D. Elkies and Zev Klagsbrun.

```python
os.environ["SAGE_NUM_THREADS"] = '10'

from lefschetz_family import EllipticSurface

R.<X,Y,Z> = QQ[]
S.<t> = R[]
U.<u> = S[]

A = (u^8 - 18*u^6 + 163*u^4 - 1152*u^2 + 4096)*t^4 + (3*u^7 - 35*u^5 - 120*u^3 + 1536*u)*t^3+ (u^8 - 13*u^6 + 32*u^4 - 152*u^2 + 1536)*t^2 + (u^7 + 3*u^5 - 156*u^3 + 672*u)*t+ (3*u^6 - 33*u^4 + 112*u^2 - 80)
B1 = (u^2 + u - 8)*t + (-u + 2)
B3 = (u^2 - u - 8)*t + (u^2 + u - 10)
B5 = (u^2 - 7*u + 8)*t + (-u^2 + u + 2)
B7 = (u^2 + 5*u + 8)*t + (u^2 + 3*u + 2)
B2 = -B1(t=-t,u=-u)
B4 = -B3(t=-t,u=-u)
B6 = -B5(t=-t,u=-u)
B8 = -B7(t=-t,u=-u)

P = -Y^2*Z + X^3 + 2*A*X^2*Z + product([B1, B2, B3, B4, B5, B6, B7, B8])*X*Z^2

surface = EllipticSurface(P(5), nbits=1000)
surface.mordell_weil
```

### K3 surfaces and sphere packings
This example recovers the result of [K3 surfaces and sphere packings](https://projecteuclid.org/journals/journal-of-the-mathematical-society-of-japan/volume-60/issue-4/K3-surfaces-and-sphere-packings/10.2969/jmsj/06041083.full) by Tetsuji Shioda.

```python
os.environ["SAGE_NUM_THREADS"] = '10'
from lefschetz_family import EllipticSurface

R.<X,Y,Z> = PolynomialRing(QQ)
S.<t> = PolynomialRing(R)

# you may modify these parameters
alpha = 3
beta = 5
n = 3

P = -Z*Y**2*t^n + X**3*t^n - 3*alpha*X*Z**2*t**n + (t**(2*n) + 1 - 2*beta*t**n)*Z^3

surface = EllipticSurface(P, nbits=1500)

# this is the Mordell-Weil lattice
surface.mordell_weil_lattice

# these are the types of the singular fibres
surface.types
```


## Options

The options are the same as those for [`Hypersurface`](docs/hypersurface.md).

## Properties

The object `EllipticSurface` has several properties.
Fibration related properties, in positive dimension:
<!-- - `fibration`: the two linear maps defining the map $X\dashrightarrow \mathbb P^1$. -->
- `critical_values`: the list critical values  of that map.
- `basepoint`: the basepoint of the fibration (i.e. a non critical value).
- `fibre`: the fibre above the basepoint as a `Hypersurface` object.
- `paths`: the list of simple loops around each point of `critical_points`. When this is called, the ordering of `critical_points` changes so that the composition of these loops is the loop around infinity.
- `family`: the one parameter family corresponding to the fibration.

Homology related properties:
- `extensions`: the extensions of the fibration.
- `extensions_morsification`: the extensions of the morsification of the fibration.
- `homology`: the homology of $X$.
- `singular_components`: a list of lists of combinations of thimbles of the morsification, such that the elements of `singular_components[i]` form a basis of the singular components of the fibre above `critical_values[i]`. To get their coordinates in the basis `homology`, use `X.lift(X.singular_components[i][j])`.
- `fibre_class`: the class of the fibre in `homology`.
- `section`: the class of the zero section in `homology`.
- `intersection_product`: the intersection matrix of the surface in the basis `homology`.
- `morsify`: a map taking a combination of extensions and returning its coordinates on the basis of thimbles of the morsification.
- `lift`: a map taking a combination of thimbles of the morsification with empty boundary and returning its class in `homology`.
- `types`: `types[i]` is the type of the fibre above `critical_values[i]`.

Cohomology related properties:
- `holomorphic_forms`: a basis of rational functions $f(t)$ such that $f(t) {Res}\frac{\Omega_2}{P_t}\wedge\mathrm dt$ is a holomorphic form of $S$.
- `picard_fuchs_equations`: the list of the Picard-Fuchs equations of the holomorphic forms mentionned previously.

Period related properties:
- `period_matrix`: the holomorphic periods of $X$ in the bases `self.homology` and `self.holomorphic_forms`.
- `primary_periods`: the holomorphic periods $X$ in the bases `self.primary_lattice` and `self.holomorphic_forms`

Sublattices of homology. Unless stated otherwise, lattices are given by the coordinates of a basis of the lattice in the basis `homology`:
- `primary_lattice`: The primary lattice of $X$, consisting of the concatenation of `extensions`, `singular_components`, `fibre_class` and `section`.
- `neron_severi`: the Néron-Severi group of $X$.
- `trivial`: the trivial lattice.
- `essential_lattice`: the essential lattice.
- `mordell_weil`: the Mordell-Weil group of $X$, described as the quotient module `neron_severi/trivial`.
- `mordell_weil_lattice`: the intersection matrix of the Mordell-Weil lattice of $X$.

Miscellaneous properties:
<!-- - `dim`: the dimension of $X$. -->
- `ctx`: the options of $X$, see related section above.

