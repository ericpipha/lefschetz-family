# lefschetz-family


## Description
This Sage package provides a means of efficiently computing periods of complex projective hypersurfaces and elliptic surfaces over $\mathbb P^1$ with certified rigorous precision bounds.
It implements the methods described in [Effective homology and periods of complex projective hypersurfaces](https://doi.org/10.1090/mcom/3947) ([arxiv:2306.05263](https://arxiv.org/abs/2306.05263)).
Here is a runtime benchmark for various examples, with an input precision of 1000 bits:
| Hypersurface (generic) 	| Time (on 10 M1 cores) | Recovered precision (decimal digits)  |
|-------------------	|----------------------	| ----------------------                |
| Elliptic curve    	| 5 seconds            | 340 digits                            |
| Quartic curve     	| 90 seconds            	| 340 digits                            |
| Quintic curve     	| 5 minutes            	| 340 digits                            |
| Sextic curve      	| 30 minutes            	| 300 digits                            |
| Cubic surface     	| 40 seconds         	| 340 digits                            |
| Quartic surface   	| 1 hour        	    | 300 digits                            |
| Cubic threefold   	| 15 minutes        	    | 300 digits                            |
| Rational elliptic surface | 10 seconds        	    | 300 digits                            |
| Elliptic K3 surface   	| 30 seconds*        	    | 300 digits                            |
| Degree 2 K3 surface   	| 5 minutes        	    | 300 digits                            |


*for holomorphic periods

This package is a successor to the [numperiods](https://gitlab.inria.fr/lairez/numperiods) package by Pierre Lairez. It contains files taken from this package, that have sometimes been slightly modified to accomodate for new usage.

## How to install

In a terminal, run
```
sage -pip install git+https://github.com/mkauers/ore_algebra.git
sage -pip install lefschetz-family
```
or
```
sage -pip install --user git+https://github.com/mkauers/ore_algebra.git
sage -pip install --user lefschetz-family
```

Alternatively, install the `ore_alegbra` package (available at [https://github.com/mkauers/ore_algebra](https://github.com/mkauers/ore_algebra)), then download this repository and add the path to the main folder to your `sys.path`.

## Requirements
Sage 9.0 and above is recommended. Furthermore, this package has the following dependencies:

- [Ore Algebra](https://github.com/mkauers/ore_algebra).
- The [delaunay-triangulation](https://pypi.org/project/delaunay-triangulation/) package from PyPI.



## Usage

### Hypersurface

The first step is to define the polynomial $P$ defining the projective hypersurface $X=V(P)$. For instance, the following gives the Fermat elliptic curve:
```python
R.<X,Y,Z> = PolynomialRing(QQ)
P = X**3+Y**3+Z**3
```
Then the following creates an object representing the hypersurface:
```python
from lefschetz_family import Hypersurface
X = Hypersurface(P)
```
The period matrix of $X$ is the simply given by:
```python
X.period_matrix
```

The module automatically uses available cores for computing numerical integrations and braids of roots. For this, the sage session needs to be made aware of the available cores. This can be done by adding the following line of code before launching the computation (replace `10` by the number of cores you want to use).
```python
os.environ["SAGE_NUM_THREADS"] = '10'
```

See [the computation of the periods of the Fermat quartic surface](https://nbviewer.org/urls/gitlab.inria.fr/epichonp/eplt-support/-/raw/main/Fermat_periods.ipynb) for a detailed usage example.


#### Copy-paste ready examples

##### The Fermat elliptic curve
```python
os.environ["SAGE_NUM_THREADS"] = '10'
from lefschetz_family import Hypersurface
R.<X,Y,Z> = PolynomialRing(QQ)
P = X**3+Y**3+Z**3
X = Hypersurface(P, nbits=1500)
X.period_matrix
```
##### A quartic K3 surface of Picard rank 3
This one should take around 1 hour to compute, provided your computer has access to 10 cores.
```python
os.environ["SAGE_NUM_THREADS"] = '10'
from lefschetz_family import Hypersurface
R.<W,X,Y,Z> = PolynomialRing(QQ)
P = (2*X*Y^2*Z + 3*X^2*Z^2 + 5*X*Y*Z^2 - 2*X*Z^3 + 2*Y*Z^3 + Z^4 + X^3*W - 3*X^2*Y*W - X*Y^2*W + Y^3*W - 2*X^2*Z*W - 2*Y^2*Z*W - 2*X*Z^2*W + 2*Y*Z^2*W - X^2*W^2 - X*Y*W^2 - 2*Y^2*W^2 - 2*X*Z*W^2 + 2*Y*W^3 - W^4)*2 + X^4 - Y^4 + Z^4 - W^4
fibration = [vector(ZZ, [10, -8, -2, 7]), vector(ZZ, [1, -1, 5, 10]), vector(ZZ, [-5, 7, 7, 10])]
X = Hypersurface(P, nbits=1200, fibration=fibration)

periods = X.holomorphic_period_matrix_modification

from lefschetz_family.numperiods.integerRelations import IntegerRelations
IR = IntegerRelations(X.holomorphic_period_matrix_modification)
# this is the rank of the transcendental lattice
transcendental_rank = X.holomorphic_period_matrix_modification.nrows()-IR.basis.rank()
# The Picard rank is thus
print("Picard rank:", 22-transcendental_rank)
```

#### Options
The object `Hypersurface` can be called with several options:
- `nbits` (positive integer, `400` by default): the number of bits of precision used as input for the computations. If a computation fails to recover the integral  monodromy matrices, you should try to increase this precision. The output precision seems to be roughly linear with respect to the input precision.
- `debug` (boolean, `False` by default): whether coherence checks should be done earlier rather than late. We recommend setting to true only if the computation failed in normal mode.
- `singular` (boolean, `False` by default): whether the variety is singular. If it is (and in particular if the monodromy representation is not of Lefschetz type), the algorithm will try to desingularise the variety from the monodromy representation. This is work in progress.
- `method` (`"voronoi"` by default/`"delaunay"`/`"delaunay_dual"`): the method used for computing a basis of homotopy. `voronoi` uses integration along paths in the voronoi graph of the critical points; `delaunay` uses integration along paths along the delaunay triangulation of the critical points; `delaunay_dual` paths are along the segments connecting the barycenter of a triangle of the Delaunay triangulation to the middle of one of its edges. In practice, `delaunay` is more efficient for low dimension and low order varieties (such as degree 3 curves and surfaces, and degree 4 curves). This gain in performance is however hindered in higher dimensions because of the algebraic complexity of the critical points (which are defined as roots of high order polynomials, with very large integer coefficients). <b>`"delaunay"` method is not working for now</b>

#### Properties


The object `Hypersurface` has several properties.
Fibration related properties, in positive dimension:
- `fibration`: a list of independant hyperplanes defining the iterative pencils. The first two element of the list generate the pencil used for the fibration.
- `critical_values`: the list critical values  of that map.
- `basepoint`: the basepoint of the fibration (i.e. a non critical value).
- `fiber`: the fiber above the basepoint as a `Hypersurface` object.
- `fundamental_group`: the class computing representants of the fundamental group of $\mathbb P^1$ punctured at the critical values.
- `paths`: the list of simple loops around each point of `critical_values`. When this is called, the ordering of `critical_values` changes so that the composition of these loops is the loop around infinity.
- `family`: the one parameter family corresponding to the fibration.

Homology related properties:
- `monodromy_matrices`: the matrices of the monodromy action of `paths` on $H_{n-1}(X_b)$.
- `vanishing_cycles`: the vanshing cycles at each point of `critical_values` along `paths`.
- `thimbles`: the thimbles of $H_n(Y,Y_b)$. They are represented by a starting cycle in $H_n(Y_b)$ and a loop in $\mathbb C$ avoiding `critical_values` and pointed at `basepoint`.
- `kernel_boundary`: linear combinations of thimbles with empty boundary.
- `extensions`: integer linear combinations of thimbles with vanishing boundary.
- `infinity_loops`: extensions around the loop at infinity.
- `homology_modification`: a basis of $H_n(Y)$.
- `intersection_product_modification`: the intersection product of $H_n(Y)$.
- `fibre_class`: the class of the fibre in $H_n(Y)$.
- `section`: the class of a section in $H_n(Y)$.
- `thimble_extensions`: couples `(t, T)` such that `T` is the homology class in $H_n(Y)$ representing the extension of a thimble $\Delta \in H_{n-1}(X_b, X_{bb'})$ over all of $\mathbb P^1$, with $\delta\Delta =$`t`. Futhermore, the `t`s define a basis of the image of the boundary map $\delta$.
- `invariant`: the intersection of `section` with the fibre above the basepoint, as a cycle in $H_{n-2}({X_b}_{b'})$.
- `exceptional_divisors`: the exceptional cycles coming from the modification $Y\to X$, given in the basis `homology_modification`.
- `homology`: a basis of $H_n(X)$, given as its embedding in $H_2(Y)$.
- `intersection_product`: the intersection product of $H_n(X)$.
- `lift`: a map taking a linear combination of thimbles with zero boundary (i.e. an element of $\ker\left(\delta:H_n(Y, Y_b)\to H_{n-1}(Y_b)\right)$) and returning the homology class of its lift in $H_2(Y)$, in the basis `homology_modification`.
- `lift_modification`: a map taking an element of $H_n(Y)$ given by its coordinates in `homology_modification`, and returning its homology class in $H_n(X)$ in the basis `homology`.

Cohomology related properties:
- `cohomology`: a basis of $PH^n(X)$, represented by the numerators of the rational fractions.
- `holomorphic_forms`: the indices of the forms in `cohomology` that form a basis of holomorphic forms.
- `picard_fuchs_equation(i)`: the picard fuchs equation of the parametrization of i-th element of `cohomology` by the fibration

Period related properties
- `period_matrix`: the period matrix of $X$ in the aforementioned bases `homology` and `cohomology`, as well as the cohomology class of the linear section in even dimension
- `period_matrix_modification`: the period matrix of the modification $Y$ in the aforementioned bases `homology_modification` and `cohomology`
- `holomorphic_period_matrix`: the periods of `holomorphic_forms` in the basis `homology`.
- `holomorphic_period_matrix_modification`: the periods of the pushforwards of `holomorphic_forms` in the basis `homology_modification`. 

Miscellaneous properties:
- `P`: the defining equation of $X$.
- `dim`: the dimension of $X$.
- `degree`: the degree of $X$.
- `ctx`: the options of $X$, see related section above.

The computation of the exceptional divisors can be costly, and is not always necessary. For example, the Picard rank of a quartic surface can be recovered with `holomorphic_period_matrix_modification` alone.

### EllipticSurface

#### Usage

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
#### Copy-paste ready examples

##### New rank records for elliptic curves having rational torsion, $\mathbb Z/2\mathbb Z$
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

##### K3 surfaces and sphere packings
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
for t, _, n in surface.types:
    print(t+str(n) if t in ['I', 'I*'] else t)
```


#### Options

The options are the same as those for `Hypersurface` (see above).

#### Properties

The object `EllipticSurface` has several properties.
Fibration related properties, in positive dimension:
<!-- - `fibration`: the two linear maps defining the map $X\dashrightarrow \mathbb P^1$. -->
- `critical_values`: the list critical values  of that map.
- `basepoint`: the basepoint of the fibration (i.e. a non critical value).
- `fiber`: the fiber above the basepoint as a `LefschetzFamily` object.
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
- `types`: `types[i]` is the type of the fibre above `critical_values[i]`. It is given as a triple `t, M, nu` where `t` is the letter of the type of the fibre (`'I'`, `'II'`, etc.), `M` is the $\operatorname{SL}_2(\mathbb Z)$ matrices so that `M**(-1)*monodromy_matrices[i]*M` is the representative $M_T$ of the monodromy class (see Table 1. of the paper), and `nu` is the multiplicity of the fibre in the cases where `t` is `'I'` or `'I*'` (otherwise `nu` is `1`). 

Cohomology related properties:
- `holomorphic_forms`: a basis of rational functions $f(t)$ such that $f(t) \operatorname{Res}\frac{\Omega_2}{P_t}\wedge\mathrm dt$ is a holomorphic form of $S$.
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




### DoubleCover

#### Usage

The defining equation for the double cover should be given as a homogeneous polynomial of even degree. Such a polynomial $P$ represents the double cover $X = V(w^2-P)$.
```python
R.<X,Y,Z> = PolynomialRing(QQ)
P = X^6+Y^6+Z^6
```
Then the following creates an object representing the variety:
```python
from lefschetz_family import DoubleCover
X = DoubleCover(P)
```
#### Copy-paste ready examples

TODO

#### Options

The options are the same as those for `Hypersurface` (see above).

#### Properties

The object `DoubleCover` has several properties.
Fibration related properties, in positive dimension:
<!-- - `fibration`: the two linear maps defining the map $X\dashrightarrow \mathbb P^1$. -->
- `critical_values`: the list critical values  of that map.
- `basepoint`: the basepoint of the fibration (i.e. a non critical value).
- `fiber`: the fiber above the basepoint as a `LefschetzFamily` object.
- `paths`: the list of simple loops around each point of `critical_points`. When this is called, the ordering of `critical_points` changes so that the composition of these loops is the loop around infinity.
- `family`: the one parameter family corresponding to the fibration.

Homology related properties:
- `extensions`: the extensions of the fibration.
- `homology`: the homology of $X$.
- `fibre_class`: the class of the fibre in `homology`.
- `section`: the class of the zero section in `homology`.
- `intersection_product`: the intersection matrix of the surface in the basis `homology`.
- `lift`: a map taking a combination of thimbles of the morsification with empty boundary and returning its class in `homology`.

Cohomology related properties:
- `holomorphic_forms`: a basis of rational functions $f(t)$ such that $f(t) \operatorname{Res}\frac{\Omega_2}{P_t}\wedge\mathrm dt$ is a holomorphic form of $S$.

Period related properties:
- `period_matrix`: the holomorphic periods of $X$ in the bases `self.homology` and `self.holomorphic_forms`.
- `effective_periods`: the holomorphic periods $X$ in the bases `self.effective_lattice` and `self.holomorphic_forms`

Sublattices of homology. Unless stated otherwise, lattices are given by the coordinates of a basis of the lattice in the basis `homology`:
- `primary_lattice`: The lattice of effective cycles of $X$, consisting of the concatenation of `extensions`, `singular_components`, `fibre_class` and `section`.

Miscellaneous properties:
- `P`: the defining equation of $X$.
- `dim`: the dimension of $X$.
- `degree`: the degree of $P$.
- `ctx`: the options of $X$, see related section above.


## Contact
For any question, bug or remark, please contact [eric.pichon-pharabod@inria.fr](mailto:eric.pichon-pharabod@inria.fr).

## Roadmap
Near future milestones:
- [x] Encapsulate integration step in its own class
- [x] Certified computation of the exceptional divisors
- [x] Saving time on differential operator by precomputing cache before parallelization
- [x] Computing periods of elliptic fibrations.
- [x] Removing dependency on `numperiods`.

Middle term goals include:
- [ ] Making Delaunay triangulation functional again
- [ ] Having own implementation of 2D voronoi graphs/Delaunay triangulation

Long term goals include:
- [x] Tackling cubic threefolds.
- [x] Generic code for all dimensions.
- [x] Computing periods of K3 surfaces with mildy singular quartic models.
- [ ] Dealing with other singularities, especially curves.
- [ ] Computing periods of complete intersections.
- [x] Computing periods of weighted projective hypersurfaces, notably double covers of $\mathbb P^2$ ramified along a sextic.

Other directions include:
- [ ] Computation of homology through braid groups instead of monodromy of differential operators.


## Project status
This project is actively being developped.
