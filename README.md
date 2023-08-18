# lefschetz-family


## Description
This Sage package provides a means of efficiently computing periods of complex projective hypersurfaces with certified rigorous precision bounds.
It implements the methods described in [https://arxiv.org/abs/2306.05263](https://arxiv.org/abs/2306.05263).
Here is a runtime benchmark for various examples:
| Variety (generic) 	| Time (on 4 M1 cores) 	|
|-------------------	|----------------------	|
| Elliptic curve    	| 7 seconds            	|
| Quartic curve     	| 4 minutes            	|
| Cubic surface     	| 4 minutes 20         	|
| Quartic surface   	| 1 hour (for holomorphic periods)        	|

## Requirements
Sage 9.0 and above is recommended. Furthermore, this package has the following dependencies:

- [Ore Algebra](https://github.com/mkauers/ore_algebra).
- [numperiods](https://gitlab.inria.fr/lairez/numperiods).
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
from period import LefschetzFamily
X = Hypersurface(P)
```
The period matrix of $X$ is the simply given by:
```python
X.period_matrix
```

See [the computation of the periods of the Fermat quartic surface](https://nbviewer.org/urls/gitlab.inria.fr/epichonp/eplt-support/-/raw/main/Fermat_periods.ipynb) for a usage example.


See [the computation of the periods of the Fermat quartic surface](https://nbviewer.org/urls/gitlab.inria.fr/epichonp/eplt-support/-/raw/main/Fermat_periods.ipynb) for a usage example.


### Options
The object `Hypersurface` can be called with several options:
- `method` (`"voronoi"` by default/`"delaunay"`/`"delaunay_dual"`): the method used for computing a basis of homotopy. `voronoi` uses integration along paths in the voronoi graph of the critical points; `delaunay` uses integration along paths along the delaunay triangulation of the critical points; `delaunay_dual` paths are along the segments connecting the barycenter of a triangle of the Delaunay triangulation to the middle of one of its edges. In practice, `delaunay` is more efficient for low dimension and low order varieties (such as degree 3 curves and surfaces, and degree 4 curves). This gain in performance is however hindered in higher dimensions because of the algebraic complexity of the critical points (which are defined as roots of high order polynomials, with very large integer coefficients). <b>`"delaunay"` method is not working for now</b>
- `nbits` (positive integer, `400` by default): the number of bits of precision used as input for the computations. If a computation fails to recover the integral  monodromy matrices, you should try to increase this precision. The output precision seems to be roughly linear with respect to the input precision.
- `debug` (boolean, `False` by default): whether coherence checks should be done earlier rather than late. Set to true only if the computation fails.
<!-- - `singular` (boolean, `False` by default): whether the variety is singular. <b>Not implemented yet</b> -->

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
- `thimble_extensions`: couples `(t, T)` such that `T` is the homology class in $H_n(Y)$ representing the extension of a thimble $\Delta \in H_{n-1}(X_b, X_{bb'})$ over all of $\mathbb P^1$, with $\delta\Delta =$`t`. Futhermore, the `t`s define a basis of the boundary map $\delta$. <b>(WIP)</b>
- `invariant`: the intersection of `section` with the fibre above the basepoint, as a cycle in $H_{n-2}({X_b}_{b'})$.
- `exceptional_divisors`: the exceptional cycles coming from the modification $Y\to X$, given in the basis `homology_modification`.
- `homology`: a basis of $H_n(X)$, given as its embedding in $H_2(Y)$.
- `intersection_product`: the intersection product of $H_n(X)$.
- `lift`: a map taking a linear combination of thimbles with zero boundary (i.e. an element of $\ker\left(\delta:H_n(Y, Y_b)\to H_{n-1}(Y_b)\right)$) and returning the homology class of its lift in $H_2(Y)$, in the basis `homology_modification`.
- `lift_modification`: a map taking an element of $H_n(Y)$ given by its coordinates in `homology_modification`, and returning its homology class in $H_n(X)$ in the basis `homology`.

Cohomology related properties:
- `cohomology`: a basis of $PH^n(X)$, represented by the numerators of the rational fractions.
- `picard_fuchs_equation(i)`: the picard fuchs equation of the parametrization of i-th element of `cohomology` by the fibration

Period related properties
- `period_matrix`: the period matrix of the blowup of $X$ in the aforementioned bases `homology` and `cohomology`
- `simple_periods`: the periods of the first element of `cohomology` in the basis `homology`. <b>TODO: give holomorphic periods</b>

Miscellaneous properties:
- `P`: the defining equation of $X$.
- `dim`: the dimension of $X$.
- `degree`: the degree of $X$.
- `ctx`: the options of $X$, see related section above.

### EllipticSurface

The defining equation for the elliptic surface should be given as a univariate polynomial over a trivariate polynomial ring. The coefficients should be homogeneous of degree $3$.
```python
R.<X,Y,Z> = PolynomialRing(QQ)
S.<t> = PolynomialRing(R)
P = X^2*Y+Y^2*Z+Z^2*X+t*X*Y*Z 
```
Then the following creates an object representing the hypersurface:
```python
from period import LefschetzFamily
X = EllipticSurface(P)
```

#### Options

The options are the same as those for `Hypersurface` (see above).

#### Properties

The object `ElliptcSurface` has several properties.
Fibration related properties, in positive dimension:
- `fibration`: the two linear maps defining the map $X\dashrightarrow \mathbb P^1$.
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

Cohomology related properties:
- `holomorphic_forms`: a basis of rational functions $f(t)$ such that $f(t) \operatorname{Res}\frac{\Omega_2}{P_t}\wedge\mathrm dt$ is a holomorphic form of $S$.
- `picard_fuchs_equations`: the list of the Picard-Fuchs equations of the holomorphic forms mentionned previously.

Period related properties:
- `period_matrix`: the holomorphic periods of $X$ in the bases `self.homology` and `self.holomorphic_forms`.
- `effective_periods`: the holomorphic periods $X$ in the bases `self.effective_lattice` and `self.holomorphic_forms`

Lattices. Unless stated otherwise, lattices are given the coordinates of a basis in the basis `homology`.
- `effective_lattice`: The lattice of effective cycles of $X$, consisting of the concatenation of `extensions`, `singular_components`, `fibre_class` and `section`.
- `neron_severi`: the Néron-Severi group of $X$.
- `trivial`: the trivial lattice.
- `essential_lattice`: the essential lattice.
- `mordell_weil`: the Mordell-Weil group of $X$, described as the quotient module `neron_severi/trivial`.
- `mordell_weil_lattice`: the intersection matrix of the Mordell-Weil lattice of $X$.

Miscellaneous properties:
- `dim`: the dimension of $X$.
- `ctx`: the options of $X$, see related section above.


## Contact
For any question, bug or remark, please contact [eric.pichon@polytechnique.edu](mailto:eric.pichon@polytechnique.edu).

## Roadmap
Near future milestones:
- [x] Encapsulate integration step in its own class
- [ ] Certified computation of the exceptional divisors
- [ ] Making Delaunay triangulation functional again
- [x] Saving time on differential operator by precomputing cache before parallelization

Middle term goals include:
- [ ] Having own implementation of 2D voronoi graphs/Delaunay triangulation

Long term goals include:
- [x] Computing periods of elliptic fibrations.
- [ ] Tackling higher dimensional varieties (most notably cubics in $\mathbb P^5$).
- [ ] Computing periods of singular varieties.
- [ ] Computing periods of complete intersections.
- [ ] Computing periods of weighted projective hypersurfaces, notably double covers of $\mathbb P^2$ ramified along a cubic.

Other directions include:
- [ ] Computation of homology through braid groups instead of monodromy of differential operators.


## Project status
This project is actively being developped.
