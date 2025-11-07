
# `Hypersurface` documentation

This class allows to compute periods of hypersurfaces.

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
The period matrix of $X$ is then simply given by:
```python
X.period_matrix
```

The module automatically uses available cores for computing numerical integrations and braids of roots. For this, the sage session needs to be made aware of the available cores. This can be done by adding the following line of code before launching the computation (replace `10` by the number of cores you want to use).
```python
os.environ["SAGE_NUM_THREADS"] = '10'
```

See [the computation of the periods of the Fermat quartic surface](https://nbviewer.org/urls/gitlab.inria.fr/epichonp/eplt-support/-/raw/main/Fermat_periods.ipynb) for a detailed usage example.


## Copy-paste ready examples

### The Fermat elliptic curve
```python
os.environ["SAGE_NUM_THREADS"] = '10'
from lefschetz_family import Hypersurface
R.<X,Y,Z> = PolynomialRing(QQ)
P = X**3+Y**3+Z**3
X = Hypersurface(P, nbits=1500)
X.period_matrix
```
### A quartic K3 surface of Picard rank 3
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

## Options
The object `Hypersurface` can be called with several options:
- `nbits` (positive integer, `400` by default): the number of bits of precision used as input for the computations. If a computation fails to recover the integral  monodromy matrices, you should try to increase this precision. The output precision seems to be roughly linear with respect to the input precision.
- `debug` (boolean, `False` by default): whether coherence checks should be done earlier rather than late. We recommend setting to true only if the computation failed in normal mode.
- `singular` (boolean, `False` by default): whether the variety is singular. If it is (and in particular if the monodromy representation is not of Lefschetz type), the algorithm will try to desingularise the variety from the monodromy representation. This is work in progress.
- `method` (`"voronoi"` by default/`"delaunay"`/`"delaunay_dual"`): the method used for computing a basis of homotopy. `voronoi` uses integration along paths in the voronoi graph of the critical points; `delaunay` uses integration along paths along the delaunay triangulation of the critical points; `delaunay_dual` paths are along the segments connecting the barycenter of a triangle of the Delaunay triangulation to the middle of one of its edges. In practice, `delaunay` is more efficient for low dimension and low order varieties (such as degree 3 curves and surfaces, and degree 4 curves). This gain in performance is however hindered in higher dimensions because of the algebraic complexity of the critical points (which are defined as roots of high order polynomials, with very large integer coefficients). <b>`"delaunay"` method is not working for now</b>
- `fibration` (list of vectors of size `self.dim` with rational entries, randomly chosen by default): allows to pass down a choice of hyperplanes that generate the pencil of the fibration.
- `simultaenous_integration` (boolean, `True` by default): whether to integrate all periods using the differential system. It should be faster to do so in most cases. <b>There is a bug that makes the precision bounds not guaranteed using `simultaenous_integration`. It could be that the result is off by a few digits.</b>

## Properties


The object `Hypersurface` has several properties.
Fibration related properties, in positive dimension:
- `fibration`: a list of independant hyperplanes defining the iterative pencils. The first two element of the list generate the pencil used for the fibration.
- `critical_values`: the list critical values  of that map.
- `basepoint`: the basepoint of the fibration (i.e. a non critical value).
- `fibre`: the fibre above the basepoint as a `Hypersurface` object.
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
- `picard_fuchs_equation(i)`: the Picard-Fuchs equation of the parametrization of i-th element of `cohomology` by the fibration

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