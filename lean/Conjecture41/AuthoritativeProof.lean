import Conjecture41.Definitions

/-!
# Authoritative proof and audit for Cohn--Rajagopal Conjecture 4.1

This Lean source file is the authoritative human proof specification for the
project.  It is intentionally stored as a `.lean` file so that Aristotle sees
the entire mathematical theory even if Markdown and text files are omitted by
project ingestion.

The source statement is Conjecture 4.1 in Henry Cohn and Isaac Rajagopal,
"Variations on five-dimensional sphere packings", arXiv:2412.00937v3,
Section 4.1.  Equal colors require distance at least `sqrt 2`, adjacent colors
at least `sqrt 5 / 2`, and opposite colors at least `1`.  The desired radial
upper density is `1`.

## Formal completion status

The local algebra, the cotangent global sum, the plane-to-periodic reduction,
the limsup equivalence, and the geometric realization of a genuine periodic
triangulation are kernel-checked in this project.  In particular, the project
constructs an actual lattice-equivariant weak Delaunay triangulation of every
nonempty square-periodic point set and derives its quotient area partition and
the identity `F = 2 V`; these facts are not inserted as assumptions.

The `TorusTriangulation` structure is a compact numerical certificate
used by the already-proved cotangent summation.  It is not by itself a full
definition of a geometric triangulation: its translation vectors are not
typed as lattice vectors and its coverage, face-to-face, vertex-orbit, and
disjoint-interior properties are not fields.  Accordingly, the completed
development first constructs a semantically faithful periodic Delaunay tiling,
proves all those properties, and only then packages it as
`TorusTriangulation`.  Thus the numerical record is used only as a derived
interface for the global sum, never as an independent existence hypothesis.

## 0. Exact statement and scope

Let `C` be a set of colored points in the Euclidean plane, with colors in
`ZMod 4`.  For distinct points `p,q`, validity says

```
exclusionSq (color p) (color q) <= dist p q ^ 2,
```

where the squared thresholds are

```
same color       : 2
adjacent colors  : 5/4
opposite colors  : 1.
```

The published assertion is

```
limsup_{r -> infinity} #(C inter closedBall(0,r)) / (pi*r^2) <= 1.
```

The Lean target is the equivalent epsilon/eventual form

```
forall eps > 0, exists R >= 1, forall r >= R,
  countInClosedBall C r <= (1+eps)*pi*r^2.
```

The Lean class also permits finite configurations.  This harmlessly
strengthens the source statement: finite configurations have density zero.
The result proves the `D5` density bound only inside the `D3`-fibered
four-coset construction; it does not prove unrestricted global optimality of
`D5` among all five-dimensional packings.

## 1. Separation and local finiteness

Every exclusion weight lies in `[1,2]`.  Thus validity implies

```
1 <= dist(p,q)^2,
```

and hence `dist(p,q) >= 1` for distinct points.  Open balls of radius `1/2`
around configuration points have disjoint interiors.  A compact set is
totally bounded, so a finite `1/3`-net contains at most one configuration point
over each net ball.  Therefore every bounded closed ball contains finitely
many points.  This is proved by `uniformlySeparated` and
`finiteInClosedBall`; the count never uses a zero-for-infinite convention.

## 2. Complete color classification for a triangle

For a triangle with vertex colors `i,j,k`, order the edge weights opposite the
three vertices as

```
(wa,wb,wc) = (w(j,k), w(i,k), w(i,j)).
```

The `4^3 = 64` ordered color triples give exactly the following four
unordered types:

```
(2,2,2), (2,5/4,5/4), (2,1,1), (5/4,5/4,1).
```

Indeed: all colors equal gives the first; exactly two equal gives the second
or third according as the remaining color is adjacent or opposite; and three
distinct colors contain exactly one opposite pair and two adjacent pairs.
Including permutations, there are exactly ten ordered weight triples.  This is
proved by `weightTriple_exclusionSq` and `color_distinct_cases`.

## 3. Marked triangle inequality, with every factor checked

Let a positively oriented nondegenerate triangle have angles `A,B,C`, area
`K>0`, and squared opposite side lengths

```
x = |BC|^2, y = |CA|^2, z = |AB|^2.
```

Define

```
H = 2xy+2yz+2zx-x^2-y^2-z^2.
```

Writing `u=B-A` and `v=C-A`, the cosine law and the Gram determinant give

```
H = 4*(|u|^2*|v|^2-(u dot v)^2) = 16*K^2 = (4*K)^2.
```

Consequently

```
cot A = (y+z-x)/(4*K),
cot B = (z+x-y)/(4*K),
cot C = (x+y-z)/(4*K).
```

For weights `(wa,wb,wc)`, put

```
N = wa*(y+z-x)+wb*(z+x-y)+wc*(x+y-z).
```

Then the marked cotangent sum is exactly `N/(4*K)`.

### 3.1 The sign cannot be omitted

As a linear form in the squared side lengths,

```
N = (-wa+wb+wc)*x + (wa-wb+wc)*y + (wa+wb-wc)*z.
```

For the four canonical patterns, these coefficient triples are

```
(2,2,2)       -> (2,2,2)
(2,5/4,5/4)   -> (1/2,2,2)
(2,1,1)       -> (0,2,2)
(5/4,5/4,1)   -> (1,1,3/2).
```

Thus `N >= 0` (in fact `N>0` for a nondegenerate triangle).  This separate
sign proof is essential: a squared inequality alone controls only `|N|`.

### 3.2 Exact SOS certificates

Direct polynomial expansion gives

```
(2,2,2):
N^2-4H = 8*(x^2+y^2+z^2).

(2,5/4,5/4):
N^2-4H = 4*(y+z-3*x/4)^2 + 2*x^2 + 4*(y-z)^2.

(2,1,1):
N^2-4H = 4*(x-y-z)^2 + 4*(y-z)^2.

(5/4,5/4,1):
N^2-4H = (x+y-5*z/2)^2 + 4*(x-y)^2.
```

All permutations are proved in `ColoredTriangle.lean`.  Therefore
`N^2 >= 4H = (8K)^2`.  Combining this with `N>=0` yields `N>=8K`, and division
by `4K>0` proves

```
wa*cot A + wb*cot B + wc*cot C >= 2.                 (MT)
```

The equality statement must be scale-correct.  Equality occurs only in the
following similarity families for the displayed canonical orderings

```
(x,y,z)=(2t,t,t), t>0,
(x,y,z)=(5t/4,5t/4,t), t>0.
```

All other ordered cases are simultaneous permutations of the weights and of
`x,y,z`.
Their areas are `t/2`.  Validity forces `t>=1`; only the minimally scaled
representatives `t=1` are the two Cohn--Rajagopal area-`1/2` triangles.  Earlier
project text incorrectly said equality itself forced area `1/2`; that wording
has been corrected here.

## 4. The precise periodic Delaunay realization theorem

Only square periods are required for the final reduction.  Let `L>0`, let `S`
be a nonempty finite colored set of representatives, and let

```
X = {s + L*(m,n) : s in S, (m,n) in Z^2}.
```

Assume the whole lift is valid.  The required geometric theorem is:

> `X` has an `L*Z^2`-equivariant face-to-face straight-line weak Delaunay
> triangulation.  Its quotient on the flat square torus uses exactly the
> `|S|` point orbits as vertices, every dart is paired with the reverse dart of
> the same geometric edge by a lattice translation, the sum of representative
> face areas is `L^2`, and the numbers of faces and vertices satisfy `F=2|S|`.

Here is a complete classical construction, broken into the facts that must
become Lean declarations.

### 4.1 `X` is a Delone set

Separation follows from validity and Section 1.  For relative density, fix
`s0 in S`.  Given `z in R^2`, choose integers `m,n` by rounding each coordinate
of `(z-s0)/L`.  Then

```
dist(z, s0+L*(m,n)) <= L/sqrt(2).
```

Thus `X` is uniformly discrete, locally finite, and relatively dense with an
explicit covering radius `R=L/sqrt(2)`.

### 4.2 Periodic Voronoi polygons

For `x in X`, define

```
V_x = {z : dist(z,x) <= dist(z,y) for every y in X}.
```

Each comparison is a closed affine half-plane, so `V_x` is closed and convex.
Separation gives it nonempty interior.

The finite-half-plane argument needs an explicit bounding subset; boundedness
of the full infinite intersection alone would not suffice.  The four sites

```
x+L*e1, x-L*e1, x+L*e2, x-L*e2
```

belong to `X`.  Their four comparison half-planes are exactly the coordinate
bounds cutting out

```
Q_x = x + [-L/2,L/2]^2.
```

Hence `V_x` is contained in `Q_x`, and `Q_x` is contained in
`closedBall(x,R)` for `R=L/sqrt(2)`.  The four bounding sites themselves lie
within distance `2R` of `x`.  Now let `Y_x` be the sites within distance `2R`
of `x`; this set is finite by local finiteness.  Any point satisfying the
half-plane constraints from `Y_x` already lies in `Q_x`.  If
`dist(x,y)>2R`, the triangle inequality then gives

```
dist(z,y) > R >= dist(z,x),
```

so every farther constraint is redundant.  Thus `V_x` is exactly a bounded
finite intersection of closed affine half-planes, hence a compact convex
polygon.

Nearest sites exist, so the polygons cover the plane; their interiors are
disjoint.  Translation by a lattice vector sends `V_x` to
`V_(x+lambda)`.  If a cell meets a fixed compact set, its site is within
distance `R` of that set; bounded-set finiteness of `X` therefore proves local
finiteness of the family of cells.

### 4.3 Dual Delaunay polygonal tiling

For every Voronoi vertex `v`, let

```
A_v = {x in X : v in V_x}.
```

All elements of `A_v` lie on the circle centered at `v` of radius
`dist(v,x)`, and its open disc contains no point of `X`.  Local finiteness
makes `A_v` finite.  At least three cells meet at a Voronoi vertex, and distinct
points on a circle are vertices of their convex hull, so

```
D_v = convexHull(A_v)
```

is a nondegenerate convex cyclic polygon.

The standard planar Voronoi--Delaunay duality proof now applies: Voronoi edges
correspond to edges shared by two polygons `D_v`; cyclic order around every
site agrees with the order of vertices of its Voronoi polygon; these polygons
have disjoint interiors and cover the plane.  One direct verification is to
use the lifting map `x |-> (x,|x|^2)`: an empty circle with center `v` is exactly
a lower supporting plane of the lifted set, and the projections of all lower
faces form a face-to-face subdivision of the whole plane because `X` is
relatively dense.  This also proves that no polygon or face is omitted.  The
construction commutes with every lattice translation.

The Delaunay subdivision is locally finite, and this fact must not be left
implicit.  At a Voronoi vertex `v`, relative density shows that its nearest-site
(empty-circle) radius is at most `R`; hence `D_v` is contained in
`closedBall(v,R)`.  The vertices of a locally finite polygonal Voronoi tiling
are locally finite: a compact set meets only finitely many Voronoi cells, each
with finitely many vertices.  If `D_v` meets a compact `K`, then
`v` lies in the compact `R`-neighborhood of `K`, so only finitely many such
`v` and Delaunay cells exist.  This proves local finiteness and, after taking a
compact fundamental square, finiteness of the cell and face orbits.

This duality/subdivision theorem must be formalized; citing the words
"Delaunay triangulation" without proving or importing the theorem does not
close the project.

### 4.4 Cocircular cells: equivariant triangulation without perturbing sites

If `|A_v|=3`, keep `D_v` as a triangle.  If more sites are cocircular,
triangulate the bounded convex polygon `D_v`.  The correct equivariance
argument is by **cell orbits**, not by an orbit-constant perturbation of the
sites.  A bounded polygon has no nonzero translational stabilizer.  Therefore
choose one representative of each lattice orbit of Delaunay polygons, choose
any boundary vertex of that representative, triangulate it by a fan, and
translate that fan to the other cells in its orbit.  The choice is consistent.

Every inserted diagonal lies inside one cocircular polygon.  The two opposite
vertices are on the same empty circle, so the relevant in-circle determinant
is exactly zero.  Original polygon edges have the usual empty-circle
inequality.  Hence every paired edge in the resulting triangulation is weak
Delaunay.  An earlier blueprint suggested an orbit-constant symbolic
perturbation; that is not reliable (for example, a one-site square lattice has
only one site orbit and such a perturbation cannot choose a diagonal).  The
cell-orbit fan construction is the authoritative method.

### 4.5 Finite quotient, lattice dart pairing, area, and `F=2V`

By the local-finiteness argument in Section 4.3 and periodicity, the tiling has
finitely many face orbits.
Choose one representative from each orbit (for example, by putting its
barycenter in a half-open fundamental square).  Pair each oriented face-edge
dart with the reverse dart of the unique adjacent translated face.  The
translation is an actual vector `L*(m,n)`, the pairing is a fixed-point-free
involution, and the lifted coloring is invariant under it.  Quotient loops and
multiple edges are allowed by the final numerical certificate.  For the proof
of Euler and area one may either formalize the resulting finite torus
`Delta`-complex directly, or pass to a sufficiently large finite-index
sublattice so that the quotient is an honest simplicial triangulation.  In the
second route one must prove injectivity on every simplex and the scaling
identities

```
V_k = k^2*V,  F_k = k^2*F,  A_k = k^2*L^2.
```

It is not acceptable merely to assert that a cover repairs the quotient.

The vertex set of the triangulation is exactly `X`; this also needs a proof.
For each `x in X`, the cell `V_x` contains an open radius-`1/2` ball and is a
bounded finite polygon, so it has a Voronoi vertex `v`.  Then `x in A_v`.
Every distinct point of the cyclic set `A_v` is an extreme point of its convex
hull, hence `x` is a vertex of `D_v`, and the fan triangulation retains every
polygon vertex.  Conversely all Delaunay and fan vertices belong to `X` by
construction.

It follows that there is exactly one vertex orbit for every member of `S`:
every point of `X` has a representative in `S`, while validity and injectivity
of `latticeVec` forbid two distinct representatives from differing by a
lattice vector.

For the area identity, let `Q` be a half-open fundamental square.  The
translated triangles tile the plane with disjoint interiors.  For a bounded
face `T`, the sets `T intersect (Q-lambda)` partition `T` up to boundaries,
so translation invariance and finite additivity give

```
sum_lambda area((T+lambda) intersect Q) = area(T).
```

Summing over the finitely many face orbits and using that their translates
partition `Q` yields

```
sum_representative_faces area(T) = area(Q) = L^2.
```

The quotient is a finite triangular CW decomposition of the flat torus.  Each
face has three darts and every edge has two, so `3F=2E`.  Euler characteristic
of the torus gives `V-E+F=0`; therefore `F=2V`.  Equivalently, one may sum face
angles: faces contribute `pi*F`, while the full angle around each vertex orbit
is `2*pi`, giving `pi*F=2*pi*V`.  Either route must be formalized from the
actual quotient tiling; `F=2V` may not simply be inserted as an unexplained
certificate field.

This completes the classical proof of the periodic Delaunay realization
theorem.  The difficulty is formalization infrastructure, not a missing
numerical inequality.

## 5. Periodic density bound from the realized triangulation

Let `V=|S|`, `F` be the number of quotient faces, and `A=L^2`.  For a face `T`
and an opposite edge `e`, the already-proved cotangent identity is

```
4*area(T) = sum_(e in T) length(e)^2*cot(theta_(T,e)).
```

For an edge with opposite face angles `alpha,beta`, weak Delaunay gives

```
cot(alpha)+cot(beta)
  = sin(alpha+beta)/(sin(alpha)*sin(beta)) >= 0.
```

The formal project uses the equivalent in-circle determinant identity, which
avoids angle branches.  Importantly, only the paired sum is nonnegative;
individual cotangents may be negative.

Validity gives `length(e)^2 >= weight(e)`.  Sum over faces, regroup by paired
edges before replacing the squared length, and then ungroup:

```
4A
 = sum_edges length(e)^2*(cot(alpha_e)+cot(beta_e))
 >= sum_edges weight(e)*(cot(alpha_e)+cot(beta_e))
 = sum_faces sum_(e in face) weight(e)*cot(theta_(face,e))
 >= 2F.
```

The last inequality is `(MT)`.  Since `F=2V`, this gives `4A>=4V`, hence

```
V <= A = L^2.                                      (PER)
```

`TorusTriangulation.card_le_area` kernel-checks this entire numerical step once
the genuine triangulation is packaged into the certificate.

## 6. Exact plane-to-periodic contrapositive used by Lean

This section deliberately matches `Periodization.lean` exactly.  Do not mix it
with earlier asymptotic constants.

Assume the epsilon/eventual statement fails.  Then there exist `e0>0` such
that, for every `R>=1`, some `r>=R` satisfies

```
N(r) > (1+e0)*pi*r^2,
```

where `N(r)=#(C inter closedBall(0,r))`.  Put

```
e = min(e0,1),
Rstar = (25/e)^2 + 169.
```

Choose a bad `r>=Rstar` and put `u=sqrt(r)`.  Then

```
u>=13,  e*u>=25,  r=u^2,
N(r)>(1+e)*pi*r^2.                                  (6.1)
```

### 6.1 Half-open grid pigeonhole

Partition the plane into disjoint half-open axis-parallel squares of side
`u`.  Let `I` be the finite set of grid squares containing points of
`C inter closedBall(0,r)`.  Every such square lies in
`closedBall(0,r+2u)`.  Disjointness and area give

```
|I|*u^2 <= pi*(r+2u)^2.
```

Choose an occupied square with maximal fiber `T`.  Since `N(r)<=|I|*|T|`,

```
N(r)*u^2 <= |T|*pi*(r+2u)^2.                         (6.2)
```

### 6.2 Explicit boundary loss

Retain only

```
S = T inter ([a+1,a+u-1] x [b+1,b+u-1]).
```

The deleted points lie in four closed strips of size `1 by u`.  For any finite
set `D` of `1`-separated points in a box of width `w` and height `h`, disjoint
radius-`1/2` discs lie in the box enlarged by `1/2` on each side, so each side
length increases by `1`; hence

```
|D|*pi/4 <= (w+1)*(h+1).
```

Using `pi>3`, each boundary strip contains at most `(8/3)*(u+1)` points.
Taking the union of four strips and weakening `32/3` to `11` gives

```
|T| <= |S| + 11*(u+1).                               (6.3)
```

### 6.3 Buffered periodization

Repeat `S` with its colors by `u*Z^2`.  Same-cell pairs remain valid.  For two
different cells, at least one coordinate differs by

```
u*|integer|-(u-2) >= 2.
```

Thus their distance is at least `2`, so their squared distance is at least
`4`, while the largest required squared distance is `2`.  The periodization is
valid.  Applying `(PER)` gives

```
|S| <= u^2.                                           (6.4)
```

### 6.4 Fully explicit polynomial contradiction

Combine (6.1)--(6.4), cancel positive `pi`, and use `r=u^2`:

```
(1+e)*u^6
  < (u^2+11u+11)*(u^2+2u)^2
  = u^6+15u^5+59u^4+88u^3+44u^2.
```

For `u>=13`,

```
59u^4 <= 5u^5,  88u^3 <= u^5,  44u^2 <= u^5.
```

Hence `e*u^6<22u^5`, i.e. `e*u<22`, contradicting `e*u>=25`.
Therefore the exact epsilon/eventual statement holds for every valid
configuration.

Earlier prose used the sharper but different bounds `r+sqrt(2)u` and
`8u-8`, together with an unspecified `O(u)`.  Those estimates are also
mathematically valid, but mixing them with the Lean constants obscured what
was proved.  The authoritative proof is the explicit chain above.

## 7. Equivalence with the published limsup

The ratio is nonnegative.  Separation gives the unconditional packing bound

```
N(r) <= 4*(r+1/2)^2 <= 9*r^2                 for r>=1,
```

and therefore

```
densityRatio(r) <= 9/pi.
```

Thus the real-valued `Filter.limsup` is neither an unbounded-above nor an
unbounded-below junk value.  Standard limsup lemmas then prove that the
epsilon/eventual statement is equivalent to the published `limsup<=1` form.
This is kernel-checked by `upperRadialDensity_iff_limsup`.

## 8. Forbidden shortcuts and previously found errors

* Do not use the false statement that every individual Voronoi cell has area
  at least `1`.  A valid six-point configuration with a central color-`0`
  point and five neighbors of colors `2,3,2,3,2`, at radii
  `1,sqrt(5)/2,1,sqrt(5)/2,1` and angles
  `0,3pi/8,3pi/4,9pi/8,3pi/2`, has central Voronoi area approximately
  `0.9941610114<1`.
* Do not infer a one-sided inequality from squares without proving `N>=0`.
* Do not assume individual cotangents are nonnegative; group paired darts
  first.
* Do not assume the original configuration is periodic, saturated, or already
  triangulated.
* Do not treat `TorusTriangulation` as arbitrary input to the final theorem.
  Construct a genuine periodic Delaunay tiling and derive its certificate.
* Do not hide coverage, cocircular cells, lattice translations, vertex orbits,
  area, or Euler counting in unexplained structure fields.
* Do not forbid a finite-cover proof of area or Euler.  If a cover is used,
  prove its simplicial injectivity and all count/area scaling identities.
* Do not use an orbit-constant perturbation of sites to resolve cocircularity;
  triangulate bounded Delaunay-cell orbits equivariantly.
* Do not state that equality in the local inequality fixes scale; it fixes only
  a similarity class.
* Do not revert to an asymptotic boundary proof while claiming to formalize the
  explicit constants in `Periodization.lean`.
* Do not use `sorry`, `admit`, new `axiom`, `opaque`, `unsafe`,
  `native_decide`, `@[implemented_by]`, or the desired conclusion as a
  hypothesis.

## 9. Completion criterion

Completion requires a kernel-checked semantic construction in Section 4,
conversion of that construction to the numerical certificate, successful
`lake build`, no proof placeholders or project-specific axioms, and

```
#print axioms Conjecture41.conjecture_4_1
```

without `sorryAx`.

**This criterion is now met.**  The semantic construction of Section 4 is the
canonical fan triangulation of the periodization (`CanonicalFan.lean`,
`GlobalTriangulation.lean`, `TriangleInterior.lean`, `LocalFiniteness.lean`,
`EdgeGrowth.lean`, `EdgeNeighbour.lean`, `EdgeToEdge.lean`), its finite torus
quotient (`Fundamental.lean`, `Darts.lean`, `TorusQuotient.lean`), the quotient
area identity (`QuotientArea.lean`) and the quotient Euler identity derived
from the `2π` angle sum around a site (`VertexSum.lean`,
`QuotientEuler.lean`).  Its conversion to the numerical certificate is
`PeriodicConfig.torusTriangulation` (`PeriodicCertificate.lean`), and
`Conjecture41.conjecture_4_1` depends only on `propext`, `Classical.choice`
and `Quot.sound`.
-/
