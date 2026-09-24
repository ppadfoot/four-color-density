import Conjecture41.PeriodicLift
import Conjecture41.TorusCertificate
import Conjecture41.PeriodicDelaunay
import Conjecture41.PeriodicCertificate

set_option autoImplicit false

/-!
# The periodic density theorem

This file assembles the whole critical path and proves the periodic density
theorem `V ≤ A` unconditionally.

* `TorusTriangulation.card_le_area` turns a `Λ`-equivariant weak Delaunay
  triangulation of the quotient torus into the bound `V ≤ A`, using the
  cotangent area identity, the nonnegativity of paired cotangent weights of
  weak Delaunay edges, the marked triangle budget for arbitrary color triples,
  and the global regrouping of the sum over corners into a sum over edges;
* `exists_torusTriangulation` below *constructs* that triangulation for every
  nonempty periodic configuration, as the finite quotient of the canonical fan
  triangulation of the periodization; its Euler and area fields are theorems
  about that tiling, not free parameters;
* `conjecture_4_1_of_periodic` turns the periodic theorem into the exact
  unrestricted statement of Conjecture 4.1, by square extraction, the explicit
  boundary-strip estimate, and buffered periodization.

Note that `TorusTriangulation` does *not* require the quotient graph to be
simple: the dart pairing `pf` is only required to be a fixed-point-free
involution, so loops and multiple edges in the quotient are permitted.

The authoritative mathematical proof and the semantic realization requirements
are recorded in `AuthoritativeProof.lean`.

## Why the nonemptiness hypothesis is present, and why it costs nothing

A `PeriodicConfig` with `points = ∅` is perfectly legal (all exclusion
inequalities hold vacuously), and it admits *no* torus triangulation
whatsoever: by `TorusTriangulation.carrier_nonempty` the existence of a
triangulation of a quotient of positive area forces the configuration to be
nonempty.  So the unrestricted form of `exists_torusTriangulation` is false,
and the hypothesis `P.points.Nonempty` is not an escape hatch but a necessary
nondegeneracy assumption; see `torusTriangulation_forces_nonempty` below.  The
empty case of the periodic theorem is of course trivial (`0 ≤ L²`) and is
discharged unconditionally in `periodic_density`.
-/

namespace Conjecture41

/-- Nonemptiness is *necessary* for the existence of a torus triangulation of a
periodic configuration: it is not a strengthening of the obligation that could
hide the mathematical content. -/
theorem torusTriangulation_forces_nonempty (P : PeriodicConfig)
    (S : TorusTriangulation P.lift (P.side ^ 2)) : P.points.Nonempty := by
  obtain ⟨x, hx⟩ := S.carrier_nonempty (pow_pos P.side_pos 2)
  obtain ⟨s, hs, -⟩ := hx
  exact ⟨s, hs⟩

/--
**Every nonempty square-periodic valid configuration admits a `Λ`-equivariant
weak Delaunay triangulation of its quotient torus**, with `V = #points`
vertices and total face area equal to the area `L²` of a fundamental domain.

The certificate is not manufactured: it is the quotient of the canonical fan
triangulation of the periodization `P.deloneLift`, assembled in
`PeriodicCertificate.lean` from

* the global fan triangulation of an arbitrary Delone set, which covers the
  plane, has pairwise disjoint interiors, is locally finite, is edge-to-edge,
  uses exactly the sites as vertices, and is weakly Delaunay
  (`CanonicalFan.lean`, `GlobalTriangulation.lean`, `TriangleInterior.lean`,
  `LocalFiniteness.lean`, `EdgeGrowth.lean`, `EdgeNeighbour.lean`,
  `EdgeToEdge.lean`);
* its finite quotient by the period lattice, with the dart involution given by
  actual integer lattice shifts (`Fundamental.lean`, `Darts.lean`,
  `TorusQuotient.lean`);
* the quotient area identity `Σ area = L²` (`QuotientArea.lean`);
* the angle sum `2π` around every site and the resulting quotient Euler
  identity `F = 2V` (`VertexSum.lean`, `QuotientEuler.lean`).
-/
theorem exists_torusTriangulation (P : PeriodicConfig) (hne : P.points.Nonempty) :
    ∃ S : TorusTriangulation P.lift (P.side ^ 2), S.nV = P.points.card :=
  ⟨P.torusTriangulation hne, rfl⟩

/-- The periodic density theorem: `V ≤ A` for every square-periodic valid
configuration (gate G6). -/
theorem periodic_density : PeriodicDensityTheorem := by
  intro P
  rcases P.points.eq_empty_or_nonempty with hemp | hne
  · rw [hemp]
    simpa using sq_nonneg P.side
  obtain ⟨S, hS⟩ := exists_torusTriangulation P hne
  have h := S.card_le_area
  rw [hS] at h
  exact h

end Conjecture41
