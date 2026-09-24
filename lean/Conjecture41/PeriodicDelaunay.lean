import Conjecture41.VoronoiVertex

set_option autoImplicit false

/-!
# The periodic Delaunay structure of a square-periodic configuration

This file specializes the Delone/Voronoi/Delaunay theory of
`Delone.lean`, `VoronoiPolygon.lean`, `DelaunayCell.lean`, `DelaunayTiling.lean`
and `VoronoiVertex.lean` to the lift of a nonempty `PeriodicConfig`, and records
the `L·ℤ²`-equivariance of every object involved.

Proved here:

* `latticeSet_add_latticeVec`: the periodization is invariant under the period
  lattice, in the form of an equality of translated sets;
* `cell_add_latticeVec`, `nearestSet_add_latticeVec`, `delCell_add_latticeVec`:
  Voronoi cells, nearest-site sets and Delaunay cells are lattice equivariant;
* `exists_weak_delaunay_triangle_periodic`: every point of the periodization is
  a vertex of a positively oriented nondegenerate triangle of periodization
  points on a common empty circle, satisfying the weak Delaunay in-circle
  inequality against every point of the periodization.

These are the equivariance and vertex-orbit ingredients (gates G5a, G5b, G5d)
of the geometric chain.  The subsequent modules complete that chain:
`CanonicalFan.lean` and `GlobalTriangulation.lean` construct the equivariant
triangulation of the Delaunay cell orbits, `TorusQuotient.lean` constructs its
finite quotient and dart pairing, and `QuotientArea.lean` and
`QuotientEuler.lean` derive the area and Euler identities.  The assembled
theorem is exposed in `PeriodicProof.lean`.
-/

namespace Conjecture41

open Metric Set

namespace PeriodicConfig

variable (P : PeriodicConfig) (hne : P.points.Nonempty)

/-- The periodization is invariant under a translation by a period. -/
lemma latticeSet_add_latticeVec (m n : ℤ) :
    (fun p : Plane => p + latticeVec P.side m n) '' P.latticeSet = P.latticeSet := by
  ext x
  constructor
  · rintro ⟨y, ⟨s, hs, m', n', rfl⟩, rfl⟩
    refine ⟨s, hs, m' + m, n' + n, ?_⟩
    simp only
    rw [add_assoc, latticeVec_add]
  · rintro ⟨s, hs, m', n', rfl⟩
    refine ⟨s + latticeVec P.side (m' - m) (n' - n), ⟨s, hs, m' - m, n' - n, rfl⟩, ?_⟩
    simp only
    rw [add_assoc, latticeVec_add]
    congr 2 <;> ring

/-- The Delone set attached to the periodization has the periodization as
carrier. -/
lemma deloneLift_carrier_eq : (P.deloneLift hne).carrier = P.latticeSet := rfl

/-- Voronoi cells of the periodization are lattice equivariant. -/
lemma cell_add_latticeVec (x : Plane) (m n : ℤ) :
    (P.deloneLift hne).cell (x + latticeVec P.side m n)
      = (fun p : Plane => p + latticeVec P.side m n) '' (P.deloneLift hne).cell x :=
  (P.deloneLift hne).cell_translate (P.latticeSet_add_latticeVec m n) x

/-- Nearest-site sets of the periodization are lattice equivariant. -/
lemma nearestSet_add_latticeVec (v : Plane) (m n : ℤ) :
    (P.deloneLift hne).nearestSet (v + latticeVec P.side m n)
      = (fun p : Plane => p + latticeVec P.side m n) '' (P.deloneLift hne).nearestSet v :=
  (P.deloneLift hne).nearestSet_translate (P.latticeSet_add_latticeVec m n) v

/-- Delaunay cells of the periodization are lattice equivariant. -/
lemma delCell_add_latticeVec (v : Plane) (m n : ℤ) :
    (P.deloneLift hne).delCell (v + latticeVec P.side m n)
      = (fun p : Plane => p + latticeVec P.side m n) '' (P.deloneLift hne).delCell v :=
  (P.deloneLift hne).delCell_translate (P.latticeSet_add_latticeVec m n) v

/-- Delaunay cells of the periodization cover the plane. -/
theorem exists_mem_delCell_periodic (z : Plane) :
    ∃ v : Plane, z ∈ (P.deloneLift hne).delCell v :=
  (P.deloneLift hne).exists_mem_delCell z

/-- Every point of the periodization is a vertex of a positively oriented
nondegenerate weak Delaunay triangle of periodization points. -/
theorem exists_weak_delaunay_triangle_periodic (hne' : P.points.Nonempty)
    {x : Plane} (hx : x ∈ P.latticeSet) :
    ∃ y₁ y₂ : Plane, y₁ ∈ P.latticeSet ∧ y₂ ∈ P.latticeSet ∧ 0 < cross x y₁ y₂ ∧
      ∀ e ∈ P.latticeSet, 0 ≤ inCircleDet x y₁ y₂ e :=
  (P.deloneLift hne').exists_weak_delaunay_triangle hx

/-- **Finitely many Delaunay cell orbits.**  Every Delaunay cell of the
periodization is a lattice translate of one of finitely many cells.  This is
the finiteness of the quotient tiling, proved from local finiteness of the
Delaunay tiling together with the covering radius of the period lattice. -/
theorem finite_delCell_orbits :
    ∃ F : Set (Set Plane), F.Finite ∧
      ∀ v : Plane, ∃ K ∈ F, ∃ m n : ℤ,
        (P.deloneLift hne).delCell v
          = (fun p : Plane => p + latticeVec P.side m n) '' K := by
  classical
  set D := P.deloneLift hne with hD
  set R : ℝ := Real.sqrt (P.side ^ 2 / 2) + D.cov with hR
  refine ⟨{K : Set Plane | ∃ v : Plane, K = D.delCell v ∧ (K ∩ closedBall (0 : Plane) R).Nonempty},
    D.finite_delCells_meeting_closedBall 0 R, ?_⟩
  intro v
  obtain ⟨m, n, hmn⟩ := P.exists_lattice_near 0 (-v)
  have hnorm : ‖v + latticeVec P.side m n‖ ≤ Real.sqrt (P.side ^ 2 / 2) := by
    have h : dist (-v) (0 + latticeVec P.side m n) ≤ Real.sqrt (P.side ^ 2 / 2) := hmn
    rw [zero_add, dist_eq_norm] at h
    have hrw : -v - latticeVec P.side m n = -(v + latticeVec P.side m n) := by abel
    rwa [hrw, norm_neg] at h
  refine ⟨D.delCell (v + latticeVec P.side m n), ⟨v + latticeVec P.side m n, rfl, ?_⟩,
    -m, -n, ?_⟩
  · obtain ⟨y, hy⟩ := D.delCell_nonempty (v + latticeVec P.side m n)
    refine ⟨y, hy, ?_⟩
    have h1 : dist y (v + latticeVec P.side m n) ≤ D.cov := by
      have := D.delCell_subset_closedBall (v + latticeVec P.side m n) hy
      rwa [mem_closedBall] at this
    have h2 : dist (v + latticeVec P.side m n) 0 = ‖v + latticeVec P.side m n‖ := by
      rw [dist_eq_norm, sub_zero]
    have h3 := dist_triangle y (v + latticeVec P.side m n) 0
    rw [mem_closedBall, hR]
    rw [h2] at h3
    linarith
  · rw [P.delCell_add_latticeVec hne v m n, Set.image_image]
    have hid : ∀ p : Plane, p + latticeVec P.side m n + latticeVec P.side (-m) (-n) = p := by
      intro p
      rw [add_assoc, latticeVec_add]
      simp
    simp only [hid]
    exact (Set.image_id _).symm

end PeriodicConfig

end Conjecture41
