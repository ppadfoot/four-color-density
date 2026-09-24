import Conjecture41.GlobalTriangulation
import Conjecture41.TriangleInterior

set_option autoImplicit false

/-!
# Local finiteness of the global fan triangulation

A full-dimensional Delaunay cell has nonempty interior (it contains a
positively oriented fan triangle), so it determines its centre.  Combined with
`DeloneSet.finite_delCells_meeting_closedBall` this shows that only finitely
many full-dimensional centres — hence only finitely many triangles of the
global family — meet a given closed ball.
-/

namespace Conjecture41

open Set Metric

namespace DeloneSet

variable (D : DeloneSet)

lemma two_le_delLast {v : Plane} (h3 : 3 ≤ D.nsCard v) : 2 ≤ D.delLast v := by
  have h1 : D.delLast v = D.nsCard v - 1 := rfl
  omega

/-- A triangle of the canonical fan has nonempty interior. -/
theorem nonempty_interior_delTri {v : Plane} (h3 : 3 ≤ D.nsCard v) {i : ℕ} (hi : 1 ≤ i)
    (hlt : i < D.delLast v) : (interior (D.delTri v i)).Nonempty :=
  nonempty_interior_triangle (D.cross_delTri_pos h3 hi hlt)

/-- A full-dimensional Delaunay cell has nonempty interior. -/
theorem nonempty_interior_delCell {v : Plane} (h3 : 3 ≤ D.nsCard v) :
    (interior (D.delCell v)).Nonempty := by
  obtain ⟨x, hx⟩ := D.nonempty_interior_delTri h3 le_rfl (D.two_le_delLast h3)
  exact ⟨x, interior_mono (D.delTri_subset_delCell h3 (D.two_le_delLast h3)) hx⟩

/-- A full-dimensional Delaunay cell determines its centre. -/
theorem delCell_injOn : Set.InjOn D.delCell {v : Plane | 3 ≤ D.nsCard v} := by
  intro v hv v' _ h
  obtain ⟨z, hz⟩ := D.nonempty_interior_delCell hv
  exact D.center_eq_of_mem_interior hz (h ▸ interior_subset hz)

/-- **Local finiteness of the full-dimensional Delaunay centres.** -/
theorem finite_fanCenters (c : Plane) (r : ℝ) :
    {v : Plane | 3 ≤ D.nsCard v ∧ (D.delCell v ∩ closedBall c r).Nonempty}.Finite := by
  refine Set.Finite.of_finite_image (f := D.delCell) ?_ ?_
  · refine (D.finite_delCells_meeting_closedBall c r).subset ?_
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, rfl, hv.2⟩
  · exact D.delCell_injOn.mono fun v hv => hv.1

/-- **Local finiteness of the global fan triangulation.** -/
theorem finite_fanIndices (c : Plane) (r : ℝ) :
    {p : Plane × ℕ | D.IsFanIndex p.1 p.2 ∧ (D.delTri p.1 p.2 ∩ closedBall c r).Nonempty}.Finite := by
  refine Set.Finite.subset
    ((D.finite_fanCenters c r).biUnion
      (fun v _ => (Set.finite_singleton v).prod (Set.finite_Iio (D.delLast v)))) ?_
  rintro ⟨v, i⟩ ⟨hidx, x, hx1, hx2⟩
  have hv : v ∈ {v : Plane | 3 ≤ D.nsCard v ∧ (D.delCell v ∩ closedBall c r).Nonempty} :=
    ⟨hidx.1, ⟨x, D.delTri_subset_delCell hidx.1 hidx.2.2 hx1, hx2⟩⟩
  exact Set.mem_biUnion hv ⟨rfl, hidx.2.2⟩

end DeloneSet

end Conjecture41
