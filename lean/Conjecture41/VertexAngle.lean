import Conjecture41.TriangleCorner
import Conjecture41.LocalFiniteness
import Conjecture41.Darts

set_option autoImplicit false

/-!
# Corner angles of the global fan triangulation

This file introduces the corner angle `DeloneSet.dangle v i j` of the fan
triangle `(v, i)` at its `j`-th vertex, and proves the two facts about it that
the Euler gate needs:

* `DeloneSet.sum_dangle` — the three angles of a fan triangle add up to `π`;
* `DeloneSet.volume_delTri_inter_ball` — near its `j`-th vertex the triangle is
  a circular sector of angle `dangle v i j`, so its area inside the small ball
  of radius `r` is `dangle · r² / 2`.

It also proves the key combinatorial input

* `DeloneSet.exists_dvert_eq_of_mem_delTri` — a *site* lying in a fan triangle
  must be one of the three vertices of that triangle,

which is what makes the local area count around a site finite and exact.
-/

namespace Conjecture41

open MeasureTheory Set Metric EuclideanGeometry
open scoped ENNReal Real RealInnerProductSpace

/-- A point of a sphere lying in the convex hull of a subset of that sphere
belongs to the subset. -/
lemma mem_of_mem_convexHull_sphere {v s : Plane} {S : Set Plane} {R : ℝ} (hR : 0 < R)
    (hS : ∀ x ∈ S, dist v x = R) (hs : dist v s = R) (hmem : s ∈ convexHull ℝ S) : s ∈ S := by
  by_contra hns
  set c : ℝ := ⟪s - v, v⟫ + R ^ 2 with hc
  have hsv : ‖s - v‖ = R := by rw [← dist_eq_norm, dist_comm]; exact hs
  have hconv : Convex ℝ {x : Plane | ⟪s - v, x⟫ < c} := by
    refine convex_halfSpace_lt ⟨fun a b => ?_, fun t a => ?_⟩ c
    · exact inner_add_right _ _ _
    · exact real_inner_smul_right _ _ _
  have hsub : S ⊆ {x : Plane | ⟪s - v, x⟫ < c} := by
    intro x hx
    have hxv : ‖x - v‖ = R := by rw [← dist_eq_norm, dist_comm]; exact hS x hx
    have hle : ⟪s - v, x - v⟫ ≤ R ^ 2 := by
      have := real_inner_le_norm (s - v) (x - v)
      rw [hsv, hxv] at this
      nlinarith
    have hlt : ⟪s - v, x - v⟫ < R ^ 2 := by
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        have heq : ⟪s - v, x - v⟫ = ‖s - v‖ * ‖x - v‖ := by rw [hsv, hxv, h]; ring
        have := inner_eq_norm_mul_iff_real.mp heq
        rw [hsv, hxv] at this
        have hxs : x = s := by
          have h2 : R • (s - v) = R • (x - v) := this
          have h3 : s - v = x - v := smul_right_injective Plane hR.ne' h2
          have : s = x := by
            have := congrArg (fun z : Plane => z + v) h3
            simpa using this
          exact this.symm
        exact hns (hxs ▸ hx)
    have hexp : ⟪s - v, x⟫ = ⟪s - v, x - v⟫ + ⟪s - v, v⟫ := by
      rw [← inner_add_right]
      congr 1
      abel
    show ⟪s - v, x⟫ < c
    rw [hexp, hc]
    linarith
  have hfin := convexHull_min hsub hconv hmem
  have hval : ⟪s - v, s⟫ = c := by
    have hexp : ⟪s - v, s⟫ = ⟪s - v, s - v⟫ + ⟪s - v, v⟫ := by
      rw [← inner_add_right]; congr 1; abel
    have : ⟪s - v, s - v⟫ = R ^ 2 := by
      rw [real_inner_self_eq_norm_sq, hsv]
    rw [hexp, this, hc]; ring
  have : ⟪s - v, s⟫ < c := hfin
  rw [hval] at this
  exact lt_irrefl _ this

namespace DeloneSet

variable (D : DeloneSet)

/-- **A site lying in a fan triangle is one of its three vertices.** -/
theorem exists_dvert_eq_of_mem_delTri {v : Plane} {i : ℕ} (hidx : D.IsFanIndex v i)
    {s : Plane} (hs : s ∈ D.carrier) (hmem : s ∈ D.delTri v i) :
    ∃ j : Fin 3, D.dvert v i j = s := by
  have hpos : 0 < D.nd v := D.nd_pos_of_three_nearest hidx.1
  have hcell : s ∈ D.delCell v := D.delTri_subset_delCell hidx.1 hidx.2.2 hmem
  have hnear : s ∈ D.nearestSet v := D.mem_nearestSet_of_mem_delCell hs hcell
  have hS : ∀ x ∈ ({D.dvert v i 0, D.dvert v i 1, D.dvert v i 2} : Set Plane),
      dist v x = D.nd v := by
    rintro x (rfl | rfl | rfl)
    · exact (D.delVert_mem_nearestSet hpos (Nat.zero_le _)).2
    · exact (D.delVert_mem_nearestSet hpos (le_of_lt hidx.2.2)).2
    · exact (D.delVert_mem_nearestSet hpos hidx.2.2).2
  have hin := mem_of_mem_convexHull_sphere hpos hS hnear.2 (D.delTri_eq_dvert v i ▸ hmem)
  rcases hin with h | h | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩
  · exact ⟨2, h.symm⟩

/-! ### The corner angles -/

/-- The angle of the fan triangle `(v, i)` at its `j`-th vertex. -/
noncomputable def dangle (v : Plane) (i : ℕ) (j : Fin 3) : ℝ :=
  ∠ (D.dvert v i (j + 1)) (D.dvert v i j) (D.dvert v i (j + 2))

lemma dangle_nonneg (v : Plane) (i : ℕ) (j : Fin 3) : 0 ≤ D.dangle v i j :=
  EuclideanGeometry.angle_nonneg _ _ _

/-- **The angles of a fan triangle add up to `π`.** -/
theorem sum_dangle {v : Plane} {i : ℕ} (hidx : D.IsFanIndex v i) :
    ∑ j : Fin 3, D.dangle v i j = π := by
  have hne : D.dvert v i 1 ≠ D.dvert v i 0 :=
    D.dvert_ne_of_ne hidx (by decide)
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := D.dvert v i 0) (p₂ := D.dvert v i 1) (D.dvert v i 2) hne
  have e0 : D.dangle v i 0 = ∠ (D.dvert v i 2) (D.dvert v i 0) (D.dvert v i 1) := by
    show ∠ (D.dvert v i 1) (D.dvert v i 0) (D.dvert v i 2) = _
    exact EuclideanGeometry.angle_comm _ _ _
  have e1 : D.dangle v i 1 = ∠ (D.dvert v i 0) (D.dvert v i 1) (D.dvert v i 2) := by
    show ∠ (D.dvert v i 2) (D.dvert v i 1) (D.dvert v i 0) = _
    exact EuclideanGeometry.angle_comm _ _ _
  have e2 : D.dangle v i 2 = ∠ (D.dvert v i 1) (D.dvert v i 2) (D.dvert v i 0) := by
    show ∠ (D.dvert v i 0) (D.dvert v i 2) (D.dvert v i 1) = _
    exact EuclideanGeometry.angle_comm _ _ _
  rw [Fin.sum_univ_three, e0, e1, e2]
  linarith

/-! ### The corner is a sector -/

/-- The radius below which the corner of the fan triangle `(v, i)` at its `j`-th
vertex is exactly a circular sector. -/
noncomputable def cornerThr (v : Plane) (i : ℕ) (j : Fin 3) : ℝ :=
  cross (D.dvert v i j) (D.dvert v i (j + 1)) (D.dvert v i (j + 2)) /
    (|D.dvert v i (j + 2) 0 - D.dvert v i (j + 1) 0| +
      |D.dvert v i (j + 2) 1 - D.dvert v i (j + 1) 1| + 1)

lemma cornerThr_pos {v : Plane} {i : ℕ} (hidx : D.IsFanIndex v i) (j : Fin 3) :
    0 < D.cornerThr v i j := by
  have h1 := D.cross_dvert_cyclic hidx j
  have h2 : 0 < |D.dvert v i (j + 2) 0 - D.dvert v i (j + 1) 0| +
      |D.dvert v i (j + 2) 1 - D.dvert v i (j + 1) 1| + 1 := by positivity
  exact div_pos h1 h2

lemma delTri_eq_convexHull_cyclic (v : Plane) (i : ℕ) (j : Fin 3) :
    D.delTri v i =
      convexHull ℝ ({D.dvert v i j, D.dvert v i (j + 1), D.dvert v i (j + 2)} : Set Plane) := by
  rw [D.delTri_eq_dvert v i]
  congr 1
  fin_cases j
  · rfl
  · show ({D.dvert v i 0, D.dvert v i 1, D.dvert v i 2} : Set Plane)
      = {D.dvert v i 1, D.dvert v i 2, D.dvert v i 0}
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · show ({D.dvert v i 0, D.dvert v i 1, D.dvert v i 2} : Set Plane)
      = {D.dvert v i 2, D.dvert v i 0, D.dvert v i 1}
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-- **The corner of a fan triangle is a circular sector.** -/
theorem volume_delTri_inter_ball {v : Plane} {i : ℕ} (hidx : D.IsFanIndex v i) (j : Fin 3)
    {r : ℝ} (hr : 0 < r) (hle : r ≤ D.cornerThr v i j) :
    volume (D.delTri v i ∩ ball (D.dvert v i j) r)
      = ENNReal.ofReal (D.dangle v i j * r ^ 2 / 2) := by
  have hD := D.cross_dvert_cyclic hidx j
  have hM : 0 < |D.dvert v i (j + 2) 0 - D.dvert v i (j + 1) 0| +
      |D.dvert v i (j + 2) 1 - D.dvert v i (j + 1) 1| + 1 := by positivity
  have hsmall : r * (|D.dvert v i (j + 2) 0 - D.dvert v i (j + 1) 0| +
      |D.dvert v i (j + 2) 1 - D.dvert v i (j + 1) 1| + 1)
      ≤ cross (D.dvert v i j) (D.dvert v i (j + 1)) (D.dvert v i (j + 2)) := by
    rw [← le_div_iff₀ hM]
    exact hle
  rw [D.delTri_eq_convexHull_cyclic v i j, volume_triangle_corner hD hr hsmall]
  rfl

end DeloneSet

end Conjecture41
