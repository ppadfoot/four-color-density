import Conjecture41.Delone
import Conjecture41.Voronoi

set_option autoImplicit false

/-!
# Voronoi polygons of a Delone set

For a Delone set `D` in the plane and a point `x`, the Voronoi cell

```
cell x = {z | ∀ y ∈ D.carrier, dist z x ≤ dist z y}
```

is studied here semantically.  We prove:

* `cell_subset_closedBall`: every cell is contained in the closed ball of
  radius the covering radius around its site (relative density);
* `isClosed_cell`, `convex_cell`, `isCompact_cell`: cells are compact and
  convex;
* `ball_subset_cell`: cells of sites have nonempty interior (separation);
* `exists_mem_cell`: the cells cover the plane;
* `cell_eq_biInter_near`: a cell is *exactly* the intersection of the finitely
  many half-planes coming from the sites within `3 * cov` of its site — the
  redundancy of all farther sites is proved, not assumed, so a cell is a
  compact convex polygon;
* `disjoint_interior_cell`: cells of distinct sites have disjoint interiors;
* `cell_meets_compact`: local finiteness, in the form that a cell meeting a
  set has its site within `cov` of that set;
* `cell_translate`: equivariance under any translation preserving the set.

This is gate G5a (Voronoi part) of the formalization ledger.
-/

namespace Conjecture41

open Metric Set

namespace DeloneSet

variable (D : DeloneSet)

/-- The Voronoi cell of `x` with respect to the Delone set `D`. -/
def cell (x : Plane) : Set Plane := {z | ∀ y ∈ D.carrier, dist z x ≤ dist z y}

lemma mem_cell_iff {x z : Plane} :
    z ∈ D.cell x ↔ ∀ y ∈ D.carrier, dist z x ≤ dist z y := Iff.rfl

lemma mem_cell_self (x : Plane) : x ∈ D.cell x := by
  intro y _
  simp [dist_nonneg]

/-- Relative density bounds every Voronoi cell by the covering radius. -/
lemma cell_subset_closedBall (x : Plane) : D.cell x ⊆ closedBall x D.cov := by
  intro z hz
  obtain ⟨y, hy, hyd⟩ := D.cover z
  have h := hz y hy
  rw [mem_closedBall]
  linarith

lemma isClosed_cell (x : Plane) : IsClosed (D.cell x) := by
  have h : D.cell x = ⋂ y ∈ D.carrier, {z : Plane | dist z x ≤ dist z y} := by
    ext z; simp [cell]
  rw [h]
  exact isClosed_biInter fun y _ => isClosed_le (continuous_id.dist continuous_const)
    (continuous_id.dist continuous_const)

lemma convex_cell (x : Plane) : Convex ℝ (D.cell x) := by
  have h : D.cell x = ⋂ y ∈ D.carrier, {z : Plane | dist z x ≤ dist z y} := by
    ext z; simp [cell]
  rw [h]
  exact convex_iInter fun y => convex_iInter fun _ => convex_setOf_dist_le x y

lemma isCompact_cell (x : Plane) : IsCompact (D.cell x) :=
  (isCompact_closedBall x D.cov).of_isClosed_subset (D.isClosed_cell x)
    (D.cell_subset_closedBall x)

/-- Separation gives every cell of a site a nonempty interior. -/
lemma ball_subset_cell {x : Plane} (hx : x ∈ D.carrier) :
    ball x (1 / 2) ⊆ D.cell x := by
  intro z hz y hy
  rcases eq_or_ne y x with rfl | hyx
  · exact le_rfl
  · have hsep : 1 ≤ dist x y := D.sep hx hy (Ne.symm hyx)
    have hzx : dist z x < 1 / 2 := by simpa using hz
    have h : dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
    rw [dist_comm x z] at h
    linarith

lemma interior_cell_nonempty {x : Plane} (hx : x ∈ D.carrier) :
    (interior (D.cell x)).Nonempty := by
  refine ⟨x, ?_⟩
  have : ball x (1 / 2) ⊆ interior (D.cell x) :=
    interior_maximal (D.ball_subset_cell hx) isOpen_ball
  exact this (mem_ball_self (by norm_num))

/-- The Voronoi cells of the sites cover the plane. -/
lemma exists_mem_cell (z : Plane) : ∃ x ∈ D.carrier, z ∈ D.cell x := by
  obtain ⟨x, hx, hmin⟩ := D.exists_nearest z
  exact ⟨x, hx, hmin⟩

/-! ### A cell is cut out by finitely many half-planes -/

/-- If `z` satisfies all the comparison inequalities coming from sites within
`3 * cov` of `x`, then `z` is within `cov` of `x`.  This is the step that makes
the finite half-plane description legitimate: it does not merely use
boundedness of the cell. -/
lemma dist_le_cov_of_near_constraints {x : Plane} (z : Plane)
    (h : ∀ y ∈ D.carrier, dist x y ≤ 3 * D.cov → dist z x ≤ dist z y) :
    dist z x ≤ D.cov := by
  by_contra hgt
  push_neg at hgt
  rcases le_or_gt (dist x z) (2 * D.cov) with hle | hgt2
  · obtain ⟨y, hy, hyd⟩ := D.cover z
    have hxy : dist x y ≤ 3 * D.cov := by
      have := dist_triangle x z y
      linarith
    have := h y hy hxy
    linarith
  · -- move from `x` towards `z` a distance `2 * cov`
    have hcovpos : 0 < D.cov := D.cov_pos
    have hxz : (0 : ℝ) < dist x z := lt_trans (by positivity) hgt2
    set t : ℝ := 2 * D.cov / dist x z with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t < 1 := by
      rw [ht, div_lt_one hxz]; exact hgt2
    set w : Plane := x + t • (z - x) with hw
    have hnorm : ‖z - x‖ = dist x z := by rw [dist_comm, dist_eq_norm]
    have hxw : dist x w = 2 * D.cov := by
      rw [hw, dist_eq_norm]
      have : x - (x + t • (z - x)) = -(t • (z - x)) := by abel
      rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, hnorm, ht]
      field_simp
    have hwz : dist w z = dist x z - 2 * D.cov := by
      rw [hw, dist_eq_norm]
      have hrw : x + t • (z - x) - z = -((1 - t) • (z - x)) := by
        rw [sub_smul, one_smul]; abel
      rw [hrw, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hnorm, ht]
      field_simp
    obtain ⟨y, hy, hyd⟩ := D.cover w
    have hxy : dist x y ≤ 3 * D.cov := by
      have := dist_triangle x w y
      have hcov := D.cov_pos
      linarith
    have hzy : dist z y ≤ dist x z - D.cov := by
      have h1 : dist z y ≤ dist z w + dist w y := dist_triangle _ _ _
      rw [dist_comm z w] at h1
      linarith
    have := h y hy hxy
    rw [dist_comm z x] at this
    have hcov := D.cov_pos
    linarith

/-- The exact finite half-plane description of a Voronoi cell.  Farther sites
are redundant. -/
lemma mem_cell_of_near_constraints {x : Plane} (z : Plane)
    (h : ∀ y ∈ D.carrier, dist x y ≤ 3 * D.cov → dist z x ≤ dist z y) :
    z ∈ D.cell x := by
  intro y hy
  by_cases hxy : dist x y ≤ 3 * D.cov
  · exact h y hy hxy
  · push_neg at hxy
    have hzx : dist z x ≤ D.cov := D.dist_le_cov_of_near_constraints z h
    have h1 : dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
    rw [dist_comm x z] at h1
    have hcov := D.cov_pos
    linarith

/-- A Voronoi cell is exactly the intersection of the finitely many half-planes
determined by the sites within `3 * cov` of its site. -/
lemma cell_eq_biInter_near (x : Plane) :
    D.cell x = ⋂ y ∈ D.ballFinset x (3 * D.cov), {z : Plane | dist z x ≤ dist z y} := by
  ext z
  simp only [Set.mem_iInter, Set.mem_setOf_eq, D.mem_ballFinset]
  constructor
  · intro hz y hy
    exact hz y hy.1
  · intro h
    refine D.mem_cell_of_near_constraints z ?_
    intro y hy hxy
    exact h y ⟨hy, by rwa [dist_comm]⟩

/-! ### Disjoint interiors -/

/-- The comparison half-plane in linear form. -/
lemma dist_le_iff_inner (x y z : Plane) :
    dist z x ≤ dist z y ↔ (inner ℝ z (y - x) : ℝ) ≤ (‖y‖ ^ 2 - ‖x‖ ^ 2) / 2 := by
  simp only [dist_eq_norm]
  rw [← Real.sqrt_sq (norm_nonneg (z - x)), ← Real.sqrt_sq (norm_nonneg (z - y)),
    Real.sqrt_le_sqrt_iff (by positivity), @norm_sub_sq_real, @norm_sub_sq_real,
    inner_sub_right]
  constructor <;> intro h <;> linarith

/-- A point in the interior of a closed half-space satisfies the strict
inequality. -/
lemma inner_lt_of_mem_interior {a : Plane} (ha : a ≠ 0) {c : ℝ} {z : Plane}
    (hz : z ∈ interior {w : Plane | (inner ℝ w a : ℝ) ≤ c}) :
    (inner ℝ z a : ℝ) < c := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  have hanorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set d : ℝ := ε / (2 * ‖a‖) with hd
  have hdpos : 0 < d := by positivity
  have hmem : z + d • a ∈ ball z ε := by
    rw [mem_ball, dist_eq_norm]
    have hrw : z + d • a - z = d • a := by abel
    rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_pos hdpos, hd]
    rw [div_mul_eq_mul_div, mul_comm]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hin : z + d • a ∈ {w : Plane | (inner ℝ w a : ℝ) ≤ c} := interior_subset (hball hmem)
  simp only [Set.mem_setOf_eq, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hin
  have hpos : 0 < d * ‖a‖ ^ 2 := by positivity
  linarith

/-- Distinct sites have Voronoi cells with disjoint interiors. -/
lemma disjoint_interior_cell {x y : Plane} (hx : x ∈ D.carrier) (hy : y ∈ D.carrier)
    (hxy : x ≠ y) :
    Disjoint (interior (D.cell x)) (interior (D.cell y)) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  have hane : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hsub : D.cell x ⊆ {w : Plane | (inner ℝ w (y - x) : ℝ) ≤ (‖y‖ ^ 2 - ‖x‖ ^ 2) / 2} := by
    intro w hw
    exact (dist_le_iff_inner x y w).mp (hw y hy)
  have hstrict : (inner ℝ z (y - x) : ℝ) < (‖y‖ ^ 2 - ‖x‖ ^ 2) / 2 :=
    inner_lt_of_mem_interior hane (interior_mono hsub hzx)
  have hzcelly : z ∈ D.cell y := interior_subset hzy
  have hother : (inner ℝ z (x - y) : ℝ) ≤ (‖x‖ ^ 2 - ‖y‖ ^ 2) / 2 :=
    (dist_le_iff_inner y x z).mp (hzcelly x hx)
  rw [show x - y = -(y - x) by abel, inner_neg_right] at hother
  linarith

/-! ### Local finiteness and equivariance -/

/-- Every point of the cell of `x` is within `cov` of `x`; hence a cell meeting
a set has its site within `cov` of that set. -/
lemma cell_meets (x : Plane) {z : Plane} (hz : z ∈ D.cell x) : dist x z ≤ D.cov := by
  have := D.cell_subset_closedBall x hz
  rw [mem_closedBall, dist_comm] at this
  exact this

/-- Only finitely many cells of sites meet a bounded set. -/
lemma finite_sites_meeting_closedBall (c : Plane) (r : ℝ) :
    {x | x ∈ D.carrier ∧ (D.cell x ∩ closedBall c r).Nonempty}.Finite := by
  refine Set.Finite.subset (D.finite_inter_closedBall c (r + D.cov)) ?_
  rintro x ⟨hx, z, hzc, hzb⟩
  refine ⟨hx, ?_⟩
  have h1 : dist x z ≤ D.cov := D.cell_meets x hzc
  have h2 : dist z c ≤ r := by simpa using hzb
  have := dist_triangle x z c
  simp only [mem_closedBall]
  linarith

/-- Voronoi cells are equivariant under any translation preserving the set. -/
lemma cell_translate {v : Plane} (hv : (fun p : Plane => p + v) '' D.carrier = D.carrier)
    (x : Plane) : D.cell (x + v) = (fun p : Plane => p + v) '' D.cell x := by
  ext z
  constructor
  · intro hz
    refine ⟨z - v, ?_, by simp⟩
    intro y hy
    have hyv : y + v ∈ D.carrier := by rw [← hv]; exact ⟨y, hy, rfl⟩
    have h := hz (y + v) hyv
    have e1 : dist (z - v) x = dist z (x + v) := by
      rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
    have e2 : dist (z - v) y = dist z (y + v) := by
      rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
    rw [e1, e2]
    exact h
  · rintro ⟨p, hp, rfl⟩
    intro y hy
    have hyv : y - v ∈ D.carrier := by
      rw [← hv] at hy
      obtain ⟨q, hq, hqe⟩ := hy
      have hq' : y - v = q := by rw [← hqe]; simp
      rwa [hq']
    have h := hp (y - v) hyv
    have e1 : dist (p + v) (x + v) = dist p x := by
      rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
    have e2 : dist (p + v) y = dist p (y - v) := by
      rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
    rw [e1, e2]
    exact h

end DeloneSet

end Conjecture41
