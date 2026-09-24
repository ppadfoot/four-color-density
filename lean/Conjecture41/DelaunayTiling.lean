import Conjecture41.DelaunayCell
import Conjecture41.Cotangent

set_option autoImplicit false

/-!
# The Delaunay tiling: maximality, face-to-face incidence, disjoint interiors

This file proves the structural (duality) properties of the Delaunay cells of a
Delone set, using the *power function*

```
pw v z = dist z v ^ 2 - nd v ^ 2
```

of the empty circle centred at `v`.  The point is that `pw v - pw v'` is an
*affine* function of `z` (the quadratic terms cancel), while `pw v x ≥ 0` for
every site `x`, with equality exactly on the nearest-site set of `v`.  This is
the analytic content of the lifting `x ↦ (x, |x|²)` to the paraboloid: `pw v`
measures the gap between the lifted point and the supporting plane of the
empty circle at `v`.

Consequences proved here:

* `pw_le_of_mem_delCell`: on its own Delaunay cell, the power function of `v`
  is minimal among all centres (the supporting plane of `v` is the highest
  one);
* `delCell_inter_eq`: two Delaunay cells meet exactly in the convex hull of the
  common nearest sites — the face-to-face property;
* `center_eq_of_mem_interior` and `disjoint_interior_delCell`: a Delaunay cell
  with nonempty interior determines its centre, so distinct centres have cells
  with disjoint interiors;
* `inCircleDet_nonneg_of_nearestSet`: the weak Delaunay (empty circumcircle)
  inequality in the in-circle determinant form used by the cotangent
  certificate;
* `finite_delCells_meeting_closedBall`: local finiteness of the tiling.

This is gate G5b (duality part) of the formalization ledger.
-/

namespace Conjecture41

open Metric Set

namespace DeloneSet

variable (D : DeloneSet)

/-- The power of `z` with respect to the empty circle centred at `v`. -/
noncomputable def pw (v z : Plane) : ℝ := dist z v ^ 2 - D.nd v ^ 2

/-- Every site has nonnegative power: the circle is empty. -/
lemma pw_nonneg {v x : Plane} (hx : x ∈ D.carrier) : 0 ≤ D.pw v x := by
  have h1 : D.nd v ≤ dist v x := D.nd_le_dist hx
  have h2 : dist v x = dist x v := dist_comm _ _
  have h3 : 0 ≤ D.nd v := D.nd_nonneg v
  simp only [pw]
  nlinarith

/-- A site has zero power exactly when it is a nearest site. -/
lemma pw_eq_zero_iff {v x : Plane} (hx : x ∈ D.carrier) :
    D.pw v x = 0 ↔ x ∈ D.nearestSet v := by
  have h3 : 0 ≤ D.nd v := D.nd_nonneg v
  have h4 : 0 ≤ dist x v := dist_nonneg
  constructor
  · intro h
    refine ⟨hx, ?_⟩
    simp only [pw] at h
    have : dist x v = D.nd v := by nlinarith
    rw [dist_comm]
    exact this
  · intro h
    have : dist x v = D.nd v := by rw [dist_comm]; exact h.2
    simp only [pw, this]
    ring

lemma pw_mem_nearestSet {v x : Plane} (hx : x ∈ D.nearestSet v) : D.pw v x = 0 :=
  (D.pw_eq_zero_iff hx.1).mpr hx

/-- The difference of two power functions is affine. -/
lemma pw_sub_eq (v v' z : Plane) :
    D.pw v z - D.pw v' z
      = 2 * (inner ℝ z (v' - v) : ℝ) + (‖v‖ ^ 2 - ‖v'‖ ^ 2 - D.nd v ^ 2 + D.nd v' ^ 2) := by
  have hv : dist z v ^ 2 = ‖z‖ ^ 2 - 2 * (inner ℝ z v : ℝ) + ‖v‖ ^ 2 := by
    rw [dist_eq_norm, @norm_sub_sq_real]
  have hv' : dist z v' ^ 2 = ‖z‖ ^ 2 - 2 * (inner ℝ z v' : ℝ) + ‖v'‖ ^ 2 := by
    rw [dist_eq_norm, @norm_sub_sq_real]
  have hinner : (inner ℝ z (v' - v) : ℝ) = (inner ℝ z v' : ℝ) - (inner ℝ z v : ℝ) :=
    inner_sub_right _ _ _
  simp only [pw, hv, hv', hinner]
  ring

/-- Evaluation of the affine difference on a convex combination. -/
lemma pw_sub_centerMass {ι : Type} (v v' : Plane) (t : Finset ι) (w : ι → ℝ)
    (p : ι → Plane) (hw : ∑ i ∈ t, w i = 1) :
    D.pw v (t.centerMass w p) - D.pw v' (t.centerMass w p)
      = ∑ i ∈ t, w i * (D.pw v (p i) - D.pw v' (p i)) := by
  have hcm : t.centerMass w p = ∑ i ∈ t, w i • p i := Finset.centerMass_eq_of_sum_1 _ _ hw
  have hinner : (inner ℝ (t.centerMass w p) (v' - v) : ℝ)
      = ∑ i ∈ t, w i * (inner ℝ (p i) (v' - v) : ℝ) := by
    rw [hcm, sum_inner]
    exact Finset.sum_congr rfl fun i _ => real_inner_smul_left _ _ _
  rw [D.pw_sub_eq v v', hinner]
  have hterm : ∀ i ∈ t, w i * (D.pw v (p i) - D.pw v' (p i))
      = w i * (2 * (inner ℝ (p i) (v' - v) : ℝ))
        + w i * (‖v‖ ^ 2 - ‖v'‖ ^ 2 - D.nd v ^ 2 + D.nd v' ^ 2) := by
    intro i _
    rw [D.pw_sub_eq v v']
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Maximality of the supporting plane.**  On the Delaunay cell of `v`, the
power function of `v` is at most that of any other centre. -/
theorem pw_le_of_mem_delCell {v z : Plane} (hz : z ∈ D.delCell v) (v' : Plane) :
    D.pw v z ≤ D.pw v' z := by
  rw [delCell, convexHull_eq] at hz
  obtain ⟨ι, t, w, p, hw0, hw1, hp, rfl⟩ := hz
  have h := D.pw_sub_centerMass v v' t w p hw1
  have hterm : ∀ i ∈ t, w i * (D.pw v (p i) - D.pw v' (p i)) ≤ 0 := by
    intro i hi
    have h1 : D.pw v (p i) = 0 := D.pw_mem_nearestSet (hp i hi)
    have h2 : 0 ≤ D.pw v' (p i) := D.pw_nonneg (D.nearestSet_subset_carrier v (hp i hi))
    have := hw0 i hi
    nlinarith
  have hsum : ∑ i ∈ t, w i * (D.pw v (p i) - D.pw v' (p i)) ≤ 0 :=
    Finset.sum_nonpos hterm
  linarith [h, hsum]

/-- **Face-to-face incidence.**  Two Delaunay cells meet exactly in the convex
hull of their common nearest sites. -/
theorem delCell_inter_eq (v v' : Plane) :
    D.delCell v ∩ D.delCell v' = convexHull ℝ (D.nearestSet v ∩ D.nearestSet v') := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨hy, hy'⟩
    have h1 : D.pw v y ≤ D.pw v' y := D.pw_le_of_mem_delCell hy v'
    have h2 : D.pw v' y ≤ D.pw v y := D.pw_le_of_mem_delCell hy' v
    have heq : D.pw v y - D.pw v' y = 0 := by linarith
    rw [delCell, convexHull_eq] at hy
    obtain ⟨ι, t, w, p, hw0, hw1, hp, hcm⟩ := hy
    have hsum : ∑ i ∈ t, w i * (D.pw v (p i) - D.pw v' (p i)) = 0 := by
      rw [← D.pw_sub_centerMass v v' t w p hw1, hcm]
      exact heq
    have hterm : ∀ i ∈ t, w i * (D.pw v (p i) - D.pw v' (p i)) ≤ 0 := by
      intro i hi
      have h1 : D.pw v (p i) = 0 := D.pw_mem_nearestSet (hp i hi)
      have h2 : 0 ≤ D.pw v' (p i) := D.pw_nonneg (D.nearestSet_subset_carrier v (hp i hi))
      have := hw0 i hi
      nlinarith
    have hzero : ∀ i ∈ t, w i * (D.pw v (p i) - D.pw v' (p i)) = 0 := by
      have hneg : ∀ i ∈ t, 0 ≤ -(w i * (D.pw v (p i) - D.pw v' (p i))) :=
        fun i hi => by linarith [hterm i hi]
      have hs : ∑ i ∈ t, -(w i * (D.pw v (p i) - D.pw v' (p i))) = 0 := by
        rw [Finset.sum_neg_distrib, hsum, neg_zero]
      have hall := (Finset.sum_eq_zero_iff_of_nonneg hneg).mp hs
      intro i hi
      have := hall i hi
      linarith
    -- restrict to the strictly positive weights
    rw [convexHull_eq]
    refine ⟨ι, {i ∈ t | w i ≠ 0}, w, p, ?_, ?_, ?_, ?_⟩
    · intro i hi
      exact hw0 i (Finset.mem_filter.mp hi).1
    · rw [Finset.sum_filter_ne_zero]
      exact hw1
    · intro i hi
      obtain ⟨hit, hiw⟩ := Finset.mem_filter.mp hi
      refine ⟨hp i hit, ?_⟩
      have h0 := hzero i hit
      have h1 : D.pw v (p i) = 0 := D.pw_mem_nearestSet (hp i hit)
      have h2 : D.pw v' (p i) = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h hiw
        · linarith [h, h1]
      exact (D.pw_eq_zero_iff (D.nearestSet_subset_carrier v (hp i hit))).mp h2
    · rw [Finset.centerMass_filter_ne_zero]
      exact hcm
  · refine convexHull_min ?_ (D.convex_delCell v |>.inter (D.convex_delCell v'))
    intro y hy
    exact ⟨D.nearestSet_subset_delCell v hy.1, D.nearestSet_subset_delCell v' hy.2⟩

/-- **A full-dimensional Delaunay cell determines its centre.** -/
theorem center_eq_of_mem_interior {v v' z : Plane} (hz : z ∈ interior (D.delCell v))
    (hz' : z ∈ D.delCell v') : v = v' := by
  by_contra hne
  set a : Plane := v - v' with ha
  have hane : a ≠ 0 := sub_ne_zero.mpr hne
  have hanorm : 0 < ‖a‖ := norm_pos_iff.mpr hane
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  set δ : ℝ := ε / (2 * ‖a‖) with hδ
  have hδpos : 0 < δ := by positivity
  set y : Plane := z - δ • a with hy
  have hymem : y ∈ D.delCell v := by
    refine interior_subset (hball ?_)
    rw [mem_ball, dist_eq_norm]
    have hrw : y - z = -(δ • a) := by rw [hy]; abel
    rw [hrw, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos, hδ]
    rw [div_mul_eq_mul_div, mul_comm]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  -- the affine difference vanishes at `z` and is nonnegative on the cell
  have hzeq : D.pw v z = D.pw v' z :=
    le_antisymm (D.pw_le_of_mem_delCell (interior_subset hz) v')
      (D.pw_le_of_mem_delCell hz' v)
  have hyge : D.pw v y ≤ D.pw v' y := D.pw_le_of_mem_delCell hymem v'
  have hz2 := D.pw_sub_eq v v' z
  have hy2 := D.pw_sub_eq v v' y
  have hinner : (inner ℝ y (v' - v) : ℝ)
      = (inner ℝ z (v' - v) : ℝ) - δ * (inner ℝ a (v' - v) : ℝ) := by
    rw [hy, inner_sub_left, real_inner_smul_left]
  have hav : (inner ℝ a (v' - v) : ℝ) = -(‖a‖ ^ 2) := by
    have hrw : v' - v = -a := by rw [ha]; abel
    rw [hrw, inner_neg_right, real_inner_self_eq_norm_sq]
  rw [hinner, hav] at hy2
  have hzz : D.pw v z - D.pw v' z = 0 := by rw [hzeq]; ring
  have : 0 < δ * ‖a‖ ^ 2 := by positivity
  linarith [hy2, hz2, hzz, hyge]

/-- Distinct centres have Delaunay cells with disjoint interiors. -/
theorem disjoint_interior_delCell {v v' : Plane} (hne : v ≠ v') :
    Disjoint (interior (D.delCell v)) (interior (D.delCell v')) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  exact hne (D.center_eq_of_mem_interior hz (interior_subset hz'))

/-! ### The weak Delaunay inequality -/

/-- The empty-circle property in the in-circle determinant form used by the
cotangent certificate: for a positively oriented triangle of nearest sites of
`v`, every site of the configuration is outside or on the circumcircle. -/
theorem inCircleDet_nonneg_of_nearestSet {v a b c e : Plane}
    (ha : a ∈ D.nearestSet v) (hb : b ∈ D.nearestSet v) (hc : c ∈ D.nearestSet v)
    (he : e ∈ D.carrier) (hpos : 0 < cross a b c) :
    0 ≤ inCircleDet a b c e := by
  have hav : dist a v = D.nd v := by rw [dist_comm]; exact ha.2
  have hbv : dist b v = D.nd v := by rw [dist_comm]; exact hb.2
  have hcv : dist c v = D.nd v := by rw [dist_comm]; exact hc.2
  have hev : D.nd v ≤ dist e v := by rw [dist_comm]; exact D.nd_le_dist he
  rw [inCircleDet_eq_cross_mul a b c e v (by rw [hav, hbv]) (by rw [hav, hcv])]
  have h1 : dist a v ^ 2 ≤ dist e v ^ 2 := by
    have h0 : 0 ≤ D.nd v := D.nd_nonneg v
    rw [hav]
    nlinarith
  nlinarith

/-! ### Local finiteness of the tiling -/

/-- Only finitely many *distinct* Delaunay cells meet a given closed ball:
each one is the convex hull of a subset of a fixed finite set of sites. -/
theorem finite_delCells_meeting_closedBall (c : Plane) (r : ℝ) :
    {K : Set Plane | ∃ v : Plane, K = D.delCell v ∧ (K ∩ closedBall c r).Nonempty}.Finite := by
  classical
  set F : Finset Plane := D.ballFinset c (r + 2 * D.cov) with hF
  have hsub : {K : Set Plane | ∃ v : Plane, K = D.delCell v ∧ (K ∩ closedBall c r).Nonempty}
      ⊆ (fun s : Finset Plane => convexHull ℝ (s : Set Plane)) '' (F.powerset : Set (Finset Plane)) := by
    rintro K ⟨v, rfl, y, hyK, hyb⟩
    have hfin := D.nearestSet_finite v
    refine ⟨hfin.toFinset, ?_, ?_⟩
    · simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
      intro x hx
      rw [Set.Finite.mem_toFinset] at hx
      -- `x` is a nearest site of `v`, and `v` is within `cov` of `y ∈ closedBall c r`
      have hxv : dist x v = D.nd v := by rw [dist_comm]; exact hx.2
      have hyv : dist y v ≤ D.cov := by
        have := D.delCell_subset_closedBall v hyK
        rwa [mem_closedBall] at this
      have hyc : dist y c ≤ r := by simpa using hyb
      have hndv : D.nd v ≤ D.cov := D.nd_le_cov v
      rw [hF, D.mem_ballFinset]
      refine ⟨hx.1, ?_⟩
      have h1 : dist x c ≤ dist x v + dist v y + dist y c := by
        have := dist_triangle x v y
        have := dist_triangle x y c
        linarith
      have h2 : dist v y = dist y v := dist_comm _ _
      linarith
    · rw [delCell]
      ext x
      simp
  refine Set.Finite.subset ?_ hsub
  exact Set.Finite.image _ (Finset.finite_toSet _)

end DeloneSet

end Conjecture41
