import Conjecture41.Definitions

set_option autoImplicit false

/-!
# Coordinate and box utilities for the Euclidean plane

This file collects the elementary coordinate-wise facts about
`Plane = EuclideanSpace ℝ (Fin 2)` used by the periodization argument
(gate G7): comparison of coordinate differences with the Euclidean distance,
axis-parallel boxes, their measurability and area, and the resulting counting
bound for a `1`-separated set inside a box.
-/

namespace Conjecture41

open Metric Set MeasureTheory

/-- A coordinate difference is at most the Euclidean distance. -/
lemma abs_coord_sub_le_dist (x y : Plane) (i : Fin 2) : |x i - y i| ≤ dist x y := by
  simpa [Real.dist_eq] using PiLp.dist_apply_le (p := 2) x y i

/-- Bounding both coordinate differences bounds the Euclidean distance. -/
lemma dist_le_of_coord_le {x y : Plane} {a b : ℝ}
    (h0 : |x 0 - y 0| ≤ a) (h1 : |x 1 - y 1| ≤ b) :
    dist x y ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  apply Real.sqrt_le_sqrt
  have e0 : dist (x.ofLp 0) (y.ofLp 0) = |x 0 - y 0| := rfl
  have e1 : dist (x.ofLp 1) (y.ofLp 1) = |x 1 - y 1| := rfl
  rw [Fin.sum_univ_two, e0, e1]
  have := abs_nonneg (x 0 - y 0)
  have := abs_nonneg (x 1 - y 1)
  nlinarith

/-- An axis-parallel box: the points whose coordinates lie in `s` and `t`. -/
def boxSet (s t : Set ℝ) : Set Plane := {x : Plane | x 0 ∈ s ∧ x 1 ∈ t}

lemma boxSet_eq_preimage (s t : Set ℝ) :
    boxSet s t = (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹' (Set.univ.pi ![s, t]) := by
  ext x
  simp [boxSet, Fin.forall_fin_two]

lemma measurableSet_boxSet {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (boxSet s t) := by
  rw [boxSet_eq_preimage]
  refine MeasurableSet.preimage ?_ (PiLp.volume_preserving_ofLp (ι := Fin 2)).measurable
  exact MeasurableSet.univ_pi (by intro i; fin_cases i <;> simpa)

lemma volume_boxSet {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    volume (boxSet s t) = volume s * volume t := by
  rw [boxSet_eq_preimage,
    (PiLp.volume_preserving_ofLp (ι := Fin 2)).measure_preimage
      (MeasurableSet.univ_pi (by intro i; fin_cases i <;> simpa)).nullMeasurableSet,
    volume_pi_pi]
  simp [Fin.prod_univ_two]

/--
Counting bound in a box.  A `1`-separated finite set contained in a
`w × h` closed box has at most `4 (w+1)(h+1) / π` elements, because the open
half-unit balls around its points are disjoint and lie in the box grown by
`1/2` in every direction.
-/
lemma card_mul_pi_div_four_le_of_box
    (C : FourColorConfig) (T : Finset Plane) (p q w h : ℝ)
    (hw : 0 ≤ w) (hh : 0 ≤ h)
    (hTC : ∀ x ∈ T, x ∈ C.carrier)
    (hbox : ∀ x ∈ T, x 0 ∈ Icc p (p + w) ∧ x 1 ∈ Icc q (q + h)) :
    (T.card : ℝ) * (Real.pi / 4) ≤ (w + 1) * (h + 1) := by
  classical
  set B : Set ℝ := Ioo (p - 1 / 2) (p + w + 1 / 2) with hB
  set B' : Set ℝ := Ioo (q - 1 / 2) (q + h + 1 / 2) with hB'
  -- each half-unit ball is inside the enlarged box
  have hsub : ∀ x ∈ T, ball x (1 / 2) ⊆ boxSet B B' := by
    intro x hx y hy
    obtain ⟨hx0, hx1⟩ := hbox x hx
    have h0 : |y 0 - x 0| < 1 / 2 :=
      lt_of_le_of_lt (abs_coord_sub_le_dist y x 0) (by simpa [dist_comm] using hy)
    have h1 : |y 1 - x 1| < 1 / 2 :=
      lt_of_le_of_lt (abs_coord_sub_le_dist y x 1) (by simpa [dist_comm] using hy)
    rw [abs_lt] at h0 h1
    obtain ⟨ha0, hb0⟩ := hx0
    obtain ⟨ha1, hb1⟩ := hx1
    exact ⟨⟨by linarith [h0.1], by linarith [h0.2]⟩, ⟨by linarith [h1.1], by linarith [h1.2]⟩⟩
  have hdisj : (T : Set Plane).Pairwise
      (Function.onFun (Disjoint) (fun x => ball x (1 / 2))) := by
    intro x hx y hy hxy
    have hsep := uniformlySeparated C (hTC x (by simpa using hx)) (hTC y (by simpa using hy)) hxy
    apply Metric.ball_disjoint_ball
    linarith
  have hvol : ∑ _x ∈ T, volume (ball (0 : Plane) (1 / 2)) ≤ volume (boxSet B B') := by
    have h1 : ∑ x ∈ T, volume (ball x (1 / 2)) = volume (⋃ x ∈ T, ball x (1 / 2)) := by
      refine (measure_biUnion_finset ?_ (fun x _ => measurableSet_ball)).symm
      exact hdisj
    have h2 : (⋃ x ∈ T, ball x (1 / 2)) ⊆ boxSet B B' := Set.iUnion₂_subset hsub
    calc ∑ _x ∈ T, volume (ball (0 : Plane) (1 / 2))
        = ∑ x ∈ T, volume (ball x (1 / 2)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp [Measure.addHaar_ball_center]
      _ = volume (⋃ x ∈ T, ball x (1 / 2)) := h1
      _ ≤ volume (boxSet B B') := measure_mono h2
  rw [Finset.sum_const, nsmul_eq_mul, EuclideanSpace.volume_ball_fin_two,
    volume_boxSet measurableSet_Ioo measurableSet_Ioo, Real.volume_Ioo, Real.volume_Ioo] at hvol
  have e1 : ENNReal.ofReal (p + w + 1 / 2 - (p - 1 / 2)) = ENNReal.ofReal (w + 1) := by
    congr 1; ring
  have e2 : ENNReal.ofReal (q + h + 1 / 2 - (q - 1 / 2)) = ENNReal.ofReal (h + 1) := by
    congr 1; ring
  rw [e1, e2, ← ENNReal.ofReal_mul (by linarith)] at hvol
  have e3 : ENNReal.ofReal (1 / 2 : ℝ) ^ 2 * ENNReal.ofReal Real.pi
      = ENNReal.ofReal (Real.pi / 4) := by
    rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  rw [e3, ← ENNReal.ofReal_natCast T.card, ← ENNReal.ofReal_mul (by positivity)] at hvol
  exact (ENNReal.ofReal_le_ofReal_iff (by nlinarith)).mp hvol

end Conjecture41
