import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Conjecture41.Rotation

set_option autoImplicit false

/-!
# The area of a circular sector

The Euler gate of the periodic Delaunay argument needs the elementary fact that
a circular sector of half-angle `α` and radius `r` has area `α r²`.  This file
proves it by the polar change of variables of Mathlib
(`lintegral_comp_polarCoord_symm` / `lintegral_image_eq_lintegral_abs_det_fderiv_mul`),
first in `ℝ × ℝ` and then, through the volume preserving identification
`planeEquivProd`, in the Euclidean plane `Plane`.

The main result is

* `volume_stdCone_inter_ball`:
  `volume ({x | 0 ≤ sin α * x 0 + cos α * x 1 ∧ 0 ≤ sin α * x 0 - cos α * x 1} ∩ ball 0 r)
      = ENNReal.ofReal (α * r ^ 2)`.
-/

namespace Conjecture41

open MeasureTheory Set Metric
open scoped ENNReal Real

/-! ### The polar computation in `ℝ × ℝ` -/

private lemma lintegral_abs_id_Ioo {r : ℝ} (hr : 0 < r) :
    ∫⁻ x in Ioo (0:ℝ) r, ENNReal.ofReal |x| = ENNReal.ofReal (r ^ 2 / 2) := by
  have h1 : ∀ x ∈ Ioo (0:ℝ) r, ENNReal.ofReal |x| = ENNReal.ofReal x := by
    intro x hx; rw [abs_of_pos hx.1]
  rw [setLIntegral_congr_fun measurableSet_Ioo h1, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
    simp [integral_id]
  · exact (continuous_id.integrableOn_Icc (a := (0:ℝ)) (b := r)).mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using hx.1.le

/-- The area of the open polar sector of radius `r` and half-angle `α`. -/
lemma volume_polarSector {r α : ℝ} (hr : 0 < r) (hα : 0 < α) (hα2 : α < π / 2) :
    volume (polarCoord.symm '' (Ioo 0 r ×ˢ Ioo (-α) α)) = ENNReal.ofReal (α * r ^ 2) := by
  have hsub : (Ioo 0 r ×ˢ Ioo (-α) α) ⊆ polarCoord.target := by
    rintro ⟨s, u⟩ ⟨hs, hu⟩
    refine ⟨hs.1, ?_⟩
    simp only [mem_Ioo] at hu ⊢
    constructor
    · nlinarith [hu.1, Real.pi_gt_three]
    · nlinarith [hu.2, Real.pi_gt_three]
  have hmeas : MeasurableSet (Ioo (0:ℝ) r ×ˢ Ioo (-α) α) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hinj : InjOn polarCoord.symm (Ioo (0:ℝ) r ×ˢ Ioo (-α) α) :=
    polarCoord.symm.injOn.mono hsub
  have key := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hmeas
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt) hinj (fun _ => (1 : ℝ≥0∞))
  simp only [mul_one, lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
    det_fderivPolarCoordSymm, one_mul] at key
  rw [key, Measure.volume_eq_prod, ← Measure.prod_restrict, MeasureTheory.lintegral_prod]
  · simp only [lintegral_const, Measure.restrict_apply, MeasurableSet.univ, univ_inter,
      Real.volume_Ioo]
    rw [lintegral_mul_const' _ _ (by simp), lintegral_abs_id_Ioo hr,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  · exact measurable_fst.abs.ennreal_ofReal.aemeasurable

/-- A line through the origin of `ℝ × ℝ` is Lebesgue null. -/
lemma volume_line_zero {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) :
    volume {q : ℝ × ℝ | a * q.1 + b * q.2 = 0} = 0 := by
  set f : (ℝ × ℝ) →ₗ[ℝ] ℝ := a • (LinearMap.fst ℝ ℝ ℝ) + b • (LinearMap.snd ℝ ℝ ℝ) with hf
  have hset : {q : ℝ × ℝ | a * q.1 + b * q.2 = 0} = (LinearMap.ker f : Set (ℝ × ℝ)) := by
    ext q; simp [hf, LinearMap.mem_ker]
  have hne : LinearMap.ker f ≠ ⊤ := by
    rw [Ne, LinearMap.ker_eq_top]
    intro h0
    rcases h with ha | hb
    · apply ha
      have : f (1, 0) = 0 := by rw [h0]; rfl
      simpa [hf] using this
    · apply hb
      have : f (0, 1) = 0 := by rw [h0]; rfl
      simpa [hf] using this
  rw [hset]
  exact Measure.addHaar_submodule _ _ hne

/-- If `sin x > 0` and `x` lies in `(-π, 3π/2)` then `x ∈ (0, π)`. -/
lemma mem_Ioo_of_sin_pos {x : ℝ} (h1 : -π < x) (h2 : x < 3 * π / 2) (h : 0 < Real.sin x) :
    0 < x ∧ x < π := by
  constructor
  · by_contra hx
    push_neg at hx
    have : Real.sin (-x) ≥ 0 := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [Real.sin_neg] at this
    linarith
  · by_contra hx
    push_neg at hx
    have hpi : (0:ℝ) < π := Real.pi_pos
    have : Real.sin (x - π) ≥ 0 :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at this
    linarith

/-- The standard cone of half-angle `α` intersected with the disc of radius `r`,
described in `ℝ × ℝ`. -/
def stdSectorRR (α r : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 ≤ Real.sin α * q.1 + Real.cos α * q.2 ∧ 0 ≤ Real.sin α * q.1 - Real.cos α * q.2 ∧
    q.1 ^ 2 + q.2 ^ 2 < r ^ 2}

lemma measurableSet_stdSectorRR (α r : ℝ) : MeasurableSet (stdSectorRR α r) := by
  have h1 : MeasurableSet {q : ℝ × ℝ | 0 ≤ Real.sin α * q.1 + Real.cos α * q.2} :=
    measurableSet_le measurable_const
      ((measurable_fst.const_mul _).add (measurable_snd.const_mul _))
  have h2 : MeasurableSet {q : ℝ × ℝ | 0 ≤ Real.sin α * q.1 - Real.cos α * q.2} :=
    measurableSet_le measurable_const
      ((measurable_fst.const_mul _).sub (measurable_snd.const_mul _))
  have h3 : MeasurableSet {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < r ^ 2} :=
    measurableSet_lt ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2))
      measurable_const
  exact (h1.inter (h2.inter h3))

lemma volume_stdSectorRR {r α : ℝ} (hr : 0 < r) (hα : 0 < α) (hα2 : α < π / 2) :
    volume (stdSectorRR α r) = ENNReal.ofReal (α * r ^ 2) := by
  have hsa : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])
  have hca : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα2⟩
  set S := polarCoord.symm '' (Ioo 0 r ×ˢ Ioo (-α) α) with hS
  -- the sector contains the open polar sector
  have hsub : S ⊆ stdSectorRR α r := by
    rintro _ ⟨⟨ρ, φ⟩, ⟨hρ, hφ⟩, rfl⟩
    simp only [mem_Ioo] at hρ hφ
    have hcoord : (polarCoord.symm (ρ, φ)) = (ρ * Real.cos φ, ρ * Real.sin φ) := rfl
    rw [hcoord]
    refine ⟨?_, ?_, ?_⟩
    · have hs : 0 < Real.sin (α + φ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have : Real.sin α * (ρ * Real.cos φ) + Real.cos α * (ρ * Real.sin φ)
          = ρ * Real.sin (α + φ) := by rw [Real.sin_add]; ring
      simp only []
      rw [this]
      exact (mul_pos hρ.1 hs).le
    · have hs : 0 < Real.sin (α - φ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have : Real.sin α * (ρ * Real.cos φ) - Real.cos α * (ρ * Real.sin φ)
          = ρ * Real.sin (α - φ) := by rw [Real.sin_sub]; ring
      simp only []
      rw [this]
      exact (mul_pos hρ.1 hs).le
    · have : (ρ * Real.cos φ) ^ 2 + (ρ * Real.sin φ) ^ 2 = ρ ^ 2 := by
        have := Real.sin_sq_add_cos_sq φ
        nlinarith
      simp only []
      rw [this]
      nlinarith [hρ.1, hρ.2]
  -- and differs from it by two lines
  have hdiff : stdSectorRR α r \ S ⊆
      {q : ℝ × ℝ | Real.sin α * q.1 + Real.cos α * q.2 = 0} ∪
      {q : ℝ × ℝ | Real.sin α * q.1 + (-Real.cos α) * q.2 = 0} := by
    rintro q ⟨⟨hq1, hq2, hq3⟩, hqS⟩
    by_contra hcon
    simp only [mem_union, mem_setOf_eq, not_or] at hcon
    have hA : 0 < Real.sin α * q.1 + Real.cos α * q.2 := lt_of_le_of_ne hq1 (Ne.symm hcon.1)
    have hB : 0 < Real.sin α * q.1 - Real.cos α * q.2 := by
      have := hcon.2
      rcases lt_or_eq_of_le hq2 with h | h
      · exact h
      · exact absurd (by linarith [h] : Real.sin α * q.1 + (-Real.cos α) * q.2 = 0) this
    have hq1pos : 0 < q.1 := by nlinarith
    have hsource : q ∈ polarCoord.source := Or.inl hq1pos
    have htarget : polarCoord q ∈ polarCoord.target := polarCoord.map_source hsource
    have hinv : polarCoord.symm (polarCoord q) = q := polarCoord.left_inv hsource
    set p := polarCoord q with hp
    obtain ⟨hp1, hp2⟩ := htarget
    simp only [mem_Ioi] at hp1
    simp only [mem_Ioo] at hp2
    have hq0 : q.1 = p.1 * Real.cos p.2 := by
      conv_lhs => rw [← hinv]
      rfl
    have hq1' : q.2 = p.1 * Real.sin p.2 := by
      conv_lhs => rw [← hinv]
      rfl
    have hplt : p.1 < r := by
      have : p.1 = Real.sqrt (q.1 ^ 2 + q.2 ^ 2) := rfl
      rw [this]
      have : Real.sqrt (q.1 ^ 2 + q.2 ^ 2) < Real.sqrt (r ^ 2) :=
        Real.sqrt_lt_sqrt (by positivity) hq3
      rwa [Real.sqrt_sq hr.le] at this
    have hAv : Real.sin α * q.1 + Real.cos α * q.2 = p.1 * Real.sin (α + p.2) := by
      rw [hq0, hq1', Real.sin_add]; ring
    have hBv : Real.sin α * q.1 - Real.cos α * q.2 = p.1 * Real.sin (α - p.2) := by
      rw [hq0, hq1', Real.sin_sub]; ring
    have hsA : 0 < Real.sin (α + p.2) := by
      rw [hAv] at hA; nlinarith
    have hsB : 0 < Real.sin (α - p.2) := by
      rw [hBv] at hB; nlinarith
    have h1 := mem_Ioo_of_sin_pos (x := α + p.2) (by linarith [hp2.1])
      (by linarith [hp2.2, Real.pi_pos]) hsA
    have h2 := mem_Ioo_of_sin_pos (x := α - p.2) (by linarith [hp2.2])
      (by linarith [hp2.1, Real.pi_pos]) hsB
    exact hqS ⟨p, ⟨⟨hp1, hplt⟩, ⟨by linarith [h1.1], by linarith [h2.1]⟩⟩, hinv⟩
  have hnull1 : volume {q : ℝ × ℝ | Real.sin α * q.1 + Real.cos α * q.2 = 0} = 0 :=
    volume_line_zero (Or.inl hsa.ne')
  have hnull2 : volume {q : ℝ × ℝ | Real.sin α * q.1 + (-Real.cos α) * q.2 = 0} = 0 :=
    volume_line_zero (Or.inl hsa.ne')
  have hle1 : volume (stdSectorRR α r) ≤ ENNReal.ofReal (α * r ^ 2) := by
    have hcover : stdSectorRR α r ⊆ S ∪
        ({q : ℝ × ℝ | Real.sin α * q.1 + Real.cos α * q.2 = 0} ∪
         {q : ℝ × ℝ | Real.sin α * q.1 + (-Real.cos α) * q.2 = 0}) := by
      intro q hq
      by_cases h : q ∈ S
      · exact Or.inl h
      · exact Or.inr (hdiff ⟨hq, h⟩)
    calc volume (stdSectorRR α r) ≤ _ := measure_mono hcover
      _ ≤ volume S + volume ({q : ℝ × ℝ | Real.sin α * q.1 + Real.cos α * q.2 = 0} ∪
            {q : ℝ × ℝ | Real.sin α * q.1 + (-Real.cos α) * q.2 = 0}) := measure_union_le _ _
      _ ≤ volume S + (volume {q : ℝ × ℝ | Real.sin α * q.1 + Real.cos α * q.2 = 0} +
            volume {q : ℝ × ℝ | Real.sin α * q.1 + (-Real.cos α) * q.2 = 0}) := by
            gcongr; exact measure_union_le _ _
      _ = ENNReal.ofReal (α * r ^ 2) := by
            rw [hnull1, hnull2, volume_polarSector hr hα hα2]; simp
  have hle2 : ENNReal.ofReal (α * r ^ 2) ≤ volume (stdSectorRR α r) := by
    rw [← volume_polarSector hr hα hα2]
    exact measure_mono hsub
  exact le_antisymm hle1 hle2

/-! ### Transfer to the Euclidean plane -/

/-- The volume preserving identification of the Euclidean plane with `ℝ × ℝ`. -/
noncomputable def planeEquivProd : Plane ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

@[simp] lemma planeEquivProd_apply (x : Plane) : planeEquivProd x = (x 0, x 1) := rfl

lemma measurePreserving_planeEquivProd : MeasurePreserving planeEquivProd :=
  (MeasureTheory.volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (ι := Fin 2))

/-- The standard cone of half-angle `α` in the plane, intersected with the ball of
radius `r` around the origin. -/
def stdSector (α r : ℝ) : Set Plane :=
  {x : Plane | 0 ≤ Real.sin α * x 0 + Real.cos α * x 1 ∧
    0 ≤ Real.sin α * x 0 - Real.cos α * x 1} ∩ ball 0 r

lemma stdSector_eq_preimage (α r : ℝ) (hr : 0 < r) :
    stdSector α r = planeEquivProd ⁻¹' stdSectorRR α r := by
  ext x
  simp only [stdSector, stdSectorRR, mem_inter_iff, mem_setOf_eq, mem_preimage,
    planeEquivProd_apply, mem_ball, dist_zero_right]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, ?_⟩
    have := norm_sq_plane x
    nlinarith [norm_nonneg x, h3]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    have hn := norm_sq_plane x
    nlinarith [norm_nonneg x]

/-- **The area of a circular sector**: the standard cone of half-angle `α`
intersected with the disc of radius `r` has area `α r²`. -/
lemma volume_stdSector {r α : ℝ} (hr : 0 < r) (hα : 0 < α) (hα2 : α < π / 2) :
    volume (stdSector α r) = ENNReal.ofReal (α * r ^ 2) := by
  rw [stdSector_eq_preimage α r hr,
    measurePreserving_planeEquivProd.measure_preimage
      (measurableSet_stdSectorRR α r).nullMeasurableSet,
    volume_stdSectorRR hr hα hα2]

end Conjecture41
