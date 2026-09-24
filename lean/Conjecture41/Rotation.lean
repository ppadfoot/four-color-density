import Conjecture41.TriangleArea

set_option autoImplicit false

/-!
# Unit vectors, rotations and their measure invariance

Elementary plane trigonometry used by the angular-area computation of the
Euler gate:

* `dirVec t` is the unit vector of angle `t`;
* `rot t` is the rotation by the angle `t`, realized as the linear map
  `triLin (dirVec t) (perpVec t)` of `TriangleArea.lean`, whose determinant is
  `1`, so Lebesgue measure is invariant under it;
* `cross 0 (dirVec a) (dirVec b) = sin (b - a)`.
-/

namespace Conjecture41

open MeasureTheory Set Metric

/-- The unit vector of angle `t`. -/
noncomputable def dirVec (t : ℝ) : Plane := !₂[Real.cos t, Real.sin t]

/-- The unit vector orthogonal to `dirVec t`, rotated a quarter turn
counterclockwise. -/
noncomputable def perpVec (t : ℝ) : Plane := !₂[-Real.sin t, Real.cos t]

@[simp] lemma dirVec_zero_apply (t : ℝ) : dirVec t 0 = Real.cos t := by simp [dirVec]

@[simp] lemma dirVec_one_apply (t : ℝ) : dirVec t 1 = Real.sin t := by simp [dirVec]

@[simp] lemma perpVec_zero_apply (t : ℝ) : perpVec t 0 = -Real.sin t := by simp [perpVec]

@[simp] lemma perpVec_one_apply (t : ℝ) : perpVec t 1 = Real.cos t := by simp [perpVec]

lemma norm_sq_plane (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, sq_abs]

lemma norm_dirVec (t : ℝ) : ‖dirVec t‖ = 1 := by
  have h : ‖dirVec t‖ ^ 2 = 1 := by
    rw [norm_sq_plane]
    simp [dirVec]
  nlinarith [norm_nonneg (dirVec t), h]

lemma cross_dirVec (a b : ℝ) : cross 0 (dirVec a) (dirVec b) = Real.sin (b - a) := by
  simp only [cross, dirVec_zero_apply, dirVec_one_apply, Real.sin_sub]
  have h0 : ((0 : Plane)) 0 = 0 := rfl
  have h1 : ((0 : Plane)) 1 = 0 := rfl
  rw [h0, h1]
  ring

/-- The rotation by the angle `t`. -/
noncomputable def rot (t : ℝ) : Plane →ₗ[ℝ] Plane := triLin (dirVec t) (perpVec t)

lemma rot_apply_zero (t : ℝ) (x : Plane) :
    rot t x 0 = x 0 * Real.cos t - x 1 * Real.sin t := by
  simp only [rot, triLin_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    dirVec_zero_apply, perpVec_zero_apply]
  ring

lemma rot_apply_one (t : ℝ) (x : Plane) :
    rot t x 1 = x 0 * Real.sin t + x 1 * Real.cos t := by
  simp only [rot, triLin_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    dirVec_one_apply, perpVec_one_apply]

lemma det_rot (t : ℝ) : LinearMap.det (rot t) = 1 := by
  rw [rot, det_triLin]
  simp only [dirVec_zero_apply, dirVec_one_apply, perpVec_zero_apply, perpVec_one_apply]
  nlinarith [Real.sin_sq_add_cos_sq t]

lemma norm_rot (t : ℝ) (x : Plane) : ‖rot t x‖ = ‖x‖ := by
  have h : ‖rot t x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_plane, norm_sq_plane, rot_apply_zero, rot_apply_one]
    nlinarith [Real.sin_sq_add_cos_sq t]
  have h1 : (0 : ℝ) ≤ ‖rot t x‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
  nlinarith

lemma rot_smul_dirVec (t s u : ℝ) : rot t (s • dirVec u) = s • dirVec (u + t) := by
  ext i
  fin_cases i
  · show rot t (s • dirVec u) 0 = (s • dirVec (u + t)) 0
    rw [rot_apply_zero]
    simp only [PiLp.smul_apply, dirVec_zero_apply, dirVec_one_apply, smul_eq_mul,
      Real.cos_add]
    ring
  · show rot t (s • dirVec u) 1 = (s • dirVec (u + t)) 1
    rw [rot_apply_one]
    simp only [PiLp.smul_apply, dirVec_zero_apply, dirVec_one_apply, smul_eq_mul,
      Real.sin_add]
    ring

/-- Rotations preserve Lebesgue measure. -/
lemma volume_image_rot (t : ℝ) (s : Set Plane) : volume (rot t '' s) = volume s := by
  rw [Measure.addHaar_image_linearMap, det_rot]
  simp

lemma rot_image_ball (t : ℝ) (r : ℝ) :
    rot t '' (closedBall (0 : Plane) r) = closedBall (0 : Plane) r := by
  ext y
  simp only [Set.mem_image, mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [norm_rot]
  · intro hy
    refine ⟨rot (-t) y, ?_, ?_⟩
    · rwa [norm_rot]
    · have h : rot t (rot (-t) y) = y := by
        ext i
        fin_cases i
        · show rot t (rot (-t) y) 0 = y 0
          rw [rot_apply_zero, rot_apply_zero, rot_apply_one]
          simp only [Real.cos_neg, Real.sin_neg]
          linear_combination (y 0) * Real.sin_sq_add_cos_sq t
        · show rot t (rot (-t) y) 1 = y 1
          rw [rot_apply_one, rot_apply_zero, rot_apply_one]
          simp only [Real.cos_neg, Real.sin_neg]
          linear_combination (y 1) * Real.sin_sq_add_cos_sq t
      exact h

end Conjecture41
