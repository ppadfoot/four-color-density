import Conjecture41.Sector

set_option autoImplicit false

/-!
# The area of a plane cone

Combining the sector computation of `Sector.lean` with the rotations of
`Rotation.lean`, we compute the area of an arbitrary (convex) plane cone
intersected with a disc centred at its apex:

`volume (coneSet u w ∩ ball 0 r) = ENNReal.ofReal (angle u w * r ^ 2 / 2)`

whenever `0 < cross 0 u w`, i.e. whenever `u, w` span a nondegenerate positively
oriented cone.
-/

namespace Conjecture41

open MeasureTheory Set Metric
open scoped ENNReal Real RealInnerProductSpace

lemma inner_plane (x y : Plane) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

lemma inner_dirVec (a b : ℝ) : ⟪dirVec a, dirVec b⟫ = Real.cos (b - a) := by
  rw [inner_plane]
  simp only [dirVec_zero_apply, dirVec_one_apply, Real.cos_sub]
  ring

/-- Every nonzero plane vector is a positive multiple of a unit vector `dirVec a`. -/
theorem exists_dirVec (x : Plane) (hx : x ≠ 0) : ∃ a : ℝ, x = ‖x‖ • dirVec a := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  set c := x 0 / ‖x‖ with hcdef
  set s := x 1 / ‖x‖ with hsdef
  have hnorm := norm_sq_plane x
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    have h : c ^ 2 + s ^ 2 = (x 0 ^ 2 + x 1 ^ 2) / ‖x‖ ^ 2 := by
      rw [hcdef, hsdef]; field_simp
    rw [h, ← hnorm]
    field_simp
  have hc1 : -1 ≤ c := by nlinarith
  have hc2 : c ≤ 1 := by nlinarith
  have hcos : Real.cos (Real.arccos c) = c := Real.cos_arccos hc1 hc2
  have hsin : Real.sin (Real.arccos c) = |s| := by
    rw [Real.sin_arccos, show (1 : ℝ) - c ^ 2 = s ^ 2 by nlinarith, Real.sqrt_sq_eq_abs]
  have hx0 : ‖x‖ * c = x 0 := by rw [hcdef]; field_simp
  have hx1 : ‖x‖ * s = x 1 := by rw [hsdef]; field_simp
  by_cases h : 0 ≤ s
  · refine ⟨Real.arccos c, ?_⟩
    ext i
    fin_cases i
    · show x 0 = ‖x‖ * Real.cos (Real.arccos c)
      rw [hcos, hx0]
    · show x 1 = ‖x‖ * Real.sin (Real.arccos c)
      rw [hsin, abs_of_nonneg h, hx1]
  · push_neg at h
    refine ⟨-Real.arccos c, ?_⟩
    ext i
    fin_cases i
    · show x 0 = ‖x‖ * Real.cos (-Real.arccos c)
      rw [Real.cos_neg, hcos, hx0]
    · show x 1 = ‖x‖ * Real.sin (-Real.arccos c)
      rw [Real.sin_neg, hsin, abs_of_neg h, ← hx1]
      ring

/-! ### Rotations -/

lemma cross_zero_apply (x y : Plane) : cross 0 x y = x 0 * y 1 - x 1 * y 0 := by
  simp only [cross]
  have h0 : ((0 : Plane)) 0 = 0 := rfl
  have h1 : ((0 : Plane)) 1 = 0 := rfl
  rw [h0, h1]; ring

lemma cross_rot (t : ℝ) (x y : Plane) : cross 0 (rot t x) (rot t y) = cross 0 x y := by
  rw [cross_zero_apply, cross_zero_apply, rot_apply_zero, rot_apply_zero, rot_apply_one,
    rot_apply_one]
  linear_combination (x 0 * y 1 - x 1 * y 0) * Real.sin_sq_add_cos_sq t

lemma rot_rot_neg (t : ℝ) (y : Plane) : rot t (rot (-t) y) = y := by
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

lemma rot_dirVec (t u : ℝ) : rot t (dirVec u) = dirVec (u + t) := by
  have := rot_smul_dirVec t 1 u
  simpa using this

/-! ### Cones -/

/-- The convex cone spanned by `u` and `w` (with apex at the origin). -/
def coneSet (u w : Plane) : Set Plane := {x | 0 ≤ cross 0 u x ∧ 0 ≤ cross 0 x w}

lemma cross_smul_left (c : ℝ) (u x : Plane) : cross 0 (c • u) x = c * cross 0 u x := by
  rw [cross_zero_apply, cross_zero_apply]
  show (c * u 0) * x 1 - (c * u 1) * x 0 = _
  ring

lemma cross_smul_right (c : ℝ) (x w : Plane) : cross 0 x (c • w) = c * cross 0 x w := by
  rw [cross_zero_apply, cross_zero_apply]
  show x 0 * (c * w 1) - x 1 * (c * w 0) = _
  ring

lemma coneSet_smul_left {c : ℝ} (hc : 0 < c) (u w : Plane) :
    coneSet (c • u) w = coneSet u w := by
  ext x
  simp only [coneSet, mem_setOf_eq, cross_smul_left]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨nonneg_of_mul_nonneg_right h1 hc, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨mul_nonneg hc.le h1, h2⟩

lemma coneSet_smul_right {c : ℝ} (hc : 0 < c) (u w : Plane) :
    coneSet u (c • w) = coneSet u w := by
  ext x
  simp only [coneSet, mem_setOf_eq, cross_smul_right]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, nonneg_of_mul_nonneg_right h2 hc⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, mul_nonneg hc.le h2⟩

lemma rot_image_coneSet_inter_ball (t : ℝ) (u w : Plane) (r : ℝ) :
    rot t '' (coneSet u w ∩ ball 0 r) = coneSet (rot t u) (rot t w) ∩ ball 0 r := by
  ext y
  simp only [mem_image, mem_inter_iff, coneSet, mem_setOf_eq, mem_ball, dist_zero_right]
  constructor
  · rintro ⟨x, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    exact ⟨⟨by rw [cross_rot]; exact h1, by rw [cross_rot]; exact h2⟩, by rwa [norm_rot]⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨rot (-t) y, ⟨⟨?_, ?_⟩, ?_⟩, rot_rot_neg t y⟩
    · have := cross_rot t u (rot (-t) y)
      rw [rot_rot_neg] at this
      rw [← this]; exact h1
    · have := cross_rot t (rot (-t) y) w
      rw [rot_rot_neg] at this
      rw [← this]; exact h2
    · rw [norm_rot]; exact h3

lemma coneSet_dirVec_inter_ball (α r : ℝ) :
    coneSet (dirVec (-α)) (dirVec α) ∩ ball 0 r = stdSector α r := by
  ext x
  simp only [coneSet, stdSector, mem_inter_iff, mem_setOf_eq, cross_zero_apply,
    dirVec_zero_apply, dirVec_one_apply, Real.cos_neg, Real.sin_neg]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by linarith, by linarith⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by linarith, by linarith⟩, h3⟩

/-- **The area of a plane cone**: for `u, w` spanning a nondegenerate positively
oriented cone, the part of the cone inside the disc of radius `r` around the apex
has area `(angle u w) r² / 2`. -/
theorem volume_coneSet_inter_ball {u w : Plane} (h : 0 < cross 0 u w) {r : ℝ} (hr : 0 < r) :
    volume (coneSet u w ∩ ball 0 r) =
      ENNReal.ofReal (InnerProductGeometry.angle u w * r ^ 2 / 2) := by
  have hu : u ≠ 0 := by
    rintro rfl
    rw [cross_zero_apply] at h
    simp at h
  have hw : w ≠ 0 := by
    rintro rfl
    rw [cross_zero_apply] at h
    simp at h
  have hnu : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw
  obtain ⟨a, ha⟩ := exists_dirVec u hu
  obtain ⟨c, hc⟩ := exists_dirVec w hw
  -- the cone only depends on the directions
  have hcone : coneSet u w = coneSet (dirVec a) (dirVec c) := by
    conv_lhs => rw [ha, hc]
    rw [coneSet_smul_left hnu, coneSet_smul_right hnw]
  -- the sign of the cross product
  have hcross : cross 0 u w = ‖u‖ * ‖w‖ * Real.sin (c - a) := by
    conv_lhs => rw [ha, hc]
    rw [cross_smul_left, cross_smul_right, cross_dirVec]
    ring
  have hsin : 0 < Real.sin (c - a) := by
    rw [hcross] at h
    nlinarith [mul_pos hnu hnw]
  -- the angle
  set θ := InnerProductGeometry.angle u w with hθdef
  have hangle : θ = Real.arccos (Real.cos (c - a)) := by
    rw [hθdef, ha, hc, InnerProductGeometry.angle_smul_left_of_pos _ _ hnu,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hnw, InnerProductGeometry.angle,
      inner_dirVec, norm_dirVec, norm_dirVec]
    norm_num
  have hθ0 : 0 ≤ θ := by rw [hangle]; exact Real.arccos_nonneg _
  have hθpi : θ ≤ π := by rw [hangle]; exact Real.arccos_le_pi _
  have hcosθ : Real.cos θ = Real.cos (c - a) := by
    rw [hangle]; exact Real.cos_arccos (Real.neg_one_le_cos _) (Real.cos_le_one _)
  have hsinθ : Real.sin θ = Real.sin (c - a) := by
    have h1 : Real.sin θ ≥ 0 := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθpi
    have h2 : Real.sin θ ^ 2 = Real.sin (c - a) ^ 2 := by
      have e1 := Real.sin_sq_add_cos_sq θ
      have e2 := Real.sin_sq_add_cos_sq (c - a)
      rw [hcosθ] at e1
      linarith
    nlinarith
  have hθpos : 0 < θ := by
    rcases lt_or_eq_of_le hθ0 with h' | h'
    · exact h'
    · rw [← h'] at hsinθ; simp at hsinθ; linarith
  have hθltpi : θ < π := by
    rcases lt_or_eq_of_le hθpi with h' | h'
    · exact h'
    · rw [h'] at hsinθ; simp at hsinθ; linarith
  -- the second direction is `a + θ`
  have hdir : dirVec c = dirVec (a + θ) := by
    have ec : Real.cos (a + (c - a))
        = Real.cos a * Real.cos (c - a) - Real.sin a * Real.sin (c - a) := Real.cos_add a (c - a)
    have es : Real.sin (a + (c - a))
        = Real.sin a * Real.cos (c - a) + Real.cos a * Real.sin (c - a) := Real.sin_add a (c - a)
    rw [show a + (c - a) = c from by ring] at ec es
    ext i
    fin_cases i
    · show Real.cos c = Real.cos (a + θ)
      rw [Real.cos_add, hcosθ, hsinθ]; exact ec
    · show Real.sin c = Real.sin (a + θ)
      rw [Real.sin_add, hcosθ, hsinθ]; exact es
  -- rotate the cone into standard position
  set t := -(a + θ / 2) with htdef
  have hrot1 : rot t (dirVec a) = dirVec (-(θ / 2)) := by
    rw [rot_dirVec, htdef]; ring_nf
  have hrot2 : rot t (dirVec c) = dirVec (θ / 2) := by
    rw [hdir, rot_dirVec, htdef]; ring_nf
  have hkey : rot t '' (coneSet u w ∩ ball 0 r) = stdSector (θ / 2) r := by
    rw [hcone, rot_image_coneSet_inter_ball, hrot1, hrot2, coneSet_dirVec_inter_ball]
  have := volume_image_rot t (coneSet u w ∩ ball 0 r)
  rw [hkey, volume_stdSector hr (by linarith) (by linarith)] at this
  rw [← this]
  congr 1
  ring

end Conjecture41
