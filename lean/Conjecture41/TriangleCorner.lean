import Conjecture41.Angle
import Conjecture41.Barycentric

set_option autoImplicit false

/-!
# The corner of a triangle is a sector

Near one of its vertices a nondegenerate triangle coincides with the cone
spanned by the two edges emanating from that vertex.  Combined with
`volume_coneSet_inter_ball` this gives

`volume (convexHull ℝ {p, a, b} ∩ ball p r) = ENNReal.ofReal (∠ a p b * r ^ 2 / 2)`

for all sufficiently small `r`.
-/

namespace Conjecture41

open MeasureTheory Set Metric EuclideanGeometry
open scoped ENNReal Real

lemma cross_translate (a b c v : Plane) : cross (a + v) (b + v) (c + v) = cross a b c := by
  simp only [cross, PiLp.add_apply]
  ring

/-- The barycentric description of a positively oriented triangle. -/
lemma triangle_eq_halfplanes {p a b : Plane} (hD : 0 < cross p a b) :
    convexHull ℝ ({p, a, b} : Set Plane) =
      {x : Plane | 0 ≤ cross p a x ∧ 0 ≤ cross a b x ∧ 0 ≤ cross b p x} := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_, ?_⟩
    · refine cross_nonneg_of_mem_convexHull ?_ hx
      rintro s (rfl | rfl | rfl)
      · exact le_of_eq (by simp only [cross]; ring)
      · exact le_of_eq (by simp only [cross]; ring)
      · exact hD.le
    · refine cross_nonneg_of_mem_convexHull ?_ hx
      rintro s (rfl | rfl | rfl)
      · rw [cross_cyclic, cross_cyclic]; exact hD.le
      · exact le_of_eq (by simp only [cross]; ring)
      · exact le_of_eq (by simp only [cross]; ring)
    · refine cross_nonneg_of_mem_convexHull ?_ hx
      rintro s (rfl | rfl | rfl)
      · exact le_of_eq (by simp only [cross]; ring)
      · rw [cross_cyclic]; exact hD.le
      · exact le_of_eq (by simp only [cross]; ring)
  · rintro ⟨h1, h2, h3⟩
    refine mem_triangle_of_cross_nonneg hD ?_ ?_ h1
    · rw [cross_cyclic]; exact h2
    · rw [cross_cyclic, cross_cyclic]; exact h3

/-- Near the vertex `p` the triangle `p a b` is the cone spanned by its two edges. -/
lemma triangle_inter_ball_eq_cone {p a b : Plane} (hD : 0 < cross p a b) {r : ℝ}
    (hsmall : r * (|b 0 - a 0| + |b 1 - a 1| + 1) ≤ cross p a b) :
    convexHull ℝ ({p, a, b} : Set Plane) ∩ ball p r =
      {x : Plane | 0 ≤ cross p a x ∧ 0 ≤ cross b p x} ∩ ball p r := by
  rw [triangle_eq_halfplanes hD]
  ext x
  simp only [mem_inter_iff, mem_setOf_eq, mem_ball]
  constructor
  · rintro ⟨⟨h1, _, h3⟩, h4⟩; exact ⟨⟨h1, h3⟩, h4⟩
  · rintro ⟨⟨h1, h3⟩, h4⟩
    refine ⟨⟨h1, ?_, h3⟩, h4⟩
    have hpab : cross a b p = cross p a b := by rw [cross_cyclic, cross_cyclic]
    have hdiff : cross a b x - cross a b p
        = (b 0 - a 0) * (x 1 - p 1) - (b 1 - a 1) * (x 0 - p 0) := by
      simp only [cross]; ring
    have hb0 : |x 0 - p 0| ≤ dist x p := abs_coord_sub_le_dist x p 0
    have hb1 : |x 1 - p 1| ≤ dist x p := abs_coord_sub_le_dist x p 1
    have hbound : |cross a b x - cross a b p| ≤
        (|b 0 - a 0| + |b 1 - a 1|) * dist x p := by
      rw [hdiff]
      calc |(b 0 - a 0) * (x 1 - p 1) - (b 1 - a 1) * (x 0 - p 0)|
          ≤ |(b 0 - a 0) * (x 1 - p 1)| + |(b 1 - a 1) * (x 0 - p 0)| := abs_sub _ _
        _ = |b 0 - a 0| * |x 1 - p 1| + |b 1 - a 1| * |x 0 - p 0| := by
            rw [abs_mul, abs_mul]
        _ ≤ |b 0 - a 0| * dist x p + |b 1 - a 1| * dist x p := by
            gcongr
        _ = (|b 0 - a 0| + |b 1 - a 1|) * dist x p := by ring
    have hd : dist x p < r := h4
    have hdn : 0 ≤ dist x p := dist_nonneg
    have hM : 0 ≤ |b 0 - a 0| + |b 1 - a 1| := by positivity
    have : |cross a b x - cross a b p| < cross p a b := by
      calc |cross a b x - cross a b p| ≤ (|b 0 - a 0| + |b 1 - a 1|) * dist x p := hbound
        _ < r * (|b 0 - a 0| + |b 1 - a 1| + 1) := by nlinarith
        _ ≤ cross p a b := hsmall
    have h5 := abs_lt.1 this
    rw [hpab] at h5
    linarith [h5.1]

/-- The corner of the triangle at `p`, in the ball of radius `r`, is a translate of a
cone. -/
lemma preimage_add_triangle_corner (p a b : Plane) (r : ℝ) :
    (fun x : Plane => x + p) ⁻¹' ({x : Plane | 0 ≤ cross p a x ∧ 0 ≤ cross b p x} ∩ ball p r)
      = coneSet (a - p) (b - p) ∩ ball 0 r := by
  ext x
  simp only [mem_preimage, mem_inter_iff, mem_setOf_eq, coneSet, mem_ball, dist_eq_norm]
  have e1 : cross p a (x + p) = cross 0 (a - p) x := by
    have h := cross_translate 0 (a - p) x p
    simpa using h
  have e2 : cross b p (x + p) = cross 0 x (b - p) := by
    have h := cross_translate (b - p) 0 x p
    rw [cross_cyclic (b - p) 0 x] at h
    simpa using h
  rw [e1, e2]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, by simpa using h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, by simpa using h3⟩

/-- **The area of a triangle corner.**  For `r` small enough, the part of the
positively oriented triangle `p a b` inside the ball of radius `r` around `p` has
area `(∠ a p b) r² / 2`. -/
theorem volume_triangle_corner {p a b : Plane} (hD : 0 < cross p a b) {r : ℝ} (hr : 0 < r)
    (hsmall : r * (|b 0 - a 0| + |b 1 - a 1| + 1) ≤ cross p a b) :
    volume (convexHull ℝ ({p, a, b} : Set Plane) ∩ ball p r)
      = ENNReal.ofReal (∠ a p b * r ^ 2 / 2) := by
  have hcross : cross 0 (a - p) (b - p) = cross p a b := by
    have h := cross_translate 0 (a - p) (b - p) p
    simpa using h.symm
  have hangle : ∠ a p b = InnerProductGeometry.angle (a - p) (b - p) := by
    rw [EuclideanGeometry.angle]
    simp [vsub_eq_sub]
  rw [triangle_inter_ball_eq_cone hD hsmall, ← measure_preimage_add_right volume p,
    preimage_add_triangle_corner, volume_coneSet_inter_ball (by rw [hcross]; exact hD) hr, hangle]

end Conjecture41
