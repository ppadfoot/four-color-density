import Conjecture41.Cotangent
import Conjecture41.PlaneUtil

set_option autoImplicit false

/-!
# The Lebesgue area of a plane triangle

This file proves the elementary but indispensable measure-theoretic fact

```
volume (convexHull ℝ {a, b, c}) = ENNReal.ofReal (|cross a b c| / 2) ,
```

i.e. the Lebesgue measure of the solid triangle spanned by three points of
`Plane = EuclideanSpace ℝ (Fin 2)` equals half the absolute value of the
signed doubled area `cross` used throughout the cotangent computation.

Mathlib contains no formula for the volume of a simplex, so the statement is
derived here from scratch:

* the standard triangle `stdTri = {x | 0 ≤ x 0, 0 ≤ x 1, x 0 + x 1 ≤ 1}` is
  convex, equals `convexHull ℝ {0, e₀, e₁}`, and has volume `1/2` (computed by
  Fubini on `ℝ × ℝ`, transported through the volume-preserving equivalences
  `EuclideanSpace ℝ (Fin 2) ≃ (Fin 2 → ℝ) ≃ ℝ × ℝ`);
* an arbitrary triangle is the image of `stdTri` under the affine map
  `x ↦ a + x 0 • (b - a) + x 1 • (c - a)`, whose linear part has determinant
  `cross a b c`;
* the Haar behaviour of Lebesgue measure under a linear map and under
  translation finishes the computation.

This is one of the ingredients required by the area gate (`Σ area = L²`) of
the periodic Delaunay construction.
-/

namespace Conjecture41

open MeasureTheory Set

/-! ### The standard triangle -/

/-- The standard (closed) triangle with vertices `0`, `e₀`, `e₁`. -/
def stdTri : Set Plane := {x : Plane | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}

/-- The standard basis vectors of the plane. -/
noncomputable def basisVec (j : Fin 2) : Plane := EuclideanSpace.single j 1

@[simp] lemma basisVec_apply (j i : Fin 2) : basisVec j i = if i = j then 1 else 0 := by
  simp [basisVec, EuclideanSpace.single_apply]

lemma convex_stdTri : Convex ℝ stdTri := by
  rintro x ⟨hx0, hx1, hx2⟩ y ⟨hy0, hy1, hy2⟩ s t hs ht hst
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
    nlinarith [mul_nonneg hs hx0, mul_nonneg ht hy0, mul_nonneg hs hx1, mul_nonneg ht hy1]

/-- Any convex combination of three points lies in their convex hull. -/
lemma mem_convexHull_three {p q r : Plane} {α β γ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hsum : α + β + γ = 1) :
    α • p + β • q + γ • r ∈ convexHull ℝ ({p, q, r} : Set Plane) := by
  have hconv := convex_convexHull ℝ ({p, q, r} : Set Plane)
  have hsub := subset_convexHull ℝ ({p, q, r} : Set Plane)
  have := hconv.sum_mem (t := (Finset.univ : Finset (Fin 3)))
    (w := ![α, β, γ]) (z := ![p, q, r])
    (by intro i _; fin_cases i <;> simpa)
    (by simp [Fin.sum_univ_three]; linarith)
    (by intro i _; fin_cases i <;> exact hsub (by simp))
  simpa [Fin.sum_univ_three, add_assoc] using this

/-- The standard triangle is the convex hull of `0`, `e₀`, `e₁`. -/
lemma stdTri_eq_convexHull :
    stdTri = convexHull ℝ ({0, basisVec 0, basisVec 1} : Set Plane) := by
  apply le_antisymm
  · rintro x ⟨hx0, hx1, hx2⟩
    have hx : x = (1 - x 0 - x 1) • (0 : Plane) + (x 0) • basisVec 0 + (x 1) • basisVec 1 := by
      ext i; fin_cases i <;> simp
    rw [hx]
    exact mem_convexHull_three (by linarith) hx0 hx1 (by ring)
  · refine convexHull_min ?_ convex_stdTri
    rintro y (rfl | rfl | rfl) <;> refine ⟨?_, ?_, ?_⟩ <;> simp

/-! ### The volume of the standard triangle -/

private def prodTri : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

private lemma measurableSet_prodTri : MeasurableSet prodTri := by
  apply MeasurableSet.inter
  · exact measurableSet_le measurable_const measurable_fst
  · apply MeasurableSet.inter
    · exact measurableSet_le measurable_const measurable_snd
    · exact measurableSet_le (measurable_fst.add measurable_snd) measurable_const

private lemma volume_prodTri : volume prodTri = ENNReal.ofReal (1 / 2) := by
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_apply measurableSet_prodTri]
  have hslice : ∀ x : ℝ, volume (Prod.mk x ⁻¹' prodTri)
      = Set.indicator (Set.Icc (0 : ℝ) 1) (fun x => ENNReal.ofReal (1 - x)) x := by
    intro x
    by_cases hx : 0 ≤ x
    · have he : Prod.mk x ⁻¹' prodTri = Set.Icc 0 (1 - x) := by
        ext y
        simp only [prodTri, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Icc, hx, true_and]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
      rw [he, Real.volume_Icc]
      by_cases hx1 : x ≤ 1
      · rw [Set.indicator_of_mem (Set.mem_Icc.2 ⟨hx, hx1⟩)]; ring_nf
      · rw [Set.indicator_of_notMem (by simp only [Set.mem_Icc, not_and]; intro _; linarith),
          ENNReal.ofReal_eq_zero.2 (by linarith)]
    · have he : Prod.mk x ⁻¹' prodTri = ∅ := by
        ext y
        simp only [prodTri, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, -, -⟩; exact hx h1
      rw [he, Set.indicator_of_notMem (by
        simp only [Set.mem_Icc, not_and]; intro h; exact absurd h hx)]
      simp
  simp_rw [hslice]
  have hint : IntegrableOn (fun x : ℝ => 1 - x) (Set.Icc (0 : ℝ) 1) :=
    (continuous_const.sub continuous_id).integrableOn_Icc
  have hae : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), 0 ≤ 1 - x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simp only [Set.mem_Icc] at hx
    linarith [hx.2]
  rw [lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal hint hae]
  congr 1
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
  simp [integral_id]
  norm_num

/-- The standard triangle has area `1/2`. -/
lemma volume_stdTri : volume stdTri = ENNReal.ofReal (1 / 2) := by
  have h1 : stdTri = (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹' (MeasurableEquiv.finTwoArrow ⁻¹' prodTri) := by
    ext x; simp [stdTri, prodTri, MeasurableEquiv.finTwoArrow]
  rw [h1, (PiLp.volume_preserving_ofLp (ι := Fin 2)).measure_preimage
      (MeasurableEquiv.finTwoArrow.measurable measurableSet_prodTri).nullMeasurableSet,
    (volume_preserving_finTwoArrow ℝ).measure_preimage measurableSet_prodTri.nullMeasurableSet,
    volume_prodTri]

/-! ### The affine parametrisation of an arbitrary triangle -/

/-- The linear map sending `e₀ ↦ u`, `e₁ ↦ w`. -/
noncomputable def triLin (u w : Plane) : Plane →ₗ[ℝ] Plane where
  toFun x := x 0 • u + x 1 • w
  map_add' x y := by ext i; fin_cases i <;> simp [PiLp.add_apply, PiLp.smul_apply] <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp [PiLp.smul_apply] <;> ring

@[simp] lemma triLin_apply (u w x : Plane) : triLin u w x = x 0 • u + x 1 • w := rfl

lemma det_triLin (u w : Plane) : LinearMap.det (triLin u w) = u 0 * w 1 - u 1 * w 0 := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, triLin]
  ring

/-- The affine parametrisation of the triangle `a b c` by the standard
triangle. -/
noncomputable def triAff (a b c : Plane) : Plane →ᵃ[ℝ] Plane :=
  AffineMap.mk' (fun x => a + triLin (b - a) (c - a) x) (triLin (b - a) (c - a)) 0
    (by intro p'; simp [add_comm])

@[simp] lemma triAff_apply (a b c x : Plane) :
    triAff a b c x = a + triLin (b - a) (c - a) x := rfl

lemma triAff_image_vertices (a b c : Plane) :
    (triAff a b c) '' ({0, basisVec 0, basisVec 1} : Set Plane) = ({a, b, c} : Set Plane) := by
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  congr 1
  · simp
  congr 1
  · ext i; fin_cases i <;> simp
  · congr 1
    ext i; fin_cases i <;> simp

lemma triangle_eq_image (a b c : Plane) :
    convexHull ℝ ({a, b, c} : Set Plane) = (fun x => a + triLin (b - a) (c - a) x) '' stdTri := by
  rw [stdTri_eq_convexHull, ← triAff_image_vertices a b c,
    ← AffineMap.image_convexHull (triAff a b c)]
  rfl

/-! ### The area formula -/

/-- **Area of a triangle.**  The Lebesgue measure of the solid triangle with
vertices `a`, `b`, `c` is half the absolute value of the signed doubled area
`cross a b c`. -/
theorem volume_triangle (a b c : Plane) :
    volume (convexHull ℝ ({a, b, c} : Set Plane)) = ENNReal.ofReal (|cross a b c| / 2) := by
  rw [triangle_eq_image a b c,
    ← Set.image_image (fun z : Plane => a + z) (triLin (b - a) (c - a)) stdTri,
    Set.image_add_left, measure_preimage_add,
    Measure.addHaar_image_linearMap volume (triLin (b - a) (c - a)) stdTri,
    det_triLin, volume_stdTri]
  have hcross : (b - a) 0 * (c - a) 1 - (b - a) 1 * (c - a) 0 = cross a b c := by
    simp [cross, PiLp.sub_apply]
  rw [hcross, ← ENNReal.ofReal_mul (abs_nonneg _)]
  ring_nf

/-- The real-valued form of the area formula. -/
theorem volume_triangle_toReal (a b c : Plane) :
    (volume (convexHull ℝ ({a, b, c} : Set Plane))).toReal = |cross a b c| / 2 := by
  rw [volume_triangle, ENNReal.toReal_ofReal (by positivity)]

end Conjecture41
