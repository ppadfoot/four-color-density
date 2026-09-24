import Conjecture41.Cotangent
import Conjecture41.Periodic

set_option autoImplicit false

/-!
# Angular coordinates on a circle and the orientation of inscribed triangles

The Delaunay cells produced in `DelaunayCell.lean` are convex hulls of finite
sets of sites lying on a common empty circle.  Triangulating such a cell by a
fan requires a cyclic order of its vertices and the fact that consecutive
vertices, taken in increasing angular order, give *positively oriented*
triangles.  This file supplies exactly that.

* `circlePoint v R t` is the point of the circle of centre `v` and radius `R`
  at angle `t`;
* `exists_circlePoint` parametrises every point of that circle, with angle in
  `(-π, π]`;
* `circlePoint_inj_of_window` shows the parametrisation is injective on any
  half-open window of length `2π`;
* `cross_circlePoint` evaluates the signed doubled area of an inscribed
  triangle as `R² (sin (β-α) + sin (γ-β) - sin (γ-α))`, and
  `cross_circlePoint_pos` shows it is positive whenever `α < β < γ < α + 2π`.

The trigonometric core is the identity
`sin p + sin q - sin (p+q) = 4 sin (p/2) sin (q/2) sin ((p+q)/2)`.
-/

namespace Conjecture41

open Real

/-- The point of the circle of centre `v` and radius `R` at angle `t`. -/
noncomputable def circlePoint (v : Plane) (R t : ℝ) : Plane :=
  v + !₂[R * Real.cos t, R * Real.sin t]

@[simp] lemma circlePoint_zero_apply (v : Plane) (R t : ℝ) :
    circlePoint v R t 0 = v 0 + R * Real.cos t := by simp [circlePoint]

@[simp] lemma circlePoint_one_apply (v : Plane) (R t : ℝ) :
    circlePoint v R t 1 = v 1 + R * Real.sin t := by simp [circlePoint]

lemma dist_circlePoint (v : Plane) {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    dist (circlePoint v R t) v = R := by
  have h : dist (circlePoint v R t) v ^ 2 = R ^ 2 := by
    rw [dist_sq_coords]
    simp only [circlePoint_zero_apply, circlePoint_one_apply]
    have := Real.sin_sq_add_cos_sq t
    nlinarith [Real.sin_sq_add_cos_sq t]
  have h0 : (0 : ℝ) ≤ dist (circlePoint v R t) v := dist_nonneg
  nlinarith

/-- The angular coordinate of `x` seen from `v`, normalised to `(-π, π]`. -/
noncomputable def circleAngle (v x : Plane) : ℝ :=
  (⟨x 0 - v 0, x 1 - v 1⟩ : ℂ).arg

lemma neg_pi_lt_circleAngle (v x : Plane) : -Real.pi < circleAngle v x :=
  (Complex.arg_mem_Ioc _).1

lemma circleAngle_le_pi (v x : Plane) : circleAngle v x ≤ Real.pi :=
  (Complex.arg_mem_Ioc _).2

/-- Every point at distance `R > 0` from `v` is recovered from its angular
coordinate. -/
lemma circlePoint_circleAngle {v x : Plane} {R : ℝ} (hR : 0 < R) (hx : dist x v = R) :
    circlePoint v R (circleAngle v x) = x := by
  symm
  set z : ℂ := ⟨x 0 - v 0, x 1 - v 1⟩ with hz
  have hnorm : ‖z‖ = R := by
    have h2 : ‖z‖ ^ 2 = R ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have hd := dist_sq_coords x v
      rw [hx] at hd
      simp only [hz]
      nlinarith [hd]
    have h0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
    nlinarith
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hnorm
    simp at hnorm
    exact absurd hnorm.symm (ne_of_gt hR)
  show x = circlePoint v R z.arg
  have hc : Real.cos z.arg = (x 0 - v 0) / R := by
    rw [Complex.cos_arg hzne, hnorm]
  have hs : Real.sin z.arg = (x 1 - v 1) / R := by
    rw [Complex.sin_arg z, hnorm]
  have hRne : R ≠ 0 := ne_of_gt hR
  ext i
  fin_cases i
  · show x 0 = circlePoint v R z.arg 0
    rw [circlePoint_zero_apply, hc]
    field_simp
    ring
  · show x 1 = circlePoint v R z.arg 1
    rw [circlePoint_one_apply, hs]
    field_simp
    ring

/-- Every point at distance `R > 0` from `v` is `circlePoint v R t` for an
angle `t` in the window `(-π, π]`. -/
lemma exists_circlePoint {v x : Plane} {R : ℝ} (hR : 0 < R) (hx : dist x v = R) :
    ∃ t : ℝ, -Real.pi < t ∧ t ≤ Real.pi ∧ x = circlePoint v R t :=
  ⟨circleAngle v x, neg_pi_lt_circleAngle v x, circleAngle_le_pi v x,
    (circlePoint_circleAngle hR hx).symm⟩

/-- Distinct angles in a window of length `2π` give distinct points of the
circle. -/
lemma circlePoint_inj_of_window {v : Plane} {R s t : ℝ} (hR : 0 < R)
    (hst : |t - s| < 2 * Real.pi) (h : circlePoint v R s = circlePoint v R t) : s = t := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hc : Real.cos s = Real.cos t := by
    have hh := congrArg (fun y : Plane => y 0) h
    simp only [circlePoint_zero_apply] at hh
    have : R * Real.cos s = R * Real.cos t := by linarith
    exact mul_left_cancel₀ hRne this
  have hs : Real.sin s = Real.sin t := by
    have hh := congrArg (fun y : Plane => y 1) h
    simp only [circlePoint_one_apply] at hh
    have : R * Real.sin s = R * Real.sin t := by linarith
    exact mul_left_cancel₀ hRne this
  have hcos1 : Real.cos (t - s) = 1 := by
    rw [Real.cos_sub, hc, hs]
    nlinarith [Real.sin_sq_add_cos_sq t]
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (t - s)).mp hcos1
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs (by exact_mod_cast hne)
      exact_mod_cast (by exact_mod_cast this : (1 : ℝ) ≤ (|n| : ℤ))
    rw [← hn] at hst
    rw [abs_mul] at hst
    rw [abs_of_pos (by linarith : (0:ℝ) < 2 * Real.pi)] at hst
    nlinarith
  rw [hn0] at hn
  simp at hn
  linarith [hn]

/-! ### The trigonometric core -/

/-- The product form of `sin p + sin q - sin (p + q)`. -/
lemma sin_add_sin_sub_sin_add (p q : ℝ) :
    Real.sin p + Real.sin q - Real.sin (p + q)
      = 4 * Real.sin (p / 2) * Real.sin (q / 2) * Real.sin ((p + q) / 2) := by
  have hp : p = 2 * (p / 2) := by ring
  have hq : q = 2 * (q / 2) := by ring
  have hpq : p + q = 2 * (p / 2 + q / 2) := by ring
  rw [show (p + q) / 2 = p / 2 + q / 2 by ring]
  nth_rewrite 1 [hp]
  nth_rewrite 1 [hq]
  nth_rewrite 1 [hpq]
  rw [Real.sin_two_mul, Real.sin_two_mul, Real.sin_two_mul, Real.sin_add, Real.cos_add]
  linear_combination (-2 * Real.sin (q / 2) * Real.cos (q / 2)) * Real.sin_sq_add_cos_sq (p / 2)
    + (-2 * Real.sin (p / 2) * Real.cos (p / 2)) * Real.sin_sq_add_cos_sq (q / 2)

/-- Positivity of `sin p + sin q - sin (p + q)` on the open triangle
`0 < p`, `0 < q`, `p + q < 2π`. -/
lemma sin_add_sin_sub_sin_add_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p + q < 2 * Real.pi) :
    0 < Real.sin p + Real.sin q - Real.sin (p + q) := by
  rw [sin_add_sin_sub_sin_add]
  have h1 : 0 < Real.sin (p / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h2 : 0 < Real.sin (q / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h3 : 0 < Real.sin ((p + q) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  positivity

/-! ### Orientation of inscribed triangles -/

/-- The signed doubled area of a triangle inscribed in a circle, in angular
coordinates. -/
lemma cross_circlePoint (v : Plane) (R α β γ : ℝ) :
    cross (circlePoint v R α) (circlePoint v R β) (circlePoint v R γ)
      = R ^ 2 * (Real.sin (β - α) + Real.sin (γ - β) - Real.sin (γ - α)) := by
  simp only [cross, circlePoint_zero_apply, circlePoint_one_apply, Real.sin_sub]
  ring

/-- **Inscribed triangles are positively oriented in increasing angular
order.** -/
theorem cross_circlePoint_pos {v : Plane} {R α β γ : ℝ} (hR : 0 < R)
    (h1 : α < β) (h2 : β < γ) (h3 : γ < α + 2 * Real.pi) :
    0 < cross (circlePoint v R α) (circlePoint v R β) (circlePoint v R γ) := by
  rw [cross_circlePoint]
  have hkey : 0 < Real.sin (β - α) + Real.sin (γ - β) - Real.sin ((β - α) + (γ - β)) :=
    sin_add_sin_sub_sin_add_pos (by linarith) (by linarith) (by linarith)
  rw [show (β - α) + (γ - β) = γ - α by ring] at hkey
  positivity

/-- **Cocircular points in increasing angular order form a positively oriented
triangle.**  This is the orientation ingredient of the fan triangulation of a
Delaunay cell: the sites of a Delaunay cell all lie on its empty circle, and
sorting them by `circleAngle` makes every triple taken in increasing order
positively oriented. -/
theorem cross_pos_of_circleAngle_lt {v x y z : Plane} {R : ℝ} (hR : 0 < R)
    (hx : dist x v = R) (hy : dist y v = R) (hz : dist z v = R)
    (h1 : circleAngle v x < circleAngle v y) (h2 : circleAngle v y < circleAngle v z) :
    0 < cross x y z := by
  rw [← circlePoint_circleAngle hR hx, ← circlePoint_circleAngle hR hy,
    ← circlePoint_circleAngle hR hz]
  refine cross_circlePoint_pos hR h1 h2 ?_
  have hxa := neg_pi_lt_circleAngle v x
  have hzb := circleAngle_le_pi v z
  linarith

/-- Cocircular points with distinct angular coordinates are distinct, and
conversely: `circleAngle v` is injective on the circle of centre `v` and
radius `R > 0`. -/
lemma circleAngle_injOn {v : Plane} {R : ℝ} (hR : 0 < R) {x y : Plane}
    (hx : dist x v = R) (hy : dist y v = R) (h : circleAngle v x = circleAngle v y) : x = y := by
  rw [← circlePoint_circleAngle hR hx, ← circlePoint_circleAngle hR hy, h]

end Conjecture41
