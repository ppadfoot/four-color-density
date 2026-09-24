import Conjecture41.TriangleArea

set_option autoImplicit false

/-!
# Half-planes, barycentric coordinates and triangle membership

Elementary planar convexity written directly in terms of the signed doubled
area `cross`, used to build and analyse the fan triangulation of a Delaunay
cell:

* `cross_affine_comb`: `cross a b ·` is affine;
* `convex_leftHalf`, `cross_nonneg_of_mem_convexHull`: the closed half-plane on
  the left of a directed line is convex, so a sign condition on a generating
  set propagates to its convex hull;
* `mem_triangle_of_cross_nonneg`: the barycentric criterion — a point on the
  correct side of the three directed edges of a positively oriented triangle
  lies in the triangle;
* `cross_neg_of_mem_interior`: an affine functional that is nonpositive on a
  set and strictly negative somewhere on it is strictly negative on its
  interior.  This is the tool used to separate the interiors of two fan
  triangles.
-/

namespace Conjecture41

open Set

/-- `cross a b ·` is affine: it commutes with affine combinations. -/
lemma cross_affine_comb (a b x y : Plane) {s t : ℝ} (hst : s + t = 1) :
    cross a b (s • x + t • y) = s * cross a b x + t * cross a b y := by
  have ht : t = 1 - s := by linarith
  subst ht
  simp only [cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The closed half-plane to the left of the directed line from `a` to `b`. -/
def leftHalf (a b : Plane) : Set Plane := {x : Plane | 0 ≤ cross a b x}

lemma convex_leftHalf (a b : Plane) : Convex ℝ (leftHalf a b) := by
  intro x hx y hy s t hs ht hst
  have : cross a b (s • x + t • y) = s * cross a b x + t * cross a b y :=
    cross_affine_comb a b x y hst
  have hx' : 0 ≤ cross a b x := hx
  have hy' : 0 ≤ cross a b y := hy
  show 0 ≤ cross a b (s • x + t • y)
  rw [this]
  positivity

/-- A sign condition on a generating set propagates to its convex hull. -/
lemma cross_nonneg_of_mem_convexHull {a b : Plane} {S : Set Plane}
    (h : ∀ s ∈ S, 0 ≤ cross a b s) {x : Plane} (hx : x ∈ convexHull ℝ S) :
    0 ≤ cross a b x :=
  convexHull_min (fun s hs => h s hs) (convex_leftHalf a b) hx

/-- The three barycentric coordinates of a point with respect to a triangle add
up to the doubled area. -/
lemma cross_bary_sum (a b c x : Plane) :
    cross x b c + cross a x c + cross a b x = cross a b c := by
  simp only [cross]; ring

/-- **Barycentric criterion.**  A point on the nonnegative side of all three
directed edges of a positively oriented triangle lies in the triangle. -/
lemma mem_triangle_of_cross_nonneg {a b c x : Plane} (hD : 0 < cross a b c)
    (h1 : 0 ≤ cross x b c) (h2 : 0 ≤ cross a x c) (h3 : 0 ≤ cross a b x) :
    x ∈ convexHull ℝ ({a, b, c} : Set Plane) := by
  have hD' : cross a b c ≠ 0 := ne_of_gt hD
  have hsum := cross_bary_sum a b c x
  have hkey : cross x b c • a + cross a x c • b + cross a b x • c = (cross a b c) • x := by
    ext i
    fin_cases i
    · show cross x b c * a 0 + cross a x c * b 0 + cross a b x * c 0 = cross a b c * x 0
      simp only [cross]; ring
    · show cross x b c * a 1 + cross a x c * b 1 + cross a b x * c 1 = cross a b c * x 1
      simp only [cross]; ring
  have hx : (cross x b c / cross a b c) • a + (cross a x c / cross a b c) • b
      + (cross a b x / cross a b c) • c = x := by
    have h := congrArg (fun w : Plane => (cross a b c)⁻¹ • w) hkey
    simpa [smul_add, smul_smul, div_eq_inv_mul, inv_smul_smul₀ hD'] using h
  rw [← hx]
  refine mem_convexHull_three (by positivity) (by positivity) (by positivity) ?_
  field_simp
  linarith [hsum]

/-- An affine functional nonpositive on a set and strictly negative at one of
its points is strictly negative on the interior of the set. -/
lemma cross_neg_of_mem_interior {a b : Plane} {T : Set Plane}
    (hT : ∀ y ∈ T, cross a b y ≤ 0) {z : Plane} (hzneg : cross a b z < 0)
    {x : Plane} (hx : x ∈ interior T) : cross a b x < 0 := by
  rcases lt_or_eq_of_le (hT x (interior_subset hx)) with h | h
  · exact h
  exfalso
  have hxz : x ≠ z := by
    intro hxz
    rw [hxz] at h
    linarith
  have hdpos : 0 < dist x z := dist_pos.mpr hxz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  set δ : ℝ := ε / (2 * dist x z) with hδ
  have hδpos : 0 < δ := by positivity
  set y : Plane := (1 + δ) • x + (-δ) • z with hy
  have hdist : dist y x < ε := by
    have : y - x = δ • (x - z) := by
      rw [hy]; module
    have hnorm : dist y x = δ * dist x z := by
      rw [dist_eq_norm, this, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos, ← dist_eq_norm]
    rw [hnorm, hδ]
    rw [div_mul_eq_mul_div, mul_comm]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hyT : y ∈ T := interior_subset (hball (by simpa [Metric.mem_ball] using hdist))
  have hcy : cross a b y = (1 + δ) * cross a b x + (-δ) * cross a b z :=
    cross_affine_comb a b x z (by ring)
  have := hT y hyT
  rw [hcy, ← h] at this
  nlinarith

end Conjecture41
