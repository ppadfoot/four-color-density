import Conjecture41.Barycentric

set_option autoImplicit false

/-!
# The interior of a positively oriented triangle

For a positively oriented triangle the interior of the convex hull of the three
vertices is exactly the intersection of the three open half-planes:

```
interior (conv {a, b, c}) = {x | 0 < cross a b x ∧ 0 < cross b c x ∧ 0 < cross c a x} .
```

In particular a positively oriented triangle has nonempty interior (its
centroid is an interior point).  These facts are used to prove that a
full-dimensional Delaunay cell has nonempty interior, hence determines its
centre, and to identify the boundary edges of the triangles.
-/

namespace Conjecture41

open Set

lemma continuous_cross (a b : Plane) : Continuous (fun x : Plane => cross a b x) := by
  unfold cross
  fun_prop

lemma cross_swap_left (a b c : Plane) : cross a b c = -cross b a c := by
  simp only [cross]; ring

lemma triple_set_rotate (a b c : Plane) : ({a, b, c} : Set Plane) = {b, c, a} := by
  ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-- A point in the interior of a positively oriented triangle is strictly to
the left of the first directed edge. -/
lemma cross_pos_of_mem_interior_triangle {a b c x : Plane} (h : 0 < cross a b c)
    (hx : x ∈ interior (convexHull ℝ ({a, b, c} : Set Plane))) : 0 < cross a b x := by
  have hT : ∀ y ∈ convexHull ℝ ({a, b, c} : Set Plane), cross b a y ≤ 0 := by
    intro y hy
    have : 0 ≤ cross a b y := by
      refine cross_nonneg_of_mem_convexHull ?_ hy
      rintro s (rfl | rfl | rfl)
      · simp only [cross]; ring_nf; simp
      · simp only [cross]; ring_nf; simp
      · exact le_of_lt h
    rw [cross_swap_left b a y]
    linarith
  have hzneg : cross b a c < 0 := by rw [cross_swap_left b a c]; linarith
  have := cross_neg_of_mem_interior hT hzneg hx
  rw [cross_swap_left b a x] at this
  linarith

/-- **The interior of a positively oriented triangle.** -/
theorem interior_triangle_eq {a b c : Plane} (h : 0 < cross a b c) :
    interior (convexHull ℝ ({a, b, c} : Set Plane))
      = {x : Plane | 0 < cross a b x ∧ 0 < cross b c x ∧ 0 < cross c a x} := by
  have hbca : cross b c a = cross a b c := (cross_cyclic a b c).symm
  have hcab : cross c a b = cross a b c := by rw [cross_cyclic a b c, cross_cyclic b c a]
  have hrot1 : ({a, b, c} : Set Plane) = {b, c, a} := triple_set_rotate a b c
  have hrot2 : ({b, c, a} : Set Plane) = {c, a, b} := triple_set_rotate b c a
  refine Set.Subset.antisymm (fun x hx => ⟨cross_pos_of_mem_interior_triangle h hx, ?_, ?_⟩) ?_
  · refine cross_pos_of_mem_interior_triangle (by rw [hbca]; exact h) ?_
    rwa [← hrot1]
  · refine cross_pos_of_mem_interior_triangle (by rw [hcab]; exact h) ?_
    rwa [← hrot2, ← hrot1]
  · refine interior_maximal ?_ ?_
    · rintro x ⟨h1, h2, h3⟩
      refine mem_triangle_of_cross_nonneg h ?_ ?_ (le_of_lt h1)
      · rw [cross_cyclic x b c]; exact le_of_lt h2
      · rw [cross_cyclic a x c, cross_cyclic x c a]; exact le_of_lt h3
    · refine IsOpen.inter (isOpen_lt continuous_const (continuous_cross a b)) ?_
      exact IsOpen.inter (isOpen_lt continuous_const (continuous_cross b c))
        (isOpen_lt continuous_const (continuous_cross c a))

/-- A positively oriented triangle has nonempty interior. -/
theorem nonempty_interior_triangle {a b c : Plane} (h : 0 < cross a b c) :
    (interior (convexHull ℝ ({a, b, c} : Set Plane))).Nonempty := by
  refine ⟨(3 : ℝ)⁻¹ • (a + b + c), ?_⟩
  rw [interior_triangle_eq h]
  have hbca : cross b c a = cross a b c := (cross_cyclic a b c).symm
  have hcab : cross c a b = cross a b c := by rw [cross_cyclic a b c, cross_cyclic b c a]
  have key : ∀ p q : Plane, cross p q ((3 : ℝ)⁻¹ • (a + b + c))
      = (cross p q a + cross p q b + cross p q c) / 3 := by
    intro p q
    simp only [cross, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [key]
    have h1 : cross a b a = 0 := by simp only [cross]; ring
    have h2 : cross a b b = 0 := by simp only [cross]; ring
    rw [h1, h2]; linarith
  · rw [key]
    have h1 : cross b c b = 0 := by simp only [cross]; ring
    have h2 : cross b c c = 0 := by simp only [cross]; ring
    rw [h1, h2, hbca]; linarith
  · rw [key]
    have h1 : cross c a c = 0 := by simp only [cross]; ring
    have h2 : cross c a a = 0 := by simp only [cross]; ring
    rw [h1, h2, hcab]; linarith

end Conjecture41
