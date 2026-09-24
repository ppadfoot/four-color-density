import Conjecture41.Fan

set_option autoImplicit false

/-!
# Every finite cocircular set of at least three points is an inscribed polygon

`Fan.lean` triangulates an `InscribedPolygon`, i.e. a family of points on a
circle presented in strictly increasing angular order.  This file produces that
presentation from the data actually available in the Delaunay construction: a
*finite set* `A` of at least three points lying on a common circle.  Sorting
the angular coordinates `circleAngle v` of the points of `A` gives the
required strictly monotone indexing, and the resulting polygon has vertex set
exactly `A`, so its convex hull is the Delaunay cell.

The construction is canonical: it depends only on `v`, `R` and `A`, and
`circleAngle` is translation invariant (`circleAngle_add`), so it is
automatically equivariant under translations of the plane — no choice of orbit
representatives is required.
-/

namespace Conjecture41

open Set

/-- Angular coordinates are translation invariant. -/
lemma circleAngle_add (v x t : Plane) : circleAngle (v + t) (x + t) = circleAngle v x := by
  unfold circleAngle
  congr 1
  simp [PiLp.add_apply]

/-- **Presentation of a finite cocircular set as an inscribed polygon.** -/
theorem exists_inscribedPolygon {v : Plane} {R : ℝ} (hR : 0 < R) (A : Finset Plane)
    (hA : ∀ a ∈ A, dist a v = R) (hcard : 3 ≤ A.card) :
    ∃ P : InscribedPolygon, P.center = v ∧ P.radius = R ∧
      P.verts = (A : Set Plane) ∧ P.last + 1 = A.card := by
  classical
  set n : ℕ := A.card with hn
  set Θ : Finset ℝ := A.image (circleAngle v) with hΘ
  have hinj : Set.InjOn (circleAngle v) (A : Set Plane) := by
    intro a ha b hb hab
    exact circleAngle_injOn hR (hA a ha) (hA b hb) hab
  have hcardΘ : Θ.card = n := by
    rw [hΘ, Finset.card_image_of_injOn hinj, hn]
  set f := Θ.orderIsoOfFin hcardΘ with hf
  have hn0 : 0 < n := by omega
  set angle : ℕ → ℝ := fun i => if h : i < n then (f ⟨i, h⟩ : ℝ) else 0 with hangle
  have hmemΘ : ∀ i : ℕ, ∀ h : i < n, angle i ∈ Θ := by
    intro i h
    simp only [hangle, dif_pos h]
    exact (f ⟨i, h⟩).2
  have hmono : ∀ i j : ℕ, i < j → j ≤ n - 1 → angle i < angle j := by
    intro i j hij hj
    have hjn : j < n := by omega
    have hin : i < n := by omega
    simp only [hangle, dif_pos hin, dif_pos hjn]
    have hlt : (⟨i, hin⟩ : Fin n) < ⟨j, hjn⟩ := hij
    have := f.lt_iff_lt.mpr hlt
    exact this
  have hwin : ∀ i : ℕ, i < n → -Real.pi < angle i ∧ angle i ≤ Real.pi := by
    intro i hi
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp (hmemΘ i hi)
    rw [← hae]
    exact ⟨neg_pi_lt_circleAngle v a, circleAngle_le_pi v a⟩
  have hwindow : angle (n - 1) < angle 0 + 2 * Real.pi := by
    have h1 := (hwin (n - 1) (by omega)).2
    have h2 := (hwin 0 hn0).1
    linarith
  have hverts : (fun i : ℕ => circlePoint v R (angle i)) '' {i : ℕ | i ≤ n - 1}
      = (A : Set Plane) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      simp only [Set.mem_setOf_eq] at hi
      have hin : i < n := by omega
      obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp (hmemΘ i hin)
      show circlePoint v R (angle i) ∈ (A : Set Plane)
      rw [← hae, circlePoint_circleAngle hR (hA a ha)]
      exact ha
    · intro hx
      have hxA : x ∈ A := hx
      have hmem : circleAngle v x ∈ Θ := Finset.mem_image_of_mem _ hxA
      obtain ⟨i, hi⟩ : ∃ i : Fin n, (f i : ℝ) = circleAngle v x := by
        obtain ⟨i, hi⟩ := f.surjective ⟨circleAngle v x, hmem⟩
        exact ⟨i, by rw [hi]⟩
      refine ⟨(i : ℕ), by simp only [Set.mem_setOf_eq]; omega, ?_⟩
      show circlePoint v R (angle (i : ℕ)) = x
      have hival : angle (i : ℕ) = circleAngle v x := by
        simp only [hangle, dif_pos i.isLt]
        rw [← hi]
      rw [hival, circlePoint_circleAngle hR (hA x hxA)]
  have hlastcard : n - 1 + 1 = A.card := by omega
  exact ⟨{ center := v
           radius := R
           radius_pos := hR
           last := n - 1
           two_le := by omega
           angle := angle
           angle_mono := hmono
           window := hwindow }, rfl, rfl, hverts, hlastcard⟩

end Conjecture41
