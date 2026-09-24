import Conjecture41.Barycentric
import Conjecture41.InscribedOrientation

set_option autoImplicit false

/-!
# The fan triangulation of a convex polygon inscribed in a circle

A Delaunay cell is the convex hull of the finitely many sites lying on its
empty circumcircle.  Sorting those sites by their angular coordinate gives an
`InscribedPolygon`, and this file proves that the *fan* of triangles

```
  T i = conv {vert 0, vert i, vert (i+1)} ,   1 ≤ i < last
```

triangulates it:

* `InscribedPolygon.tri_subset_poly` — each fan triangle lies in the polygon;
* `InscribedPolygon.exists_mem_tri` — the fan triangles cover the polygon;
* `InscribedPolygon.poly_eq_iUnion_tri` — hence the polygon is exactly their
  union;
* `InscribedPolygon.disjoint_interior_tri` — distinct fan triangles have
  disjoint interiors;
* `InscribedPolygon.cross_tri_pos` — each fan triangle is positively oriented.

The proof is elementary and self-contained.  Every vertex of the polygon lies
on a circle, so `cross_pos_of_circleAngle_lt` gives the sign of the doubled
area of any triple of vertices taken in increasing angular order; the two
consequences used are that every directed edge `vert i → vert (i+1)` (and the
closing edge `vert last → vert 0`) has the whole polygon on its left, and that
the rays `vert 0 → vert m` are angularly monotone.  A discrete intermediate
value argument on `m ↦ cross (vert 0) (vert m) p` then locates the fan triangle
containing a given point `p`, and the barycentric criterion
`mem_triangle_of_cross_nonneg` proves membership.
-/

namespace Conjecture41

open Set

/-- A convex polygon inscribed in a circle, presented by the strictly
increasing angular coordinates of its vertices inside a window of length
`2π`. -/
structure InscribedPolygon where
  /-- Centre of the circumscribed circle. -/
  center : Plane
  /-- Radius of the circumscribed circle. -/
  radius : ℝ
  radius_pos : 0 < radius
  /-- Index of the last vertex; the polygon has `last + 1 ≥ 3` vertices. -/
  last : ℕ
  two_le : 2 ≤ last
  /-- Angular coordinate of each vertex. -/
  angle : ℕ → ℝ
  angle_mono : ∀ i j : ℕ, i < j → j ≤ last → angle i < angle j
  window : angle last < angle 0 + 2 * Real.pi

namespace InscribedPolygon

/-- Degenerate triples have vanishing signed area. -/
lemma cross_self_last (a b : Plane) : cross a b b = 0 := by simp only [cross]; ring

lemma cross_self_mid (a b : Plane) : cross a b a = 0 := by simp only [cross]; ring

/-- Reversing the first two arguments of `cross` changes the sign. -/
lemma cross_swap12 (a b c : Plane) : cross a b c = -cross b a c := by
  simp only [cross]; ring

variable (P : InscribedPolygon)

/-- The `i`-th vertex. -/
noncomputable def vert (i : ℕ) : Plane := circlePoint P.center P.radius (P.angle i)

/-- The set of vertices. -/
noncomputable def verts : Set Plane := P.vert '' {i : ℕ | i ≤ P.last}

/-- The polygon: the convex hull of the vertices. -/
noncomputable def poly : Set Plane := convexHull ℝ P.verts

/-- The `i`-th triangle of the fan based at `vert 0`. -/
noncomputable def tri (i : ℕ) : Set Plane :=
  convexHull ℝ ({P.vert 0, P.vert i, P.vert (i + 1)} : Set Plane)

lemma dist_vert (i : ℕ) : dist (P.vert i) P.center = P.radius :=
  dist_circlePoint _ (le_of_lt P.radius_pos) _

lemma vert_shift (i : ℕ) :
    P.vert i = circlePoint P.center P.radius (P.angle i + 2 * Real.pi) := by
  unfold vert circlePoint
  simp [Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma angle_le_last {i : ℕ} (hi : i ≤ P.last) : P.angle i ≤ P.angle P.last := by
  rcases eq_or_lt_of_le hi with h | h
  · rw [h]
  · exact le_of_lt (P.angle_mono i P.last h le_rfl)

lemma angle_zero_le {i : ℕ} (hi : i ≤ P.last) : P.angle 0 ≤ P.angle i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · rw [h]
  · exact le_of_lt (P.angle_mono 0 i h hi)

/-- Three vertices in increasing index order form a positively oriented
triangle. -/
lemma cross_vert_pos {i j l : ℕ} (hij : i < j) (hjl : j < l) (hl : l ≤ P.last) :
    0 < cross (P.vert i) (P.vert j) (P.vert l) := by
  have hi : i ≤ P.last := le_of_lt (lt_of_lt_of_le hij (le_of_lt (lt_of_lt_of_le hjl hl)))
  have hj : j ≤ P.last := le_of_lt (lt_of_lt_of_le hjl hl)
  refine cross_circlePoint_pos P.radius_pos (P.angle_mono i j hij hj)
    (P.angle_mono j l hjl hl) ?_
  have h1 : P.angle l ≤ P.angle P.last := P.angle_le_last hl
  have h2 : P.angle 0 ≤ P.angle i := P.angle_zero_le hi
  have := P.window
  linarith

/-- The wrapped version: `vert m` with `m < i` lies strictly to the left of the
directed line `vert i → vert j` when `i < j`. -/
lemma cross_vert_wrap {i j m : ℕ} (hij : i < j) (hj : j ≤ P.last) (hmi : m < i) :
    0 < cross (P.vert i) (P.vert j) (P.vert m) := by
  have hi : i ≤ P.last := le_of_lt (lt_of_lt_of_le hij hj)
  have hm : m ≤ P.last := le_of_lt (lt_of_lt_of_le hmi hi)
  rw [vert_shift P m]
  refine cross_circlePoint_pos P.radius_pos (P.angle_mono i j hij hj) ?_ ?_
  · have h1 : P.angle j ≤ P.angle P.last := P.angle_le_last hj
    have h2 : P.angle 0 ≤ P.angle m := P.angle_zero_le hm
    have := P.window
    linarith
  · have := P.angle_mono m i hmi hi
    linarith

/-- Every vertex is weakly to the left of the directed edge
`vert i → vert (i+1)`. -/
lemma cross_edge_vert_nonneg {i : ℕ} (hi : i < P.last) {m : ℕ} (hm : m ≤ P.last) :
    0 ≤ cross (P.vert i) (P.vert (i + 1)) (P.vert m) := by
  rcases lt_trichotomy m i with h | h | h
  · exact le_of_lt (P.cross_vert_wrap (Nat.lt_succ_self i) hi h)
  · subst h
    rw [cross_self_mid]
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h1 | h1
    · rw [← h1, cross_self_last]
    · exact le_of_lt (P.cross_vert_pos (Nat.lt_succ_self i) h1 hm)

/-- Every vertex is weakly to the left of the closing edge
`vert last → vert 0`. -/
lemma cross_close_vert_nonneg {m : ℕ} (hm : m ≤ P.last) :
    0 ≤ cross (P.vert P.last) (P.vert 0) (P.vert m) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    rw [cross_self_last]
  rcases eq_or_lt_of_le hm with h1 | h1
  · rw [h1, cross_self_mid]
  refine le_of_lt ?_
  rw [vert_shift P 0, vert_shift P m]
  refine cross_circlePoint_pos P.radius_pos P.window ?_ ?_
  · have := P.angle_mono 0 m h hm
    linarith
  · linarith [P.angle_le_last hm, h1, P.angle_mono m P.last h1 le_rfl]

/-- The whole polygon is weakly to the left of each directed edge. -/
lemma cross_edge_nonneg {i : ℕ} (hi : i < P.last) {p : Plane} (hp : p ∈ P.poly) :
    0 ≤ cross (P.vert i) (P.vert (i + 1)) p := by
  refine cross_nonneg_of_mem_convexHull ?_ hp
  rintro s ⟨m, hm, rfl⟩
  exact P.cross_edge_vert_nonneg hi hm

/-- The whole polygon is weakly to the left of the closing edge. -/
lemma cross_close_nonneg {p : Plane} (hp : p ∈ P.poly) :
    0 ≤ cross (P.vert P.last) (P.vert 0) p := by
  refine cross_nonneg_of_mem_convexHull ?_ hp
  rintro s ⟨m, hm, rfl⟩
  exact P.cross_close_vert_nonneg hm

/-- Each fan triangle is positively oriented. -/
lemma cross_tri_pos {i : ℕ} (hi : 1 ≤ i) (hlt : i < P.last) :
    0 < cross (P.vert 0) (P.vert i) (P.vert (i + 1)) :=
  P.cross_vert_pos hi (Nat.lt_succ_self i) hlt

lemma tri_subset_poly {i : ℕ} (hlt : i < P.last) : P.tri i ⊆ P.poly := by
  refine convexHull_mono ?_
  rintro y (rfl | rfl | rfl)
  · exact ⟨0, Nat.zero_le _, rfl⟩
  · exact ⟨i, le_of_lt hlt, rfl⟩
  · exact ⟨i + 1, hlt, rfl⟩

/-- **The fan covers the polygon.** -/
theorem exists_mem_tri {p : Plane} (hp : p ∈ P.poly) :
    ∃ i : ℕ, 1 ≤ i ∧ i < P.last ∧ p ∈ P.tri i := by
  classical
  set d : ℕ → ℝ := fun m => cross (P.vert 0) (P.vert m) p with hdef
  have key : ∀ m : ℕ, d m = cross (P.vert 0) (P.vert m) p := fun _ => rfl
  have hlast0 : 0 < P.last := lt_of_lt_of_le (by norm_num) P.two_le
  have hd1 : 0 ≤ d 1 := by
    rw [key]
    exact P.cross_edge_nonneg (i := 0) hlast0 hp
  have hdlast : d P.last ≤ 0 := by
    have h := P.cross_close_nonneg hp
    rw [cross_swap12 (P.vert P.last) (P.vert 0) p] at h
    rw [key]
    linarith
  have hIVT : ∃ i : ℕ, 1 ≤ i ∧ i < P.last ∧ 0 ≤ d i ∧ d (i + 1) ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ m : ℕ, 2 ≤ m → m ≤ P.last → 0 < d m := by
      intro m hm
      induction m with
      | zero => omega
      | succ n ih =>
        intro hle
        rcases Nat.lt_or_ge n 2 with hn | hn
        · have hn1 : n = 1 := by omega
          subst hn1
          exact hcon 1 le_rfl (by omega) hd1
        · exact hcon n (by omega) (by omega) (le_of_lt (ih hn (by omega)))
    have := hall P.last P.two_le le_rfl
    linarith
  obtain ⟨i, hi1, hi2, hdi, hdi1⟩ := hIVT
  rw [key] at hdi hdi1
  refine ⟨i, hi1, hi2, ?_⟩
  refine mem_triangle_of_cross_nonneg (P.cross_tri_pos hi1 hi2) ?_ ?_ hdi
  · have h := P.cross_edge_nonneg (i := i) hi2 hp
    rw [cross_cyclic (P.vert i) (P.vert (i + 1)) p,
      cross_cyclic (P.vert (i + 1)) p (P.vert i)] at h
    exact h
  · rw [cross_swap (P.vert 0) p (P.vert (i + 1))]
    linarith

/-- The polygon is exactly the union of the fan triangles. -/
theorem poly_eq_iUnion_tri :
    P.poly = ⋃ i ∈ Finset.Ico 1 P.last, P.tri i := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨i, hi1, hi2, hmem⟩ := P.exists_mem_tri hp
    exact Set.mem_biUnion (Finset.mem_Ico.mpr ⟨hi1, hi2⟩) hmem
  · refine Set.iUnion₂_subset ?_
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact P.tri_subset_poly hi.2

/-- **Distinct fan triangles have disjoint interiors.** -/
theorem disjoint_interior_tri {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hj : j < P.last) :
    Disjoint (interior (P.tri i)) (interior (P.tri j)) := by
  have hilt : i < P.last := lt_trans hij hj
  -- the separating functional
  have hpos : 0 < cross (P.vert (i + 1)) (P.vert 0) (P.vert i) := by
    rw [vert_shift P 0, vert_shift P i]
    refine cross_circlePoint_pos P.radius_pos ?_ ?_ ?_
    · have h1 : P.angle (i + 1) ≤ P.angle P.last := P.angle_le_last hilt
      have := P.window
      linarith
    · have := P.angle_mono 0 i hi (le_of_lt hilt)
      linarith
    · have := P.angle_mono i (i + 1) (Nat.lt_succ_self i) hilt
      linarith
  have hTi : ∀ y ∈ P.tri i, cross (P.vert 0) (P.vert (i + 1)) y ≤ 0 := by
    intro y hy
    have h : 0 ≤ cross (P.vert (i + 1)) (P.vert 0) y := by
      refine cross_nonneg_of_mem_convexHull ?_ hy
      rintro s (rfl | rfl | rfl)
      · rw [cross_self_last]
      · exact le_of_lt hpos
      · rw [cross_self_mid]
    rw [cross_swap12 (P.vert 0) (P.vert (i + 1)) y]
    linarith
  have hzneg : cross (P.vert 0) (P.vert (i + 1)) (P.vert i) < 0 := by
    rw [cross_swap12 (P.vert 0) (P.vert (i + 1)) (P.vert i)]
    linarith
  have hTj : ∀ y ∈ P.tri j, 0 ≤ cross (P.vert 0) (P.vert (i + 1)) y := by
    intro y hy
    refine cross_nonneg_of_mem_convexHull ?_ hy
    rintro s (rfl | rfl | rfl)
    · rw [cross_self_mid]
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hij) with h | h
      · rw [← h, cross_self_last]
      · exact le_of_lt (P.cross_vert_pos (Nat.succ_pos i) h (le_of_lt hj))
    · exact le_of_lt (P.cross_vert_pos (Nat.succ_pos i) (by omega) hj)
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 : cross (P.vert 0) (P.vert (i + 1)) x < 0 :=
    cross_neg_of_mem_interior hTi hzneg hx
  have h2 : 0 ≤ cross (P.vert 0) (P.vert (i + 1)) x := hTj x (interior_subset hx')
  linarith

end InscribedPolygon

end Conjecture41
