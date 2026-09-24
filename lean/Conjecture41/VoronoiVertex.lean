import Mathlib.Analysis.Convex.KreinMilman
import Conjecture41.DelaunayTiling

set_option autoImplicit false

/-!
# Voronoi vertices and nondegenerate Delaunay cells at every site

This file proves that **every site of a Delone set is a vertex of a
nondegenerate (two-dimensional) Delaunay cell**.

The Voronoi cell of a site is compact, convex and has nonempty interior, so by
the Krein--Milman theorem it has an extreme point `v` — a Voronoi vertex.  At
such a vertex, at least three nearest sites occur and they cannot all be
collinear with the given site: otherwise all the *active* constraints of the
Voronoi cell at `v` would be orthogonal to a common direction `u`, and `v`
could be moved by `± t u` inside the cell for a small `t`, contradicting
extremality (the finitely many inactive constraints are strict, and by the
redundancy result of `VoronoiPolygon.lean` only finitely many constraints
matter).

The conclusion `cross x y₁ y₂ ≠ 0` is exactly nondegeneracy of the triangle
`x y₁ y₂` of the Delaunay cell centred at `v`, all of whose vertices are
sites lying on the empty circle of centre `v`.  Together with
`inCircleDet_nonneg_of_nearestSet` this produces genuine weak Delaunay
triangles at every site.

This is gate G5d (vertex-orbit part) of the formalization ledger.
-/

namespace Conjecture41

open Metric Set

namespace DeloneSet

variable (D : DeloneSet)

/-- A point of the Voronoi cell of a site has that site among its nearest
sites. -/
lemma mem_nearestSet_of_mem_cell {x v : Plane} (hx : x ∈ D.carrier) (hv : v ∈ D.cell x) :
    x ∈ D.nearestSet v := by
  refine ⟨hx, le_antisymm ?_ (D.nd_le_dist hx)⟩
  exact (Metric.le_infDist D.nonempty).mpr (fun y hy => hv y hy)

/-- If a direction is orthogonal to all active constraints at a point `v` of
the Voronoi cell of `x`, then `v` can be moved in that direction without
leaving the cell. -/
lemma exists_shift_mem_cell {x v u : Plane} (hx : x ∈ D.carrier) (hv : v ∈ D.cell x)
    (hu : ∀ y ∈ D.nearestSet v, (inner ℝ u (y - x) : ℝ) = 0) :
    ∃ t : ℝ, 0 < t ∧ v + t • u ∈ D.cell x ∧ v - t • u ∈ D.cell x := by
  classical
  have hvx : dist v x = D.nd v := (D.mem_nearestSet_of_mem_cell hx hv).2
  set S : Finset Plane := D.ballFinset x (3 * D.cov) with hS
  set S2 : Finset Plane := S.filter (fun y => dist v y ≠ D.nd v) with hS2
  set M : ℝ := (∑ y ∈ S, |(inner ℝ u (y - x) : ℝ)|) + 1 with hM
  have hMpos : 0 < M := by
    have h0 : 0 ≤ ∑ y ∈ S, |(inner ℝ u (y - x) : ℝ)| :=
      Finset.sum_nonneg fun y _ => abs_nonneg _
    rw [hM]; linarith
  have hMle : ∀ y ∈ S, |(inner ℝ u (y - x) : ℝ)| ≤ M := by
    intro y hy
    have h1 : |(inner ℝ u (y - x) : ℝ)| ≤ ∑ w ∈ S, |(inner ℝ u (w - x) : ℝ)| :=
      Finset.single_le_sum (f := fun w => |(inner ℝ u (w - x) : ℝ)|)
        (fun w _ => abs_nonneg _) hy
    rw [hM]; linarith
  set δ : ℝ := if h : S2.Nonempty then S2.inf' h (fun y => dist v y ^ 2 - D.nd v ^ 2) else 1
    with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    split_ifs with h
    · rw [Finset.lt_inf'_iff]
      intro y hy
      rw [hS2, Finset.mem_filter] at hy
      have hyc : y ∈ D.carrier := ((D.mem_ballFinset).mp hy.1).1
      have h1 : D.nd v ≤ dist v y := D.nd_le_dist hyc
      have h2 : D.nd v < dist v y := lt_of_le_of_ne h1 (fun h' => hy.2 h'.symm)
      have h3 : 0 ≤ D.nd v := D.nd_nonneg v
      nlinarith
    · norm_num
  have hδle : ∀ y ∈ S2, δ ≤ dist v y ^ 2 - D.nd v ^ 2 := by
    intro y hy
    rw [hδ, dif_pos ⟨y, hy⟩]
    exact Finset.inf'_le _ hy
  refine ⟨δ / (4 * M), by positivity, ?_, ?_⟩
  · set t : ℝ := δ / (4 * M) with ht
    have htM : 2 * t * M ≤ δ / 2 := by
      have hMne : M ≠ 0 := ne_of_gt hMpos
      have heq : 2 * t * M = δ / 2 := by rw [ht]; field_simp; ring
      rw [heq]
    refine D.mem_cell_of_near_constraints _ ?_
    intro y hyc hxy
    have hyS : y ∈ S := by
      rw [hS, D.mem_ballFinset]
      exact ⟨hyc, by rwa [dist_comm]⟩
    have hkey := dist_sq_shift v u y x t
    by_cases hact : dist v y = D.nd v
    · have h1 : (inner ℝ u (y - x) : ℝ) = 0 := hu y ⟨hyc, hact⟩
      have h2 : dist v x ^ 2 - dist v y ^ 2 = 0 := by rw [hvx, hact]; ring
      have : dist (v + t • u) x ^ 2 - dist (v + t • u) y ^ 2 = 0 := by
        rw [hkey, h1, h2]; ring
      nlinarith [dist_nonneg (x := v + t • u) (y := x), dist_nonneg (x := v + t • u) (y := y)]
    · have hyS2 : y ∈ S2 := by rw [hS2, Finset.mem_filter]; exact ⟨hyS, hact⟩
      have h1 : δ ≤ dist v y ^ 2 - D.nd v ^ 2 := hδle y hyS2
      have h2 : |(inner ℝ u (y - x) : ℝ)| ≤ M := hMle y hyS
      have h3 : (inner ℝ u (y - x) : ℝ) ≤ M := le_trans (le_abs_self _) h2
      have h4 : dist (v + t • u) x ^ 2 - dist (v + t • u) y ^ 2 ≤ 0 := by
        rw [hkey, hvx]
        have htpos : 0 < t := by rw [ht]; positivity
        nlinarith
      nlinarith [dist_nonneg (x := v + t • u) (y := x), dist_nonneg (x := v + t • u) (y := y)]
  · set t : ℝ := δ / (4 * M) with ht
    have htM : 2 * t * M ≤ δ / 2 := by
      have hMne : M ≠ 0 := ne_of_gt hMpos
      have heq : 2 * t * M = δ / 2 := by rw [ht]; field_simp; ring
      rw [heq]
    refine D.mem_cell_of_near_constraints _ ?_
    intro y hyc hxy
    have hyS : y ∈ S := by
      rw [hS, D.mem_ballFinset]
      exact ⟨hyc, by rwa [dist_comm]⟩
    have hrw : v - t • u = v + (-t) • u := by
      rw [neg_smul]; abel
    have hkey := dist_sq_shift v u y x (-t)
    rw [← hrw] at hkey
    by_cases hact : dist v y = D.nd v
    · have h1 : (inner ℝ u (y - x) : ℝ) = 0 := hu y ⟨hyc, hact⟩
      have h2 : dist v x ^ 2 - dist v y ^ 2 = 0 := by rw [hvx, hact]; ring
      have : dist (v - t • u) x ^ 2 - dist (v - t • u) y ^ 2 = 0 := by
        rw [hkey, h1, h2]; ring
      nlinarith [dist_nonneg (x := v - t • u) (y := x), dist_nonneg (x := v - t • u) (y := y)]
    · have hyS2 : y ∈ S2 := by rw [hS2, Finset.mem_filter]; exact ⟨hyS, hact⟩
      have h1 : δ ≤ dist v y ^ 2 - D.nd v ^ 2 := hδle y hyS2
      have h2 : |(inner ℝ u (y - x) : ℝ)| ≤ M := hMle y hyS
      have h3 : -M ≤ (inner ℝ u (y - x) : ℝ) := neg_le_of_abs_le h2
      have h4 : dist (v - t • u) x ^ 2 - dist (v - t • u) y ^ 2 ≤ 0 := by
        rw [hkey, hvx]
        have htpos : 0 < t := by rw [ht]; positivity
        nlinarith
      nlinarith [dist_nonneg (x := v - t • u) (y := x), dist_nonneg (x := v - t • u) (y := y)]

/-- The inner product with the rotated vector is the plane cross product. -/
lemma inner_perp_eq_cross (a b c : Plane) :
    (inner ℝ (!₂[-(b 1 - a 1), b 0 - a 0] : Plane) (c - a) : ℝ) = cross a b c := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, cross]
  ring

/-- **Every site is a vertex of a nondegenerate Delaunay cell.**  At a Voronoi
vertex `v` of the cell of `x`, there are two further nearest sites forming a
nondegenerate triangle with `x`; all three lie on the empty circle of `v`. -/
theorem exists_nondegenerate_delaunay_triangle {x : Plane} (hx : x ∈ D.carrier) :
    ∃ v y₁ y₂ : Plane, x ∈ D.nearestSet v ∧ y₁ ∈ D.nearestSet v ∧ y₂ ∈ D.nearestSet v ∧
      cross x y₁ y₂ ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ := (D.isCompact_cell x).extremePoints_nonempty ⟨x, D.mem_cell_self x⟩
  have hvcell : v ∈ D.cell x := hv.1
  have hxA : x ∈ D.nearestSet v := D.mem_nearestSet_of_mem_cell hx hvcell
  refine ⟨v, ?_⟩
  by_contra hcon
  push_neg at hcon
  -- all nearest sites of `v` are collinear with `x`
  have hdeg : ∀ y₁ ∈ D.nearestSet v, ∀ y₂ ∈ D.nearestSet v, cross x y₁ y₂ = 0 := by
    intro y₁ h₁ y₂ h₂
    exact hcon y₁ y₂ hxA h₁ h₂
  -- pick a direction orthogonal to all active constraints
  obtain ⟨u, hune, hu⟩ :
      ∃ u : Plane, u ≠ 0 ∧ ∀ y ∈ D.nearestSet v, (inner ℝ u (y - x) : ℝ) = 0 := by
    by_cases hall : ∀ y ∈ D.nearestSet v, y = x
    · refine ⟨!₂[1, 0], ?_, ?_⟩
      · intro h
        have := congrArg (fun p : Plane => p 0) h
        simp at this
      · intro y hy
        rw [hall y hy]
        simp
    · push_neg at hall
      obtain ⟨y₁, hy₁, hy₁x⟩ := hall
      refine ⟨!₂[-(y₁ 1 - x 1), y₁ 0 - x 0], ?_, ?_⟩
      · intro h
        refine hy₁x ?_
        have h0 := congrArg (fun p : Plane => p 0) h
        have h1 := congrArg (fun p : Plane => p 1) h
        simp at h0 h1
        have hc0 : y₁ 0 = x 0 := by linarith
        have hc1 : y₁ 1 = x 1 := by linarith
        ext i
        fin_cases i
        · exact hc0
        · exact hc1
      · intro y hy
        rw [inner_perp_eq_cross]
        exact hdeg y₁ hy₁ y hy
  obtain ⟨t, htpos, hplus, hminus⟩ := D.exists_shift_mem_cell hx hvcell hu
  have hseg : v ∈ openSegment ℝ (v - t • u) (v + t • u) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [smul_sub, smul_add]
    module
  have hl : v - t • u = v := hv.2 hminus hplus hseg
  have hzero : t • u = 0 := by
    have h : v - (v - t • u) = 0 := by rw [hl]; abel
    simpa using h
  rcases smul_eq_zero.mp hzero with h | h
  · exact absurd h (ne_of_gt htpos)
  · exact hune h

/-- **A genuine weak Delaunay triangle at every site.**  Every site of a Delone
set is a vertex of a positively oriented nondegenerate triangle whose three
vertices are sites on a common empty circle; consequently every site of the
configuration satisfies the in-circle inequality against it. -/
theorem exists_weak_delaunay_triangle {x : Plane} (hx : x ∈ D.carrier) :
    ∃ y₁ y₂ : Plane, y₁ ∈ D.carrier ∧ y₂ ∈ D.carrier ∧ 0 < cross x y₁ y₂ ∧
      ∀ e ∈ D.carrier, 0 ≤ inCircleDet x y₁ y₂ e := by
  obtain ⟨v, y₁, y₂, hx', h₁, h₂, hne⟩ := D.exists_nondegenerate_delaunay_triangle hx
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hpos : 0 < cross x y₂ y₁ := by rw [cross_swap x y₂ y₁]; linarith
    refine ⟨y₂, y₁, h₂.1, h₁.1, hpos, ?_⟩
    · intro e he
      exact D.inCircleDet_nonneg_of_nearestSet hx' h₂ h₁ he hpos
  · exact ⟨y₁, y₂, h₁.1, h₂.1, hgt, fun e he =>
      D.inCircleDet_nonneg_of_nearestSet hx' h₁ h₂ he hgt⟩

end DeloneSet

end Conjecture41
