import Conjecture41.VoronoiPolygon

set_option autoImplicit false

/-!
# Delaunay cells of a Delone set

For a Delone set `D` and a point `v` of the plane, the *nearest-site set*

```
nearestSet v = {x ∈ D.carrier | dist v x = infDist v D.carrier}
```

is a finite nonempty set of sites lying on the circle of centre `v` and radius
the nearest-site distance, whose open disc contains no site (the empty-circle
property).  Its convex hull

```
delCell v = convexHull ℝ (nearestSet v)
```

is the Delaunay cell centred at `v`.

The main theorem of this file is the **covering theorem** for Delaunay cells:

```
∀ z, ∃ v, z ∈ delCell v
```

It is proved, not cited.  The proof maximizes the continuous function

```
f u = infDist u D.carrier ^ 2 - dist u z ^ 2
```

over the plane; relative density makes `f` eventually negative, so a global
maximizer `v` exists, and at a maximizer the target `z` must lie in the convex
hull of the nearest sites of `v`, since otherwise the Hilbert projection of `z`
on that compact convex hull produces a direction along which `f` strictly
increases.  This is the analytic form of the classical statement that the
projections of the lower faces of the lifted paraboloid hull subdivide the
plane.

This is gate G5b (covering part) of the formalization ledger.
-/

namespace Conjecture41

open Metric Set

namespace DeloneSet

variable (D : DeloneSet)

/-- The distance from a point of the plane to the nearest site. -/
noncomputable def nd (u : Plane) : ℝ := Metric.infDist u D.carrier

lemma nd_nonneg (u : Plane) : 0 ≤ D.nd u := Metric.infDist_nonneg

/-- The empty-circle inequality: no site is closer than `nd`. -/
lemma nd_le_dist {u x : Plane} (hx : x ∈ D.carrier) : D.nd u ≤ dist u x :=
  Metric.infDist_le_dist_of_mem hx

/-- The nearest-site distance is attained. -/
lemma exists_dist_eq_nd (u : Plane) : ∃ x ∈ D.carrier, dist u x = D.nd u := by
  obtain ⟨x, hx, hmin⟩ := D.exists_nearest u
  refine ⟨x, hx, le_antisymm ?_ (D.nd_le_dist hx)⟩
  exact (Metric.le_infDist D.nonempty).mpr (fun y hy => hmin y hy)

/-- Relative density bounds the nearest-site distance by the covering radius. -/
lemma nd_le_cov (u : Plane) : D.nd u ≤ D.cov := by
  obtain ⟨x, hx, hxd⟩ := D.cover u
  exact le_trans (D.nd_le_dist hx) hxd

lemma continuous_nd : Continuous D.nd := Metric.continuous_infDist_pt _

/-- The set of sites nearest to `v`. -/
def nearestSet (v : Plane) : Set Plane := {x | x ∈ D.carrier ∧ dist v x = D.nd v}

lemma nearestSet_subset_carrier (v : Plane) : D.nearestSet v ⊆ D.carrier :=
  fun _ hx => hx.1

lemma dist_eq_nd_of_mem {v x : Plane} (hx : x ∈ D.nearestSet v) : dist v x = D.nd v := hx.2

lemma nearestSet_nonempty (v : Plane) : (D.nearestSet v).Nonempty := by
  obtain ⟨x, hx, hxd⟩ := D.exists_dist_eq_nd v
  exact ⟨x, hx, hxd⟩

lemma nearestSet_subset_closedBall (v : Plane) :
    D.nearestSet v ⊆ closedBall v D.cov := by
  intro x hx
  rw [mem_closedBall, dist_comm, hx.2]
  exact D.nd_le_cov v

lemma nearestSet_finite (v : Plane) : (D.nearestSet v).Finite :=
  (D.finite_inter_closedBall v D.cov).subset
    (fun _ hx => ⟨hx.1, D.nearestSet_subset_closedBall v hx⟩)

/-- The Delaunay cell centred at `v`: the convex hull of the nearest sites. -/
def delCell (v : Plane) : Set Plane := convexHull ℝ (D.nearestSet v)

lemma nearestSet_subset_delCell (v : Plane) : D.nearestSet v ⊆ D.delCell v :=
  subset_convexHull ℝ _

lemma convex_delCell (v : Plane) : Convex ℝ (D.delCell v) := convex_convexHull ℝ _

lemma isCompact_delCell (v : Plane) : IsCompact (D.delCell v) :=
  (D.nearestSet_finite v).isCompact_convexHull

lemma delCell_nonempty (v : Plane) : (D.delCell v).Nonempty :=
  (D.nearestSet_nonempty v).mono (D.nearestSet_subset_delCell v)

/-- A Delaunay cell lies in the closed ball of radius the covering radius
around its centre. -/
lemma delCell_subset_closedBall (v : Plane) : D.delCell v ⊆ closedBall v D.cov := by
  refine convexHull_min (D.nearestSet_subset_closedBall v) ?_
  exact convex_closedBall v D.cov

/-! ### The shift identity -/

/-- Moving the base point along a direction changes the two squared distances
by the same affine amount. -/
lemma dist_sq_shift (v d z x : Plane) (t : ℝ) :
    dist (v + t • d) x ^ 2 - dist (v + t • d) z ^ 2
      = (dist v x ^ 2 - dist v z ^ 2) + 2 * t * (inner ℝ d (z - x) : ℝ) := by
  have hx : dist (v + t • d) x ^ 2 = dist v x ^ 2
      + 2 * t * (inner ℝ d (v - x) : ℝ) + t ^ 2 * ‖d‖ ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm]
    have hrw : v + t • d - x = (v - x) + t • d := by abel
    rw [hrw, @norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      real_inner_comm]
    rw [mul_pow, sq_abs]
    ring
  have hz : dist (v + t • d) z ^ 2 = dist v z ^ 2
      + 2 * t * (inner ℝ d (v - z) : ℝ) + t ^ 2 * ‖d‖ ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm]
    have hrw : v + t • d - z = (v - z) + t • d := by abel
    rw [hrw, @norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      real_inner_comm]
    rw [mul_pow, sq_abs]
    ring
  have hinner : (inner ℝ d (v - x) : ℝ) - (inner ℝ d (v - z) : ℝ) = (inner ℝ d (z - x) : ℝ) := by
    rw [← inner_sub_right]
    congr 1
    abel
  rw [hx, hz, ← hinner]
  ring

/-! ### The covering theorem -/

/-- **Delaunay cells cover the plane.**  Every point of the plane lies in the
convex hull of the nearest sites of some centre. -/
theorem exists_mem_delCell (z : Plane) : ∃ v : Plane, z ∈ D.delCell v := by
  classical
  set f : Plane → ℝ := fun u => D.nd u ^ 2 - dist u z ^ 2 with hf
  have hfcont : Continuous f := by
    refine Continuous.sub ((D.continuous_nd).pow 2) ?_
    exact (continuous_id.dist continuous_const).pow 2
  have hcov := D.cov_pos
  -- a global maximizer exists
  obtain ⟨v, hvmem, hvmax⟩ := (isCompact_closedBall z (D.cov + 1)).exists_isMaxOn
    ⟨z, mem_closedBall_self (by linarith)⟩ hfcont.continuousOn
  have hfz : 0 ≤ f z := by
    have : dist z z = 0 := dist_self z
    simp only [hf, this]
    have := D.nd_nonneg z
    nlinarith
  have hfzv : f z ≤ f v := hvmax (mem_closedBall_self (by linarith))
  have hglobal : ∀ u : Plane, f u ≤ f v := by
    intro u
    by_cases hu : u ∈ closedBall z (D.cov + 1)
    · exact hvmax hu
    · have h1 : D.cov + 1 < dist u z := by
        rw [mem_closedBall] at hu
        exact lt_of_not_ge hu
      have h2 : D.nd u ≤ D.cov := D.nd_le_cov u
      have h3 : 0 ≤ D.nd u := D.nd_nonneg u
      have h4 : f u ≤ D.cov ^ 2 - (D.cov + 1) ^ 2 := by
        simp only [hf]
        have hsq : D.nd u ^ 2 ≤ D.cov ^ 2 := by nlinarith
        have hsq2 : (D.cov + 1) ^ 2 ≤ dist u z ^ 2 := by nlinarith
        linarith
      nlinarith
  refine ⟨v, ?_⟩
  by_contra hz
  -- separate `z` from the compact convex Delaunay cell of `v`
  set K : Set Plane := D.delCell v with hK
  obtain ⟨p, hpK, hp⟩ := exists_norm_eq_iInf_of_complete_convex (D.delCell_nonempty v)
    (D.isCompact_delCell v).isComplete (D.convex_delCell v) z
  have hproj : ∀ w ∈ K, (inner ℝ (z - p) (w - p) : ℝ) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero (D.convex_delCell v) hpK).mp hp
  set d : Plane := z - p with hd
  have hdne : d ≠ 0 := by
    rw [hd, sub_ne_zero]
    intro h
    exact hz (h ▸ hpK)
  have hdnorm : 0 < ‖d‖ := norm_pos_iff.mpr hdne
  have hdsq : 0 < ‖d‖ ^ 2 := by positivity
  have hkey : ∀ x ∈ D.nearestSet v, ‖d‖ ^ 2 ≤ (inner ℝ d (z - x) : ℝ) := by
    intro x hx
    have hxK : x ∈ K := D.nearestSet_subset_delCell v hx
    have h1 := hproj x hxK
    have h2 : (inner ℝ d (z - x) : ℝ) = ‖d‖ ^ 2 - (inner ℝ d (x - p) : ℝ) := by
      have hrw : z - x = d - (x - p) := by rw [hd]; abel
      rw [hrw, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [h2]
    linarith
  -- the finitely many relevant sites
  set S : Finset Plane := D.ballFinset v (D.cov + 2) with hS
  set S2 : Finset Plane := S.filter (fun x => dist v x ≠ D.nd v) with hS2
  set M : ℝ := (∑ x ∈ S, |(inner ℝ d (z - x) : ℝ)|) + 1 with hM
  have hMpos : 0 < M := by
    have : 0 ≤ ∑ x ∈ S, |(inner ℝ d (z - x) : ℝ)| :=
      Finset.sum_nonneg fun x _ => abs_nonneg _
    rw [hM]; linarith
  have hMle : ∀ x ∈ S, |(inner ℝ d (z - x) : ℝ)| ≤ M := by
    intro x hx
    have h1 : |(inner ℝ d (z - x) : ℝ)| ≤ ∑ y ∈ S, |(inner ℝ d (z - y) : ℝ)| :=
      Finset.single_le_sum (f := fun y => |(inner ℝ d (z - y) : ℝ)|)
        (fun y _ => abs_nonneg _) hx
    rw [hM]; linarith
  set δ : ℝ := if h : S2.Nonempty then S2.inf' h (fun x => dist v x ^ 2 - D.nd v ^ 2) else 1
    with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    split_ifs with h
    · rw [Finset.lt_inf'_iff]
      intro x hx
      rw [hS2, Finset.mem_filter] at hx
      have hxc : x ∈ D.carrier := ((D.mem_ballFinset).mp hx.1).1
      have h1 : D.nd v ≤ dist v x := D.nd_le_dist hxc
      have h2 : D.nd v ≠ dist v x := fun h' => hx.2 h'.symm
      have h3 : D.nd v < dist v x := lt_of_le_of_ne h1 h2
      have h4 : 0 ≤ D.nd v := D.nd_nonneg v
      nlinarith
    · norm_num
  have hδle : ∀ x ∈ S2, δ ≤ dist v x ^ 2 - D.nd v ^ 2 := by
    intro x hx
    have hne : S2.Nonempty := ⟨x, hx⟩
    rw [hδ, dif_pos hne]
    exact Finset.inf'_le _ hx
  -- the perturbation
  set t : ℝ := min (1 / ‖d‖) (δ / (4 * M)) with ht
  have htpos : 0 < t := by
    rw [ht]
    exact lt_min (by positivity) (by positivity)
  have htd : t * ‖d‖ ≤ 1 := by
    have h1 : t ≤ 1 / ‖d‖ := min_le_left _ _
    calc t * ‖d‖ ≤ (1 / ‖d‖) * ‖d‖ := by nlinarith
      _ = 1 := by field_simp
  have htM : 2 * t * M < δ := by
    have h1 : t ≤ δ / (4 * M) := min_le_right _ _
    have h2 : 2 * t * M ≤ 2 * (δ / (4 * M)) * M := by nlinarith
    have h3 : 2 * (δ / (4 * M)) * M = δ / 2 := by field_simp; ring
    linarith
  set u : Plane := v + t • d with hu
  have hudist : dist v u ≤ 1 := by
    rw [hu, dist_eq_norm]
    have hrw : v - (v + t • d) = -(t • d) := by abel
    rw [hrw, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    exact htd
  obtain ⟨w, hwc, hwd⟩ := D.exists_dist_eq_nd u
  have hwS : w ∈ S := by
    rw [hS, D.mem_ballFinset]
    refine ⟨hwc, ?_⟩
    have h1 : dist w v ≤ dist w u + dist u v := dist_triangle _ _ _
    have h2 : dist w u = dist u w := dist_comm _ _
    have h3 : dist u w = D.nd u := hwd
    have h4 : D.nd u ≤ D.cov := D.nd_le_cov u
    have h5 : dist u v = dist v u := dist_comm _ _
    linarith
  have hfu : f u = dist v w ^ 2 - dist v z ^ 2 + 2 * t * (inner ℝ d (z - w) : ℝ) := by
    have h1 : f u = dist u w ^ 2 - dist u z ^ 2 := by
      simp only [hf, hwd]
    rw [h1, hu, dist_sq_shift v d z w t]
  have hfv : f v = D.nd v ^ 2 - dist v z ^ 2 := rfl
  have hcontra : f v < f u := by
    by_cases hwn : w ∈ D.nearestSet v
    · have h1 : dist v w = D.nd v := hwn.2
      have h2 : ‖d‖ ^ 2 ≤ (inner ℝ d (z - w) : ℝ) := hkey w hwn
      rw [hfu, h1, hfv]
      nlinarith
    · have hwS2 : w ∈ S2 := by
        rw [hS2, Finset.mem_filter]
        exact ⟨hwS, fun hcon => hwn ⟨hwc, hcon⟩⟩
      have h1 : δ ≤ dist v w ^ 2 - D.nd v ^ 2 := hδle w hwS2
      have h2 : |(inner ℝ d (z - w) : ℝ)| ≤ M := hMle w hwS
      have h3 : -M ≤ (inner ℝ d (z - w) : ℝ) := by
        have := abs_le.mp h2
        linarith [this.1]
      have h4 : 2 * t * (inner ℝ d (z - w) : ℝ) ≥ -(2 * t * M) := by nlinarith
      rw [hfu, hfv]
      linarith
  exact absurd (hglobal u) (not_le.mpr hcontra)

/-! ### Equivariance -/

/-- The nearest-site distance is invariant under a translation preserving the
set. -/
lemma nd_translate {w : Plane} (hw : (fun p : Plane => p + w) '' D.carrier = D.carrier)
    (u : Plane) : D.nd (u + w) = D.nd u := by
  have hmem : ∀ y : Plane, y ∈ D.carrier ↔ y + w ∈ D.carrier := by
    intro y
    constructor
    · intro hy; rw [← hw]; exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hw] at hy
      obtain ⟨q, hq, hqe⟩ := hy
      have : q = y := by
        have : q + w = y + w := hqe
        exact add_right_cancel this
      rwa [this] at hq
  refine le_antisymm ?_ ?_
  · obtain ⟨x, hx, hxd⟩ := D.exists_dist_eq_nd u
    have hxw : x + w ∈ D.carrier := (hmem x).mp hx
    have : dist (u + w) (x + w) = dist u x := by
      rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
    calc D.nd (u + w) ≤ dist (u + w) (x + w) := D.nd_le_dist hxw
      _ = dist u x := this
      _ = D.nd u := hxd
  · obtain ⟨x, hx, hxd⟩ := D.exists_dist_eq_nd (u + w)
    have hxw : x - w ∈ D.carrier := by
      refine (hmem (x - w)).mpr ?_
      have : x - w + w = x := by abel
      rwa [this]
    have : dist u (x - w) = dist (u + w) x := by
      rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
    calc D.nd u ≤ dist u (x - w) := D.nd_le_dist hxw
      _ = dist (u + w) x := this
      _ = D.nd (u + w) := hxd

/-- The nearest-site set is equivariant under a translation preserving the
set. -/
lemma nearestSet_translate {w : Plane} (hw : (fun p : Plane => p + w) '' D.carrier = D.carrier)
    (v : Plane) : D.nearestSet (v + w) = (fun p : Plane => p + w) '' D.nearestSet v := by
  have hmem : ∀ y : Plane, y ∈ D.carrier ↔ y + w ∈ D.carrier := by
    intro y
    constructor
    · intro hy; rw [← hw]; exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hw] at hy
      obtain ⟨q, hq, hqe⟩ := hy
      have hqy : q = y := add_right_cancel (by exact hqe)
      rwa [hqy] at hq
  ext y
  constructor
  · rintro ⟨hyc, hyd⟩
    refine ⟨y - w, ⟨?_, ?_⟩, by simp⟩
    · exact (hmem (y - w)).mpr (by rwa [show y - w + w = y by abel])
    · have h1 : dist v (y - w) = dist (v + w) y := by
        rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
      rw [h1, hyd, D.nd_translate hw v]
  · rintro ⟨q, ⟨hqc, hqd⟩, rfl⟩
    refine ⟨(hmem q).mp hqc, ?_⟩
    have h1 : dist (v + w) (q + w) = dist v q := by
      rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
    rw [h1, hqd, D.nd_translate hw v]

/-- Delaunay cells are equivariant under a translation preserving the set. -/
lemma delCell_translate {w : Plane} (hw : (fun p : Plane => p + w) '' D.carrier = D.carrier)
    (v : Plane) : D.delCell (v + w) = (fun p : Plane => p + w) '' D.delCell v := by
  have himg : (fun p : Plane => p + w) '' D.delCell v
      = convexHull ℝ ((fun p : Plane => p + w) '' D.nearestSet v) := by
    have := AffineMap.image_convexHull (AffineMap.const ℝ Plane w +ᵥ AffineMap.id ℝ Plane)
      (D.nearestSet v)
    simpa [delCell, add_comm] using this
  rw [delCell, D.nearestSet_translate hw v, himg]

end DeloneSet

end Conjecture41
