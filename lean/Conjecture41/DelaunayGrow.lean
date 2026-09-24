import Conjecture41.DelaunayTiling

set_option autoImplicit false

/-!
# Growing an empty circle

A Delaunay cell `delCell v` is full-dimensional exactly when at least three
sites lie on the empty circle of `v`.  To triangulate the whole plane one needs
to know that every point lies in such a cell, and this file provides the
mechanism: if the nearest-site set of `v` is *degenerate*, in the precise sense
that some unit direction `d` is orthogonal to all its differences and points
away from it, then the empty circle can be grown along `d` until a new site
joins it, without ever losing the sites already on it.

The precise statement is `DeloneSet.exists_grow`: there is a new centre `v'`
with `nearestSet v ⊆ nearestSet v'` and at least one extra site.  Note that the
Delone covering radius is what makes the growth stop: the empty circle around
`v + t·d` has radius at least `t`, but the nearest site is always within
`cov`.
-/

namespace Conjecture41

open Metric Set

/-- Coordinate dot product on the plane. -/
def pdot (u w : Plane) : ℝ := u 0 * w 0 + u 1 * w 1

lemma pdot_sub_sub (d u w : Plane) : pdot d (u - w) = pdot d u - pdot d w := by
  simp only [pdot, PiLp.sub_apply]; ring

lemma dist_sq_move (v d x : Plane) (t : ℝ) (hd : pdot d d = 1) :
    dist (v + t • d) x ^ 2 = dist v x ^ 2 + 2 * t * pdot d (v - x) + t ^ 2 := by
  rw [dist_sq_coords, dist_sq_coords]
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, pdot] at *
  nlinarith [hd]

lemma dist_move (v d : Plane) (s t : ℝ) (hd : pdot d d = 1) :
    dist (v + t • d) (v + s • d) = |t - s| := by
  have h : dist (v + t • d) (v + s • d) ^ 2 = (t - s) ^ 2 := by
    rw [dist_sq_coords]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pdot] at *
    nlinarith [hd]
  have h0 : (0 : ℝ) ≤ dist (v + t • d) (v + s • d) := dist_nonneg
  have := abs_nonneg (t - s)
  nlinarith [sq_abs (t - s)]

namespace DeloneSet

variable (D : DeloneSet)

/-- **Growing the empty circle.**  If a unit direction `d` is orthogonal to all
differences of nearest sites of `v` and the nearest sites are on the far side
of `v` along `d`, then moving `v` along `d` produces a centre whose nearest-site
set strictly contains that of `v`. -/
theorem exists_grow (v d : Plane) (hd : pdot d d = 1)
    (hperp : ∀ x ∈ D.nearestSet v, ∀ y ∈ D.nearestSet v, pdot d (x - y) = 0)
    (hfar : ∀ x ∈ D.nearestSet v, 0 ≤ pdot d (v - x)) :
    ∃ v' : Plane, D.nearestSet v ⊆ D.nearestSet v' ∧
      ∃ y, y ∈ D.nearestSet v' ∧ y ∉ D.nearestSet v := by
  classical
  obtain ⟨a, ha⟩ := D.nearestSet_nonempty v
  set c : ℝ := pdot d (v - a) with hc
  have hc0 : 0 ≤ c := hfar a ha
  set u : ℝ → Plane := fun t => v + t • d with hu
  set ρ : ℝ → ℝ := fun t => Real.sqrt (D.nd v ^ 2 + 2 * t * c + t ^ 2) with hρ
  have hrad : ∀ t : ℝ, 0 ≤ t → 0 ≤ D.nd v ^ 2 + 2 * t * c + t ^ 2 := by
    intro t ht; nlinarith [sq_nonneg (D.nd v), mul_nonneg ht hc0]
  -- the sites of `S` stay equidistant from the moving centre
  have hpd : ∀ x ∈ D.nearestSet v, pdot d (v - x) = c := by
    intro x hx
    have h := hperp x hx a ha
    rw [hc]
    have e : pdot d (v - a) - pdot d (v - x) = pdot d (x - a) := by
      simp only [pdot, PiLp.sub_apply]; ring
    linarith
  have hkey : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D.nearestSet v, dist (u t) x = ρ t := by
    intro t ht x hx
    have h1 : dist (u t) x ^ 2 = D.nd v ^ 2 + 2 * t * c + t ^ 2 := by
      rw [hu]
      rw [dist_sq_move v d x t hd, hpd x hx, hx.2]
    have h2 : 0 ≤ dist (u t) x := dist_nonneg
    show dist (u t) x = Real.sqrt (D.nd v ^ 2 + 2 * t * c + t ^ 2)
    rw [← h1, Real.sqrt_sq h2]
  have hρ0 : ρ 0 = D.nd v := by
    show Real.sqrt (D.nd v ^ 2 + 2 * 0 * c + 0 ^ 2) = D.nd v
    rw [show D.nd v ^ 2 + 2 * 0 * c + 0 ^ 2 = D.nd v ^ 2 by ring, Real.sqrt_sq (D.nd_nonneg v)]
  have hρge : ∀ t : ℝ, 0 ≤ t → t ≤ ρ t := by
    intro t ht
    show t ≤ Real.sqrt (D.nd v ^ 2 + 2 * t * c + t ^ 2)
    nth_rewrite 1 [(Real.sqrt_sq ht).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (D.nd v), mul_nonneg ht hc0])
  have hρcont : Continuous ρ := by
    rw [hρ]
    exact Real.continuous_sqrt.comp (by continuity)
  have hucont : Continuous u := by
    rw [hu]; continuity
  have hndcont : Continuous fun t => D.nd (u t) := D.continuous_nd.comp hucont
  have hle : ∀ t : ℝ, 0 ≤ t → D.nd (u t) ≤ ρ t := by
    intro t ht
    rw [← hkey t ht a ha]
    exact D.nd_le_dist ha.1
  -- the growth stops before `cov + 1`
  set T : ℝ := D.cov + 1 with hT
  have hTpos : 0 < T := by have := D.cov_pos; linarith
  have hTnot : D.nd (u T) < ρ T := by
    have h1 : D.nd (u T) ≤ D.cov := D.nd_le_cov _
    have h2 : T ≤ ρ T := hρge T (le_of_lt hTpos)
    linarith
  set A : Set ℝ := {t | t ∈ Icc (0 : ℝ) T ∧ D.nd (u t) = ρ t} with hA
  have hAne : (0 : ℝ) ∈ A := by
    refine ⟨⟨le_rfl, le_of_lt hTpos⟩, ?_⟩
    rw [hρ0]
    simp [hu]
  have hAclosed : IsClosed A := by
    have : A = Icc (0 : ℝ) T ∩ (fun t => D.nd (u t) - ρ t) ⁻¹' {0} := by
      ext t
      simp only [hA, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, sub_eq_zero]
    rw [this]
    exact isClosed_Icc.inter (IsClosed.preimage (hndcont.sub hρcont) isClosed_singleton)
  have hAcompact : IsCompact A := by
    refine (isCompact_Icc (a := (0:ℝ)) (b := T)).of_isClosed_subset hAclosed ?_
    intro t ht; exact ht.1
  set s : ℝ := sSup A with hs
  have hsA : s ∈ A := hAcompact.sSup_mem ⟨0, hAne⟩
  have hs0 : 0 ≤ s := hsA.1.1
  have hsT : s < T := by
    rcases lt_or_eq_of_le hsA.1.2 with h | h
    · exact h
    · exfalso; rw [h] at hsA; exact absurd hsA.2 (ne_of_lt hTnot)
  have hsub : D.nearestSet v ⊆ D.nearestSet (u s) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    rw [hkey s hs0 x hx, ← hsA.2]
  -- beyond `s` the empty circle is strictly smaller than `ρ`
  have hbeyond : ∀ t : ℝ, s < t → t ≤ T → D.nd (u t) < ρ t := by
    intro t h1 h2
    rcases lt_or_eq_of_le (hle t (le_trans hs0 (le_of_lt h1))) with h | h
    · exact h
    · exfalso
      have : t ∈ A := ⟨⟨le_trans hs0 (le_of_lt h1), h2⟩, h⟩
      have := le_csSup hAcompact.bddAbove this
      linarith
  set δ : ℝ := min 1 (T - s) with hδ
  have hδpos : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδT : s + δ ≤ T := by
    have := min_le_right 1 (T - s)
    linarith
  -- the finitely many sites that can be nearest during the growth
  have hFfin : (D.carrier ∩ closedBall (u s) (D.cov + 1)).Finite :=
    D.finite_inter_closedBall (u s) (D.cov + 1)
  set G : Set Plane := (D.carrier ∩ closedBall (u s) (D.cov + 1)) \ D.nearestSet v with hG
  have hGfin : G.Finite := hFfin.subset (fun x hx => hx.1)
  have hGsub : G ⊆ D.carrier := fun x hx => hx.1.1
  -- for every `t` slightly beyond `s`, a site outside `nearestSet v` is nearest
  have hnew : ∀ t : ℝ, s < t → t ≤ s + δ →
      ∃ x, x ∈ G ∧ dist (u t) x = D.nd (u t) := by
    intro t h1 h2
    have ht0 : 0 ≤ t := le_trans hs0 (le_of_lt h1)
    have htT : t ≤ T := le_trans h2 hδT
    obtain ⟨x, hxc, hxd⟩ := D.exists_dist_eq_nd (u t)
    have hlt : D.nd (u t) < ρ t := hbeyond t h1 htT
    have hxS : x ∉ D.nearestSet v := by
      intro hxS
      have := hkey t ht0 x hxS
      rw [hxd] at this
      linarith
    have hball : dist (u s) x ≤ D.cov + 1 := by
      have h3 : dist (u s) (u t) = |s - t| := by
        rw [hu]; exact dist_move v d t s hd
      have h4 : |s - t| ≤ 1 := by
        rw [abs_of_nonpos (by linarith)]
        have := hδ1
        linarith
      have h5 : dist (u t) x ≤ D.cov := by rw [hxd]; exact D.nd_le_cov _
      calc dist (u s) x ≤ dist (u s) (u t) + dist (u t) x := dist_triangle _ _ _
        _ ≤ 1 + D.cov := by rw [h3]; linarith
        _ = D.cov + 1 := by ring
    exact ⟨x, ⟨⟨hxc, mem_closedBall.mpr (by rw [dist_comm]; exact hball)⟩, hxS⟩, hxd⟩
  have hGne : G.Nonempty := by
    obtain ⟨x, hx, -⟩ := hnew (s + δ) (by linarith) le_rfl
    exact ⟨x, hx⟩
  -- the distance to the new sites
  set m : ℝ → ℝ := fun t => infDist (u t) G with hm
  have hmcont : Continuous m := (Metric.continuous_infDist_pt G).comp hucont
  have hmlt : ∀ t : ℝ, s < t → t ≤ s + δ → m t < ρ t := by
    intro t h1 h2
    obtain ⟨x, hxG, hxd⟩ := hnew t h1 h2
    have h3 : m t ≤ dist (u t) x := infDist_le_dist_of_mem hxG
    have h4 : D.nd (u t) < ρ t := hbeyond t h1 (le_trans h2 hδT)
    rw [hxd] at h3
    linarith
  have hmge : ρ s ≤ m s := by
    have h1 : D.nd (u s) ≤ m s := by
      rw [hm]
      exact Metric.infDist_le_infDist_of_subset hGsub hGne
    rw [← hsA.2]
    exact h1
  have hmle : m s ≤ ρ s := by
    have h1 : Filter.Tendsto m (nhdsWithin s (Ioi s)) (nhds (m s)) :=
      (hmcont.tendsto s).mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto ρ (nhdsWithin s (Ioi s)) (nhds (ρ s)) :=
      (hρcont.tendsto s).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto h1 h2 ?_
    filter_upwards [Ioo_mem_nhdsGT (show s < s + δ by linarith)] with t ht
    exact le_of_lt (hmlt t ht.1 (le_of_lt ht.2))
  have hmeq : m s = ρ s := le_antisymm hmle hmge
  obtain ⟨y, hyG, hyd⟩ := (hGfin.isCompact).exists_infDist_eq_dist hGne (u s)
  refine ⟨u s, hsub, y, ⟨hGsub hyG, ?_⟩, hyG.2⟩
  have hfin : infDist (u s) G = D.nd (u s) := by
    rw [hsA.2]
    exact hmeq
  rw [← hyd, hfin]

end DeloneSet

/-! ### A unit direction orthogonal to a given vector -/

/-- An explicit unit vector orthogonal to `w` (an arbitrary unit vector if
`w = 0`). -/
noncomputable def unitPerp (w : Plane) : Plane :=
  if pdot w w = 0 then !₂[1, 0] else (Real.sqrt (pdot w w))⁻¹ • !₂[-(w 1), w 0]

lemma pdot_self_nonneg (w : Plane) : 0 ≤ pdot w w := by
  simp only [pdot]; nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]

lemma pdot_neg_right (d u : Plane) : pdot d (-u) = -pdot d u := by
  simp only [pdot, PiLp.neg_apply]; ring

lemma pdot_unitPerp_self (w : Plane) : pdot (unitPerp w) (unitPerp w) = 1 := by
  unfold unitPerp
  split_ifs with h
  · simp [pdot]
  · have hpos : 0 < pdot w w := lt_of_le_of_ne (pdot_self_nonneg w) (Ne.symm h)
    have hpos' : (0:ℝ) < w 0 ^ 2 + w 1 ^ 2 := by simp only [pdot] at hpos; nlinarith
    have hsq2 : Real.sqrt (w 0 ^ 2 + w 1 ^ 2) ^ 2 = w 0 ^ 2 + w 1 ^ 2 :=
      Real.sq_sqrt hpos'.le
    have hne2 : Real.sqrt (w 0 ^ 2 + w 1 ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos'
    simp only [pdot, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    field_simp
    nlinarith [hsq2, hpos']

lemma pdot_unitPerp_orth (w : Plane) : pdot (unitPerp w) w = 0 := by
  unfold unitPerp
  split_ifs with h
  · have hw0 : w 0 = 0 := by
      simp only [pdot] at h
      nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
    have hw1 : w 1 = 0 := by
      simp only [pdot] at h
      nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
    simp [pdot, hw0, hw1]
  · simp only [pdot, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring

/-- A unit direction orthogonal to `w` making a nonnegative angle with `z`. -/
lemma exists_unit_perp (w z : Plane) :
    ∃ d : Plane, pdot d d = 1 ∧ pdot d w = 0 ∧ 0 ≤ pdot d z := by
  rcases le_or_gt 0 (pdot (unitPerp w) z) with h | h
  · exact ⟨unitPerp w, pdot_unitPerp_self w, pdot_unitPerp_orth w, h⟩
  · refine ⟨-unitPerp w, ?_, ?_, ?_⟩
    · have hs := pdot_unitPerp_self w
      simp only [pdot, PiLp.neg_apply] at hs ⊢
      nlinarith [hs]
    · have ho := pdot_unitPerp_orth w
      simp only [pdot, PiLp.neg_apply] at ho ⊢
      linarith
    · simp only [pdot, PiLp.neg_apply] at h ⊢
      linarith

namespace DeloneSet

variable (D : DeloneSet)

/-- The number of sites on the empty circle of `v`. -/
noncomputable def nsCard (v : Plane) : ℕ := (D.nearestSet_finite v).toFinset.card

lemma delCell_mono {v v' : Plane} (h : D.nearestSet v ⊆ D.nearestSet v') :
    D.delCell v ⊆ D.delCell v' := convexHull_mono h

/-- **If at most two sites lie on the empty circle of `v`, the circle can be
grown.** -/
theorem exists_grow_of_card_le_two {v : Plane} (hle : D.nsCard v ≤ 2) :
    ∃ v' : Plane, D.nearestSet v ⊆ D.nearestSet v' ∧ D.nsCard v < D.nsCard v' := by
  classical
  obtain ⟨a, ha⟩ := D.nearestSet_nonempty v
  set T := (D.nearestSet_finite v).toFinset with hT
  have hmemT : ∀ x : Plane, x ∈ T ↔ x ∈ D.nearestSet v := by
    intro x; simp [hT]
  -- a vector spanning all the differences of nearest sites
  obtain ⟨w, hw⟩ : ∃ w : Plane, ∀ x ∈ D.nearestSet v, ∀ y ∈ D.nearestSet v,
      x - y = 0 ∨ x - y = w ∨ x - y = -w := by
    have hTne : T.Nonempty := ⟨a, (hmemT a).mpr ha⟩
    rcases Nat.lt_or_ge T.card 2 with hc | hc
    · have hcard1 : T.card = 1 := by
        have := Finset.card_pos.mpr hTne
        omega
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcard1
      refine ⟨0, fun x hx y hy => Or.inl ?_⟩
      have hxb : x = b := by
        have hx' : x ∈ T := (hmemT x).mpr hx
        rw [hb] at hx'; simpa using hx'
      have hyb : y = b := by
        have hy' : y ∈ T := (hmemT y).mpr hy
        rw [hb] at hy'; simpa using hy'
      rw [hxb, hyb, sub_self]
    · have hcard2 : T.card = 2 := le_antisymm (by simpa [hT, nsCard] using hle) hc
      obtain ⟨b, c, hbc, hT2⟩ := Finset.card_eq_two.mp hcard2
      refine ⟨c - b, fun x hx y hy => ?_⟩
      have hxm : x = b ∨ x = c := by
        have hx' : x ∈ T := (hmemT x).mpr hx
        rw [hT2] at hx'; simpa using hx'
      have hym : y = b ∨ y = c := by
        have hy' : y ∈ T := (hmemT y).mpr hy
        rw [hT2] at hy'; simpa using hy'
      rcases hxm with rfl | rfl <;> rcases hym with rfl | rfl
      · exact Or.inl (sub_self _)
      · exact Or.inr (Or.inr (by rw [neg_sub]))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (sub_self _)
  obtain ⟨d, hd1, hd2, hd3⟩ := exists_unit_perp w (v - a)
  have hperp : ∀ x ∈ D.nearestSet v, ∀ y ∈ D.nearestSet v, pdot d (x - y) = 0 := by
    intro x hx y hy
    rcases hw x hx y hy with h | h | h <;> rw [h]
    · simp [pdot]
    · exact hd2
    · rw [pdot_neg_right, hd2, neg_zero]
  have hfar : ∀ x ∈ D.nearestSet v, 0 ≤ pdot d (v - x) := by
    intro x hx
    have hax : pdot d (a - x) = 0 := hperp a ha x hx
    have e : pdot d (v - x) - pdot d (v - a) = pdot d (a - x) := by
      simp only [pdot, PiLp.sub_apply]; ring
    linarith
  obtain ⟨v', hsub, y, hy1, hy2⟩ := D.exists_grow v d hd1 hperp hfar
  refine ⟨v', hsub, ?_⟩
  have hss : T ⊂ (D.nearestSet_finite v').toFinset := by
    refine Finset.ssubset_iff_of_subset ?_ |>.mpr
      ⟨y, by simpa using hy1, fun hc => hy2 ((hmemT y).mp hc)⟩
    intro x hx
    simpa using hsub ((hmemT x).mp hx)
  simpa [nsCard, hT] using Finset.card_lt_card hss

/-- **Every point of the plane lies in a Delaunay cell with at least three
sites on its empty circle.**  Such a cell is a nondegenerate convex polygon,
so it is triangulated by the fan of `Fan.lean`. -/
theorem exists_delCell_three (z : Plane) :
    ∃ v : Plane, z ∈ D.delCell v ∧ 3 ≤ D.nsCard v := by
  classical
  obtain ⟨v0, hv0⟩ := D.exists_mem_delCell z
  set F := (D.finite_inter_closedBall z (2 * D.cov)).toFinset with hF
  have hsubF : ∀ v : Plane, z ∈ D.delCell v → (D.nearestSet_finite v).toFinset ⊆ F := by
    intro v hv x hx
    have hx' : x ∈ D.nearestSet v := by simpa using hx
    have h1 : dist v x ≤ D.cov := by rw [hx'.2]; exact D.nd_le_cov v
    have h2 : dist z v ≤ D.cov := by
      have h := D.delCell_subset_closedBall v hv
      simpa [Metric.mem_closedBall] using h
    have h3 : dist z x ≤ 2 * D.cov := by
      have := dist_triangle z v x
      linarith
    simp only [hF, Set.Finite.mem_toFinset, Set.mem_inter_iff, Metric.mem_closedBall]
    exact ⟨hx'.1, by rw [dist_comm]; exact h3⟩
  have key : ∀ k : ℕ, ∀ v : Plane, z ∈ D.delCell v → F.card - D.nsCard v ≤ k →
      ∃ v', z ∈ D.delCell v' ∧ 3 ≤ D.nsCard v' := by
    intro k
    induction k with
    | zero =>
      intro v hv hk
      rcases Nat.lt_or_ge (D.nsCard v) 3 with h3 | h3
      · exfalso
        obtain ⟨v', hsub, hlt⟩ := D.exists_grow_of_card_le_two (v := v) (by omega)
        have hz' : z ∈ D.delCell v' := D.delCell_mono hsub hv
        have hle1 : D.nsCard v' ≤ F.card := by
          simpa [nsCard] using Finset.card_le_card (hsubF v' hz')
        omega
      · exact ⟨v, hv, h3⟩
    | succ n ih =>
      intro v hv hk
      rcases Nat.lt_or_ge (D.nsCard v) 3 with h3 | h3
      · obtain ⟨v', hsub, hlt⟩ := D.exists_grow_of_card_le_two (v := v) (by omega)
        exact ih v' (D.delCell_mono hsub hv) (by omega)
      · exact ⟨v, hv, h3⟩
  exact key F.card v0 hv0 (Nat.sub_le _ _)

end DeloneSet

end Conjecture41
