import Conjecture41.DelaunayGrow

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Growing the empty circle across a boundary edge of a Delaunay cell

Let `a ≠ b` be two nearest sites of a centre `v` such that every *other*
nearest site of `v` lies strictly on one side of the line `ab` — that is, the
segment `[a,b]` is a boundary edge of the Delaunay cell of `v`.  Moving the
centre along the perpendicular bisector of `[a,b]`, away from that side, keeps
`a` and `b` on the empty circle, and the circle must eventually meet a new
site: the covering radius of the Delone set forbids an arbitrarily large empty
circle.

`DeloneSet.exists_grow_edge` is that statement.  The new centre `v'` is a
*different*, full-dimensional centre whose Delaunay cell also has `[a,b]` as a
boundary edge, on the other side.  This is the geometric heart of the
face-to-face (edge-to-edge) property of the Delaunay tiling: every boundary
edge of a Delaunay cell is shared with exactly one further cell.

Throughout, `pdot d (a - y)` is the signed distance of the site `y` from the
line `ab`, measured in the direction opposite to the unit normal `d`.
-/

namespace Conjecture41

open Metric Set

lemma pdot_self_eq_dist_sq (x y : Plane) : pdot (x - y) (x - y) = dist x y ^ 2 := by
  rw [dist_sq_coords]
  simp only [pdot, PiLp.sub_apply]
  ring

lemma pdot_cauchy_schwarz (d z : Plane) : pdot d z ^ 2 ≤ pdot d d * pdot z z := by
  simp only [pdot]
  nlinarith [sq_nonneg (d 0 * z 1 - d 1 * z 0)]

lemma pdot_sub_left_cancel (d x y z : Plane) :
    pdot d (x - z) - pdot d (y - z) = pdot d (x - y) := by
  simp only [pdot, PiLp.sub_apply]; ring

namespace DeloneSet

variable (D : DeloneSet)

/-- **Growing the empty circle across a boundary edge.**

If `a` and `b` are nearest sites of `v` and every other nearest site of `v` is
strictly on the `-d` side of the line `ab` (where `d` is a unit vector
orthogonal to `b - a`), then moving the centre along `d` produces a *new*
centre `v + t·d`, `t > 0`, which still has `a` and `b` as nearest sites and has
at least one further nearest site, necessarily strictly on the `d` side. -/
theorem exists_grow_edge {v a b d : Plane} (hd : pdot d d = 1)
    (ha : a ∈ D.nearestSet v) (hb : b ∈ D.nearestSet v)
    (hperp : pdot d (a - b) = 0)
    (hleft : ∀ y ∈ D.nearestSet v, y ≠ a → y ≠ b → 0 < pdot d (a - y)) :
    ∃ t : ℝ, 0 < t ∧ a ∈ D.nearestSet (v + t • d) ∧ b ∈ D.nearestSet (v + t • d) ∧
      (∃ y ∈ D.nearestSet (v + t • d), pdot d (a - y) < 0) ∧
      (∀ y ∈ D.nearestSet (v + t • d), y ≠ a → y ≠ b → pdot d (a - y) < 0) := by
  classical
  set u : ℝ → Plane := fun t => v + t • d with hu
  set N : ℝ := D.nd v with hN
  set c : ℝ := pdot d (v - a) with hc
  set ρ : ℝ → ℝ := fun t => Real.sqrt (N ^ 2 + 2 * t * c + t ^ 2) with hρ
  have hN0 : 0 ≤ N := D.nd_nonneg v
  -- `|c| ≤ N`
  have hcN : c ^ 2 ≤ N ^ 2 := by
    have h1 : pdot d (v - a) ^ 2 ≤ pdot d d * pdot (v - a) (v - a) := pdot_cauchy_schwarz _ _
    rw [hd, one_mul, pdot_self_eq_dist_sq, ha.2] at h1
    exact h1
  have hrad : ∀ t : ℝ, 0 ≤ N ^ 2 + 2 * t * c + t ^ 2 := by
    intro t; nlinarith [sq_nonneg (t + c)]
  have hρnn : ∀ t : ℝ, 0 ≤ ρ t := fun t => Real.sqrt_nonneg _
  have hρsq : ∀ t : ℝ, ρ t ^ 2 = N ^ 2 + 2 * t * c + t ^ 2 := by
    intro t; exact Real.sq_sqrt (hrad t)
  -- distances to `a` and `b`
  have hpdb : pdot d (v - b) = c := by
    have := pdot_sub_left_cancel d v a b
    -- `pdot d (v - b) - pdot d (a - b) = pdot d (v - a)`
    have h2 : pdot d (v - b) - pdot d (a - b) = pdot d (v - a) := by
      simp only [pdot, PiLp.sub_apply]; ring
    rw [hperp, sub_zero] at h2
    rw [h2, hc]
  have hda : ∀ t : ℝ, dist (u t) a = ρ t := by
    intro t
    have h1 : dist (u t) a ^ 2 = N ^ 2 + 2 * t * c + t ^ 2 := by
      rw [hu]
      rw [dist_sq_move v d a t hd, ← hc, ha.2]
    have h2 : (0 : ℝ) ≤ dist (u t) a := dist_nonneg
    nlinarith [hρsq t, hρnn t]
  have hdb : ∀ t : ℝ, dist (u t) b = ρ t := by
    intro t
    have h1 : dist (u t) b ^ 2 = N ^ 2 + 2 * t * c + t ^ 2 := by
      rw [hu]
      rw [dist_sq_move v d b t hd, hpdb, hb.2]
    have h2 : (0 : ℝ) ≤ dist (u t) b := dist_nonneg
    nlinarith [hρsq t, hρnn t]
  -- the key affine comparison
  have hcleN : c ≤ N := by nlinarith [hcN, hN0]
  have hdiff : ∀ (t : ℝ) (y : Plane),
      dist (u t) y ^ 2 - ρ t ^ 2 = (dist v y ^ 2 - N ^ 2) + 2 * t * pdot d (a - y) := by
    intro t y
    have hsplit : pdot d (v - y) = c + pdot d (a - y) := by
      rw [hc]; simp only [pdot, PiLp.sub_apply]; ring
    rw [hu]
    rw [dist_sq_move v d y t hd, hρsq t, hsplit]
    ring
  have hgnn : ∀ y ∈ D.carrier, 0 ≤ dist v y ^ 2 - N ^ 2 := by
    intro y hy
    have h1 : D.nd v ≤ dist v y := D.nd_le_dist hy
    nlinarith [dist_nonneg (x := v) (y := y), D.nd_nonneg v]
  have hsda : pdot d (a - a) = 0 := by simp only [pdot, PiLp.sub_apply]; ring
  have hgpos : ∀ y ∈ D.carrier, pdot d (a - y) < 0 → 0 < dist v y ^ 2 - N ^ 2 := by
    intro y hy hsd
    rcases lt_or_eq_of_le (hgnn y hy) with h | h
    · exact h
    · exfalso
      have hyd : dist v y = N := by
        have h1 : dist v y ^ 2 = N ^ 2 := by linarith
        nlinarith [dist_nonneg (x := v) (y := y)]
      have hyn : y ∈ D.nearestSet v := ⟨hy, hyd⟩
      have hya : y ≠ a := by rintro rfl; rw [hsda] at hsd; exact lt_irrefl 0 hsd
      have hyb : y ≠ b := by rintro rfl; rw [hperp] at hsd; exact lt_irrefl 0 hsd
      exact absurd (hleft y hyn hya hyb) (by linarith)
  -- a positive initial interval on which the circle stays empty
  set F : Finset Plane := D.ballFinset v (D.cov + 2) with hF
  set Fneg : Finset Plane := F.filter (fun y => pdot d (a - y) < 0) with hFneg
  set ε : ℝ := if h : Fneg.Nonempty then
      min 1 (Fneg.inf' h (fun y => (dist v y ^ 2 - N ^ 2) / (2 * -pdot d (a - y)))) else 1 with hε
  have hεpos : 0 < ε := by
    rw [hε]
    split_ifs with h
    · refine lt_min one_pos ?_
      rw [Finset.lt_inf'_iff]
      intro y hy
      rw [hFneg, Finset.mem_filter] at hy
      have hyc : y ∈ D.carrier := ((D.mem_ballFinset).mp hy.1).1
      have h1 := hgpos y hyc hy.2
      have h2 : 0 < 2 * -pdot d (a - y) := by linarith [hy.2]
      positivity
    · norm_num
  have hε1 : ε ≤ 1 := by
    rw [hε]; split_ifs with h
    · exact min_le_left _ _
    · exact le_rfl
  have hεle : ∀ y ∈ Fneg, ε ≤ (dist v y ^ 2 - N ^ 2) / (2 * -pdot d (a - y)) := by
    intro y hy
    have hne : Fneg.Nonempty := ⟨y, hy⟩
    rw [hε, dif_pos hne]
    exact le_trans (min_le_right _ _) (Finset.inf'_le _ hy)
  have hρle : ∀ t : ℝ, 0 ≤ t → ρ t ≤ N + t := by
    intro t ht
    have h1 : ρ t ^ 2 ≤ (N + t) ^ 2 := by
      rw [hρsq t]
      nlinarith [mul_nonneg ht (sub_nonneg.mpr hcleN)]
    nlinarith [hρnn t, hN0, ht]
  have hfar : ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ y ∈ D.carrier, dist v y > D.cov + 2 →
      ρ t ≤ dist (u t) y := by
    intro t ht ht1 y _ hy
    have hut : dist (u t) v = t := by
      have h1 : dist (v + t • d) (v + (0 : ℝ) • d) = |t - 0| := dist_move v d 0 t hd
      rw [zero_smul, add_zero, sub_zero, abs_of_nonneg ht] at h1
      exact h1
    have h1 : dist v y ≤ dist v (u t) + dist (u t) y := dist_triangle _ _ _
    have h2 : dist v (u t) = t := by rw [dist_comm]; exact hut
    have h3 : ρ t ≤ N + t := hρle t ht
    have h4 : N ≤ D.cov := D.nd_le_cov v
    linarith
  have hstart : ∀ t : ℝ, 0 ≤ t → t ≤ ε → D.nd (u t) = ρ t := by
    intro t ht htε
    have ht1 : t ≤ 1 := le_trans htε hε1
    refine le_antisymm ?_ ?_
    · rw [← hda t]
      exact D.nd_le_dist ha.1
    · refine (Metric.le_infDist D.nonempty).mpr ?_
      intro y hy
      by_cases hyb : dist v y ≤ D.cov + 2
      · have hyF : y ∈ F := (D.mem_ballFinset).mpr ⟨hy, by rw [dist_comm]; exact hyb⟩
        by_cases hsd : pdot d (a - y) < 0
        · have hyFneg : y ∈ Fneg := by rw [hFneg, Finset.mem_filter]; exact ⟨hyF, hsd⟩
          have hb1 := hεle y hyFneg
          have hpos : 0 < 2 * -pdot d (a - y) := by linarith
          have hb2 : ε * (2 * -pdot d (a - y)) ≤ dist v y ^ 2 - N ^ 2 :=
            (le_div_iff₀ hpos).mp hb1
          have hkey0 : 0 ≤ dist (u t) y ^ 2 - ρ t ^ 2 := by
            rw [hdiff t y]; nlinarith
          nlinarith [hkey0, hρnn t, dist_nonneg (x := u t) (y := y)]
        · push_neg at hsd
          have hg := hgnn y hy
          have hkey0 : 0 ≤ dist (u t) y ^ 2 - ρ t ^ 2 := by
            rw [hdiff t y]; nlinarith
          nlinarith [hkey0, hρnn t, dist_nonneg (x := u t) (y := y)]
      · push_neg at hyb
        exact hfar t ht ht1 y hy hyb
  -- the growth stops
  set T : ℝ := 2 * D.cov + 3 with hT
  have hcov := D.cov_pos
  have hTpos : 0 < T := by rw [hT]; linarith
  have hεT : ε ≤ T := by linarith [hε1]
  have hρT : D.cov < ρ T := by
    have h1 : (T + c) ^ 2 ≤ ρ T ^ 2 := by rw [hρsq T]; nlinarith
    have h2 : -N ≤ c := by nlinarith
    have h3 : N ≤ D.cov := D.nd_le_cov v
    have h4 : 0 < T + c := by linarith
    nlinarith [hρnn T]
  have hTnot : D.nd (u T) < ρ T := lt_of_le_of_lt (D.nd_le_cov _) hρT
  have hρcont : Continuous ρ := by
    rw [hρ]
    exact Real.continuous_sqrt.comp (by fun_prop)
  have hucont : Continuous u := by
    rw [hu]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hndcont : Continuous fun t => D.nd (u t) := D.continuous_nd.comp hucont
  have hle : ∀ t : ℝ, D.nd (u t) ≤ ρ t := by
    intro t
    rw [← hda t]
    exact D.nd_le_dist ha.1
  set A : Set ℝ := {t | t ∈ Icc (0 : ℝ) T ∧ D.nd (u t) = ρ t} with hA
  have hεA : ε ∈ A := ⟨⟨le_of_lt hεpos, hεT⟩, hstart ε (le_of_lt hεpos) le_rfl⟩
  have hAclosed : IsClosed A := by
    have hrw : A = Icc (0 : ℝ) T ∩ (fun t => D.nd (u t) - ρ t) ⁻¹' {0} := by
      ext t
      simp only [hA, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, sub_eq_zero]
    rw [hrw]
    exact isClosed_Icc.inter (IsClosed.preimage (hndcont.sub hρcont) isClosed_singleton)
  have hAcompact : IsCompact A :=
    (isCompact_Icc (a := (0 : ℝ)) (b := T)).of_isClosed_subset hAclosed fun t ht => ht.1
  set s : ℝ := sSup A with hs
  have hsA : s ∈ A := hAcompact.sSup_mem ⟨ε, hεA⟩
  have hspos : 0 < s := lt_of_lt_of_le hεpos (le_csSup hAcompact.bddAbove hεA)
  have hsT : s < T := by
    rcases lt_or_eq_of_le hsA.1.2 with h | h
    · exact h
    · exfalso; rw [h] at hsA; exact absurd hsA.2 (ne_of_lt hTnot)
  -- beyond `s` the empty circle is strictly smaller
  have hbeyond : ∀ t : ℝ, s < t → t ≤ T → D.nd (u t) < ρ t := by
    intro t h1 h2
    rcases lt_or_eq_of_le (hle t) with h | h
    · exact h
    · exact absurd (le_csSup hAcompact.bddAbove
        (show t ∈ A from ⟨⟨le_trans (le_of_lt hspos) (le_of_lt h1), h2⟩, h⟩)) (by linarith)
  set δ : ℝ := min 1 (T - s) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by linarith)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδT : s + δ ≤ T := by have := min_le_right 1 (T - s); linarith
  -- the finitely many sites that can catch up
  set G : Set Plane := {y | y ∈ D.carrier ∩ closedBall (u s) (D.cov + 1) ∧ pdot d (a - y) < 0}
    with hG
  have hGfin : G.Finite := (D.finite_inter_closedBall (u s) (D.cov + 1)).subset fun y hy => hy.1
  have hGsub : G ⊆ D.carrier := fun y hy => hy.1.1
  have hnew : ∀ t : ℝ, s < t → t ≤ s + δ → ∃ y, y ∈ G ∧ dist (u t) y = D.nd (u t) := by
    intro t h1 h2
    have ht0 : 0 ≤ t := le_trans (le_of_lt hspos) (le_of_lt h1)
    have htT : t ≤ T := le_trans h2 hδT
    obtain ⟨y, hyc, hyd⟩ := D.exists_dist_eq_nd (u t)
    have hlt : D.nd (u t) < ρ t := hbeyond t h1 htT
    have hsd : pdot d (a - y) < 0 := by
      have h3 : dist (u t) y ^ 2 - ρ t ^ 2 < 0 := by
        rw [hyd]
        nlinarith [D.nd_nonneg (u t), hρnn t]
      have h4 := hdiff t y
      have h5 := hgnn y hyc
      nlinarith
    have hball : dist (u s) y ≤ D.cov + 1 := by
      have h3 : dist (u s) (u t) = |s - t| := by rw [hu]; exact dist_move v d t s hd
      have h4 : |s - t| ≤ 1 := by
        rw [abs_of_nonpos (by linarith)]; linarith [hδ1]
      have h5 : dist (u t) y ≤ D.cov := by rw [hyd]; exact D.nd_le_cov _
      calc dist (u s) y ≤ dist (u s) (u t) + dist (u t) y := dist_triangle _ _ _
        _ ≤ 1 + D.cov := by rw [h3]; linarith
        _ = D.cov + 1 := by ring
    exact ⟨y, ⟨⟨hyc, mem_closedBall.mpr (by rw [dist_comm]; exact hball)⟩, hsd⟩, hyd⟩
  have hGne : G.Nonempty := by
    obtain ⟨y, hy, -⟩ := hnew (s + δ) (by linarith) le_rfl
    exact ⟨y, hy⟩
  set m : ℝ → ℝ := fun t => infDist (u t) G with hm
  have hmcont : Continuous m := (Metric.continuous_infDist_pt G).comp hucont
  have hmlt : ∀ t : ℝ, s < t → t ≤ s + δ → m t < ρ t := by
    intro t h1 h2
    obtain ⟨y, hyG, hyd⟩ := hnew t h1 h2
    have h3 : m t ≤ dist (u t) y := infDist_le_dist_of_mem hyG
    have h4 : D.nd (u t) < ρ t := hbeyond t h1 (le_trans h2 hδT)
    rw [hyd] at h3
    linarith
  have hmge : ρ s ≤ m s := by
    have h1 : D.nd (u s) ≤ m s := Metric.infDist_le_infDist_of_subset hGsub hGne
    rw [← hsA.2]; exact h1
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
  have hother : ∀ z ∈ D.nearestSet (u s), z ≠ a → z ≠ b → pdot d (a - z) < 0 := by
    intro z hz hza hzb
    have hdz : dist (u s) z = ρ s := by rw [hz.2, hsA.2]
    have h0 : dist (u s) z ^ 2 - ρ s ^ 2 = 0 := by rw [hdz]; ring
    have h1 := hdiff s z
    have h2 := hgnn z hz.1
    rcases lt_trichotomy (pdot d (a - z)) 0 with h | h | h
    · exact h
    · exfalso
      have h3 : dist v z ^ 2 = N ^ 2 := by rw [h] at h1; linarith
      have h4 : dist v z = N := by
        nlinarith [dist_nonneg (x := v) (y := z), hN0]
      exact absurd (hleft z ⟨hz.1, h4⟩ hza hzb) (by rw [h]; exact lt_irrefl 0)
    · exfalso
      nlinarith
  refine ⟨s, hspos, ⟨ha.1, ?_⟩, ⟨hb.1, ?_⟩, ⟨y, ⟨hGsub hyG, ?_⟩, hyG.2⟩, hother⟩
  · show dist (u s) a = D.nd (u s)
    rw [hda s, hsA.2]
  · show dist (u s) b = D.nd (u s)
    rw [hdb s, hsA.2]
  · show dist (u s) y = D.nd (u s)
    rw [← hyd, hsA.2]
    exact hmeq

end DeloneSet

end Conjecture41
