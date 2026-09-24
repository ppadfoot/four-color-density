import Mathlib.Analysis.Real.Pi.Bounds
import Conjecture41.Periodic
import Conjecture41.Voronoi
import Conjecture41.Limsup

set_option autoImplicit false

/-!
# From arbitrary configurations to square-periodic ones (gates G7 and G8)

This file contains the plane-to-periodic reduction:

* `grid_pigeonhole` (square extraction): among the half-open grid squares of
  side `L`, one contains a proportional share of the points of `C` in the ball
  of radius `r`;
* `card_strip_bound` (explicit boundary-strip estimate): deleting the width-one
  boundary strip of a square of side `L` removes at most `11 (L+1)` points;
* `periodize` (buffered periodization): the retained points, repeated by
  `L·ℤ²`, form a valid periodic configuration;
* `conjecture_4_1_of_periodic` (contrapositive): the periodic theorem implies
  the exact unrestricted epsilon/eventual statement.
-/

namespace Conjecture41

open Metric Set MeasureTheory

/-! ### The grid of half-open squares -/

/-- Grid index of a point in the grid of half-open squares of side `L`. -/
noncomputable def gridIdx (L : ℝ) (x : Plane) : ℤ × ℤ := (⌊x 0 / L⌋, ⌊x 1 / L⌋)

/-- The half-open grid square with index `k`. -/
def gridSquare (L : ℝ) (k : ℤ × ℤ) : Set Plane :=
  boxSet (Ico ((k.1 : ℝ) * L) ((k.1 : ℝ) * L + L)) (Ico ((k.2 : ℝ) * L) ((k.2 : ℝ) * L + L))

lemma mem_Ico_iff_floor {L : ℝ} (hL : 0 < L) (u : ℝ) (k : ℤ) :
    u ∈ Ico ((k : ℝ) * L) ((k : ℝ) * L + L) ↔ ⌊u / L⌋ = k := by
  rw [Set.mem_Ico, Int.floor_eq_iff, le_div_iff₀ hL, div_lt_iff₀ hL]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith⟩

lemma mem_gridSquare_iff {L : ℝ} (hL : 0 < L) (k : ℤ × ℤ) (x : Plane) :
    x ∈ gridSquare L k ↔ gridIdx L x = k := by
  simp only [gridSquare, boxSet, Set.mem_setOf_eq, mem_Ico_iff_floor hL, gridIdx,
    Prod.ext_iff]

lemma measurableSet_gridSquare (L : ℝ) (k : ℤ × ℤ) : MeasurableSet (gridSquare L k) :=
  measurableSet_boxSet measurableSet_Ico measurableSet_Ico

lemma volume_gridSquare {L : ℝ} (hL : 0 < L) (k : ℤ × ℤ) :
    volume (gridSquare L k) = ENNReal.ofReal (L ^ 2) := by
  rw [gridSquare, volume_boxSet measurableSet_Ico measurableSet_Ico, Real.volume_Ico,
    Real.volume_Ico]
  rw [show (k.1 : ℝ) * L + L - (k.1 : ℝ) * L = L by ring,
    show (k.2 : ℝ) * L + L - (k.2 : ℝ) * L = L by ring,
    ← ENNReal.ofReal_mul hL.le]
  congr 1
  ring

lemma disjoint_gridSquare {L : ℝ} (hL : 0 < L) {k k' : ℤ × ℤ} (h : k ≠ k') :
    Disjoint (gridSquare L k) (gridSquare L k') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact h (((mem_gridSquare_iff hL k x).mp hx).symm.trans ((mem_gridSquare_iff hL k' x).mp hx'))

/-- Two points of one grid square are at distance at most `2L`. -/
lemma dist_le_of_mem_gridSquare {L : ℝ} (hL : 0 < L) {k : ℤ × ℤ} {x y : Plane}
    (hx : x ∈ gridSquare L k) (hy : y ∈ gridSquare L k) : dist x y ≤ 2 * L := by
  obtain ⟨⟨hx0, hx0'⟩, ⟨hx1, hx1'⟩⟩ := hx
  obtain ⟨⟨hy0, hy0'⟩, ⟨hy1, hy1'⟩⟩ := hy
  have h0 : |x 0 - y 0| ≤ L := by rw [abs_le]; constructor <;> linarith
  have h1 : |x 1 - y 1| ≤ L := by rw [abs_le]; constructor <;> linarith
  refine (dist_le_of_coord_le h0 h1).trans ?_
  rw [show L ^ 2 + L ^ 2 = (Real.sqrt 2 * L) ^ 2 by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; ring]
  rw [Real.sqrt_sq (by positivity)]
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
    Real.sqrt_nonneg 2, hL.le]

/-! ### Square extraction -/

/--
Square extraction.  For every side length `L > 0` and radius `r ≥ 0` there is a
half-open square of side `L` containing a set `T` of points of `C` with
`#(C ∩ B(0,r)) · L² ≤ #T · π (r+2L)²`.
-/
lemma grid_pigeonhole (C : FourColorConfig) {L : ℝ} (hL : 0 < L) {r : ℝ} (hr : 0 ≤ r) :
    ∃ (a b : ℝ) (T : Finset Plane),
      (∀ x ∈ T, x ∈ C.carrier) ∧
      (∀ x ∈ T, x 0 ∈ Ico a (a + L) ∧ x 1 ∈ Ico b (b + L)) ∧
      (countInClosedBall C r : ℝ) * L ^ 2 ≤ (T.card : ℝ) * (Real.pi * (r + 2 * L) ^ 2) := by
  classical
  set F := pointsInClosedBall C r with hFdef
  rcases F.eq_empty_or_nonempty with hF | hF
  · refine ⟨0, 0, ∅, by simp, by simp, ?_⟩
    have : countInClosedBall C r = 0 := by simp [countInClosedBall, ← hFdef, hF]
    rw [this]
    simp
  set I := F.image (gridIdx L) with hIdef
  have hI : I.Nonempty := hF.image _
  obtain ⟨k₀, hk₀I, hk₀max⟩ :=
    I.exists_max_image (fun k => (F.filter (fun x => gridIdx L x = k)).card) hI
  set T := F.filter (fun x => gridIdx L x = k₀) with hTdef
  -- the number of occupied squares times `L²` is at most the area of a slightly larger disc
  have harea : (I.card : ℝ) * L ^ 2 ≤ Real.pi * (r + 2 * L) ^ 2 := by
    have hsub : ∀ k ∈ I, gridSquare L k ⊆ closedBall (0 : Plane) (r + 2 * L) := by
      intro k hk y hy
      obtain ⟨x, hxF, hxk⟩ := Finset.mem_image.mp hk
      have hxsq : x ∈ gridSquare L k := (mem_gridSquare_iff hL k x).mpr hxk
      have h1 : dist y x ≤ 2 * L := dist_le_of_mem_gridSquare hL hy hxsq
      have h2 : dist x 0 ≤ r := (mem_pointsInClosedBall.mp hxF).2
      have := dist_triangle y x (0 : Plane)
      simp only [mem_closedBall]
      linarith
    have hdisj : (↑I : Set (ℤ × ℤ)).Pairwise
        (Function.onFun Disjoint (gridSquare L)) := fun k _ k' _ h => disjoint_gridSquare hL h
    have hvol : ∑ k ∈ I, volume (gridSquare L k) ≤ volume (closedBall (0 : Plane) (r + 2 * L)) := by
      rw [measure_biUnion_finset hdisj (fun k _ => measurableSet_gridSquare L k) |>.symm]
      exact measure_mono (Set.iUnion₂_subset hsub)
    rw [Finset.sum_congr rfl (fun k _ => volume_gridSquare hL k), Finset.sum_const, nsmul_eq_mul,
      EuclideanSpace.volume_closedBall_fin_two, ← ENNReal.ofReal_natCast I.card,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity)] at hvol
    refine (ENNReal.ofReal_le_ofReal_iff ?_).mp ?_
    · positivity
    · calc ENNReal.ofReal ((I.card : ℝ) * L ^ 2) ≤ ENNReal.ofReal ((r + 2 * L) ^ 2 * Real.pi) :=
            hvol
        _ = ENNReal.ofReal (Real.pi * (r + 2 * L) ^ 2) := by rw [mul_comm]
  -- the pigeonhole step
  have hcard : (F.card : ℝ) ≤ (I.card : ℝ) * (T.card : ℝ) := by
    have h1 : F.card = ∑ k ∈ I, (F.filter (fun x => gridIdx L x = k)).card :=
      Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem _ hx)
    have h2 : ∑ k ∈ I, (F.filter (fun x => gridIdx L x = k)).card ≤ ∑ _k ∈ I, T.card :=
      Finset.sum_le_sum fun k hk => hk₀max k hk
    rw [Finset.sum_const, smul_eq_mul] at h2
    have := h1 ▸ h2
    exact_mod_cast this
  refine ⟨(k₀.1 : ℝ) * L, (k₀.2 : ℝ) * L, T, ?_, ?_, ?_⟩
  · intro x hx
    exact (mem_pointsInClosedBall.mp (Finset.mem_of_mem_filter x hx)).1
  · intro x hx
    have : gridIdx L x = k₀ := (Finset.mem_filter.mp hx).2
    exact (mem_gridSquare_iff hL k₀ x).mpr this
  · have hcount : (countInClosedBall C r : ℝ) = (F.card : ℝ) := rfl
    rw [hcount]
    have hT0 : (0 : ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
    have hL2 : (0 : ℝ) < L ^ 2 := by positivity
    calc (F.card : ℝ) * L ^ 2 ≤ ((I.card : ℝ) * (T.card : ℝ)) * L ^ 2 := by
          exact mul_le_mul_of_nonneg_right hcard hL2.le
      _ = (T.card : ℝ) * ((I.card : ℝ) * L ^ 2) := by ring
      _ ≤ (T.card : ℝ) * (Real.pi * (r + 2 * L) ^ 2) := mul_le_mul_of_nonneg_left harea hT0

/-! ### The boundary strip -/

/-- The points of `T` remaining after deleting the width-one boundary strip of
the square `[a, a+L) × [b, b+L)`. -/
noncomputable def interiorPoints (T : Finset Plane) (a b L : ℝ) : Finset Plane :=
  T.filter (fun x => (a + 1 ≤ x 0 ∧ x 0 ≤ a + L - 1) ∧ (b + 1 ≤ x 1 ∧ x 1 ≤ b + L - 1))

lemma interiorPoints_subset (T : Finset Plane) (a b L : ℝ) :
    interiorPoints T a b L ⊆ T := Finset.filter_subset _ _

lemma mem_interiorPoints {T : Finset Plane} {a b L : ℝ} {x : Plane}
    (hx : x ∈ interiorPoints T a b L) :
    x ∈ T ∧ x 0 ∈ Icc (a + 1) (a + L - 1) ∧ x 1 ∈ Icc (b + 1) (b + L - 1) := by
  obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hx
  exact ⟨h1, h2, h3⟩

/--
Explicit boundary-strip estimate.  Deleting the width-one boundary strip of a
square of side `L` removes at most `11 (L+1)` points of a valid configuration.
-/
lemma card_strip_bound (C : FourColorConfig) {L a b : ℝ} (hL : 0 ≤ L) (T : Finset Plane)
    (hTC : ∀ x ∈ T, x ∈ C.carrier)
    (hbox : ∀ x ∈ T, x 0 ∈ Ico a (a + L) ∧ x 1 ∈ Ico b (b + L)) :
    (T.card : ℝ) ≤ ((interiorPoints T a b L).card : ℝ) + 11 * (L + 1) := by
  classical
  -- a uniform bound for the number of points in a thin box
  have hstrip : ∀ (D : Finset Plane) (p q w h : ℝ), 0 ≤ w → 0 ≤ h →
      (∀ x ∈ D, x ∈ C.carrier) →
      (∀ x ∈ D, x 0 ∈ Icc p (p + w) ∧ x 1 ∈ Icc q (q + h)) →
      (D.card : ℝ) * (3 / 4) ≤ (w + 1) * (h + 1) := by
    intro D p q w h hw hh hDC hDbox
    have hb := card_mul_pi_div_four_le_of_box C D p q w h hw hh hDC hDbox
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have : (D.card : ℝ) * (3 / 4) ≤ (D.card : ℝ) * (Real.pi / 4) := by
      have : (0 : ℝ) ≤ (D.card : ℝ) := Nat.cast_nonneg _
      nlinarith
    linarith
  set D := T.filter (fun x => ¬((a + 1 ≤ x 0 ∧ x 0 ≤ a + L - 1) ∧ (b + 1 ≤ x 1 ∧ x 1 ≤ b + L - 1)))
    with hDdef
  have hsplit : (interiorPoints T a b L).card + D.card = T.card :=
    Finset.card_filter_add_card_filter_not (s := T) (p := fun x : Plane =>
      (a + 1 ≤ x 0 ∧ x 0 ≤ a + L - 1) ∧ (b + 1 ≤ x 1 ∧ x 1 ≤ b + L - 1))
  -- the four boundary strips
  set D1 := T.filter (fun x => x 0 ≤ a + 1) with hD1
  set D2 := T.filter (fun x => a + L - 1 ≤ x 0) with hD2
  set D3 := T.filter (fun x => x 1 ≤ b + 1) with hD3
  set D4 := T.filter (fun x => b + L - 1 ≤ x 1) with hD4
  have hDsub : D ⊆ D1 ∪ D2 ∪ D3 ∪ D4 := by
    intro x hx
    obtain ⟨hxT, hxP⟩ := Finset.mem_filter.mp hx
    simp only [Finset.mem_union, hD1, hD2, hD3, hD4, Finset.mem_filter]
    by_contra hc
    push_neg at hc
    exact hxP ⟨⟨(hc.1.1.1 hxT).le, (hc.1.1.2 hxT).le⟩, ⟨(hc.1.2 hxT).le, (hc.2 hxT).le⟩⟩
  have hDcard : D.card ≤ D1.card + D2.card + D3.card + D4.card := by
    calc D.card ≤ (D1 ∪ D2 ∪ D3 ∪ D4).card := Finset.card_le_card hDsub
      _ ≤ (D1 ∪ D2 ∪ D3).card + D4.card := Finset.card_union_le _ _
      _ ≤ ((D1 ∪ D2).card + D3.card) + D4.card := by
          exact Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ ((D1.card + D2.card) + D3.card) + D4.card := by
          exact Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
  have hb1 : (D1.card : ℝ) * (3 / 4) ≤ 2 * (L + 1) := by
    have := hstrip D1 a b 1 L (by norm_num) hL
      (fun x hx => hTC x (Finset.mem_of_mem_filter x hx))
      (fun x hx => by
        obtain ⟨hxT, hxle⟩ := Finset.mem_filter.mp hx
        obtain ⟨⟨h1, _⟩, ⟨h3, h4⟩⟩ := hbox x hxT
        exact ⟨⟨h1, hxle⟩, ⟨h3, h4.le⟩⟩)
    linarith
  have hb2 : (D2.card : ℝ) * (3 / 4) ≤ 2 * (L + 1) := by
    have := hstrip D2 (a + L - 1) b 1 L (by norm_num) hL
      (fun x hx => hTC x (Finset.mem_of_mem_filter x hx))
      (fun x hx => by
        obtain ⟨hxT, hxle⟩ := Finset.mem_filter.mp hx
        obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hbox x hxT
        exact ⟨⟨hxle, by linarith⟩, ⟨h3, h4.le⟩⟩)
    linarith
  have hb3 : (D3.card : ℝ) * (3 / 4) ≤ 2 * (L + 1) := by
    have := hstrip D3 a b L 1 hL (by norm_num)
      (fun x hx => hTC x (Finset.mem_of_mem_filter x hx))
      (fun x hx => by
        obtain ⟨hxT, hxle⟩ := Finset.mem_filter.mp hx
        obtain ⟨⟨h1, h2⟩, ⟨h3, _⟩⟩ := hbox x hxT
        exact ⟨⟨h1, h2.le⟩, ⟨h3, hxle⟩⟩)
    linarith
  have hb4 : (D4.card : ℝ) * (3 / 4) ≤ 2 * (L + 1) := by
    have := hstrip D4 a (b + L - 1) L 1 hL (by norm_num)
      (fun x hx => hTC x (Finset.mem_of_mem_filter x hx))
      (fun x hx => by
        obtain ⟨hxT, hxle⟩ := Finset.mem_filter.mp hx
        obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hbox x hxT
        exact ⟨⟨h1, h2.le⟩, ⟨hxle, by linarith⟩⟩)
    linarith
  have hDreal : (D.card : ℝ) ≤ (D1.card : ℝ) + D2.card + D3.card + D4.card := by
    exact_mod_cast hDcard
  have : (D.card : ℝ) ≤ 11 * (L + 1) := by linarith
  have hsplit' : ((interiorPoints T a b L).card : ℝ) + (D.card : ℝ) = (T.card : ℝ) := by
    exact_mod_cast hsplit
  linarith

/-! ### Buffered periodization -/

/--
Buffered periodization.  A set of points of a valid configuration contained in
the inner square `[a+1, a+L-1] × [b+1, b+L-1]` can be repeated by the lattice
`L·ℤ²` to give a valid periodic configuration: same-cell pairs are valid
because they are pairs of `C`, and cross-cell pairs are separated by at least
`2 > √2` in some coordinate.
-/
lemma exists_periodicConfig (C : FourColorConfig) {L a b : ℝ} (hL : 4 ≤ L) (S : Finset Plane)
    (hSC : ∀ x ∈ S, x ∈ C.carrier)
    (hbox : ∀ x ∈ S, x 0 ∈ Icc (a + 1) (a + L - 1) ∧ x 1 ∈ Icc (b + 1) (b + L - 1)) :
    ∃ P : PeriodicConfig, P.side = L ∧ P.points = S := by
  refine ⟨ ⟨L, by linarith, S, C.color, ?_⟩, rfl, rfl⟩
  intro s hs t ht m n hne
  by_cases hmn : m = 0 ∧ n = 0
  · obtain ⟨rfl, rfl⟩ := hmn
    have hst : s ≠ t := fun h => hne ⟨h, rfl, rfl⟩
    simpa using C.valid (hSC s hs) (hSC t ht) hst
  · -- some coordinate is displaced by at least `2`
    have key : ∃ i : Fin 2, (2 : ℝ) ≤ |s i - (t + latticeVec L m n) i| := by
      obtain ⟨h0, h1⟩ := hbox s hs
      obtain ⟨h2, h3⟩ := hbox t ht
      rcases (not_and_or.mp hmn) with hm | hn
      · refine ⟨0, ?_⟩
        have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
          have : (1 : ℤ) ≤ |m| := Int.one_le_abs (by omega)
          calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
            _ ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast this
            _ = |(m : ℝ)| := by push_cast [Int.cast_abs]; ring_nf
        have hLm : L ≤ |L * (m : ℝ)| := by
          rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ L)]
          nlinarith
        rw [add_latticeVec_zero_apply]
        have hdiff : |s 0 - t 0| ≤ L - 2 := by
          rw [abs_le]
          obtain ⟨hs1, hs2⟩ := h0
          obtain ⟨ht1, ht2⟩ := h2
          constructor <;> linarith
        have : |s 0 - (t 0 + L * (m : ℝ))| ≥ |L * (m : ℝ)| - |s 0 - t 0| := by
          have := abs_sub_abs_le_abs_sub (L * (m:ℝ)) (s 0 - t 0)
          have h' : |L * (m:ℝ) - (s 0 - t 0)| = |s 0 - (t 0 + L * (m:ℝ))| := by
            rw [← abs_neg]; congr 1; ring
          linarith [h' ▸ this]
        linarith
      · refine ⟨1, ?_⟩
        have hm1 : (1 : ℝ) ≤ |(n : ℝ)| := by
          have : (1 : ℤ) ≤ |n| := Int.one_le_abs (by omega)
          calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
            _ ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
            _ = |(n : ℝ)| := by push_cast [Int.cast_abs]; ring_nf
        have hLm : L ≤ |L * (n : ℝ)| := by
          rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ L)]
          nlinarith
        rw [add_latticeVec_one_apply]
        have hdiff : |s 1 - t 1| ≤ L - 2 := by
          rw [abs_le]
          obtain ⟨hs1, hs2⟩ := h1
          obtain ⟨ht1, ht2⟩ := h3
          constructor <;> linarith
        have : |s 1 - (t 1 + L * (n : ℝ))| ≥ |L * (n : ℝ)| - |s 1 - t 1| := by
          have := abs_sub_abs_le_abs_sub (L * (n:ℝ)) (s 1 - t 1)
          have h' : |L * (n:ℝ) - (s 1 - t 1)| = |s 1 - (t 1 + L * (n:ℝ))| := by
            rw [← abs_neg]; congr 1; ring
          linarith [h' ▸ this]
        linarith
    obtain ⟨i, hi⟩ := key
    have hdist : (2 : ℝ) ≤ dist s (t + latticeVec L m n) :=
      le_trans hi (abs_coord_sub_le_dist _ _ i)
    have h2 : exclusionSq (C.color s) (C.color t) ≤ 2 := exclusionSq_le_two _ _
    nlinarith

/-! ### The contrapositive: from the periodic theorem to Conjecture 4.1 -/

/-- The closing polynomial estimate of the contrapositive: with side length
`u = √r ≥ 13` and `ep * u ≥ 25`, the periodic bound is incompatible with a
density exceeding `1 + ep`. -/
lemma periodization_poly_contradiction {ep u : ℝ} (hu13 : (13 : ℝ) ≤ u)
    (hueps : (25 : ℝ) ≤ ep * u)
    (hfinal : (1 + ep) * u ^ 6
      < u ^ 6 + 15 * u ^ 5 + 59 * u ^ 4 + 88 * u ^ 3 + 44 * u ^ 2) : False := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hp2 : (0 : ℝ) < u ^ 2 := by positivity
  have hp3 : (0 : ℝ) < u ^ 3 := by positivity
  have hp4 : (0 : ℝ) < u ^ 4 := by positivity
  have hp5 : (0 : ℝ) < u ^ 5 := by positivity
  have hA : 59 * u ^ 4 ≤ 5 * u ^ 5 := by nlinarith
  have hB : 88 * u ^ 3 ≤ u ^ 5 := by nlinarith
  have hC : 44 * u ^ 2 ≤ u ^ 5 := by nlinarith
  have hD : ep * u ^ 6 < 22 * u ^ 5 := by nlinarith
  have hE : (25 : ℝ) * u ^ 5 ≤ ep * u ^ 6 := by nlinarith
  linarith

/--
Gate G8.  The periodic density theorem implies the exact unrestricted
epsilon/eventual form of Cohn--Rajagopal Conjecture 4.1, with no additional
hypothesis on the configuration.
-/
theorem conjecture_4_1_of_periodic (hper : PeriodicDensityTheorem) (C : FourColorConfig) :
    UpperRadialDensityAtMostOne C := by
  classical
  by_contra hcon
  unfold UpperRadialDensityAtMostOne at hcon
  push_neg at hcon
  obtain ⟨e0, he0, hbad⟩ := hcon
  set ep := min e0 1 with hepdef
  have hep : 0 < ep := lt_min he0 one_pos
  have hep1 : ep ≤ 1 := min_le_right _ _
  have hepe0 : ep ≤ e0 := min_le_left _ _
  set R := (25 / ep) ^ 2 + 169 with hRdef
  have hR169 : (169 : ℝ) ≤ R := by
    have : (0 : ℝ) ≤ (25 / ep) ^ 2 := sq_nonneg _
    linarith
  obtain ⟨r, hrR, hrbad⟩ := hbad R (by linarith)
  have hr169 : (169 : ℝ) ≤ r := le_trans hR169 hrR
  have hr0 : (0 : ℝ) ≤ r := by linarith
  -- the side length of the extracted square
  set u := Real.sqrt r with hudef
  have hu2 : u ^ 2 = r := Real.sq_sqrt hr0
  have hunn : 0 ≤ u := Real.sqrt_nonneg _
  have hu13 : (13 : ℝ) ≤ u := by nlinarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hueps : (25 : ℝ) ≤ ep * u := by
    have h1 : (25 / ep) ^ 2 ≤ u ^ 2 := by rw [hu2]; linarith
    have h2 : (0 : ℝ) < 25 / ep := by positivity
    have h3 : 25 / ep ≤ u := by nlinarith
    rw [div_le_iff₀ hep] at h3
    linarith
  -- the strict count bound, weakened to `ep`
  have hcount : (1 + ep) * Real.pi * r ^ 2 < (countInClosedBall C r : ℝ) := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have : (1 + ep) * Real.pi * r ^ 2 ≤ (1 + e0) * Real.pi * r ^ 2 := by
      have : (0 : ℝ) ≤ Real.pi * r ^ 2 := by positivity
      nlinarith
    linarith
  -- square extraction
  obtain ⟨a, b, T, hTC, hTbox, hpig⟩ := grid_pigeonhole C hu0 hr0
  -- boundary strip
  have hstrip := card_strip_bound C hunn T hTC hTbox
  -- buffered periodization
  obtain ⟨P, hPside, hPpoints⟩ :=
    exists_periodicConfig C (by linarith : (4:ℝ) ≤ u) (interiorPoints T a b u)
      (fun x hx => hTC x (interiorPoints_subset T a b u hx))
      (fun x hx => ⟨(mem_interiorPoints hx).2.1, (mem_interiorPoints hx).2.2⟩)
  have hPcard : ((interiorPoints T a b u).card : ℝ) ≤ u ^ 2 := by
    have := hper P
    rw [hPside, hPpoints] at this
    exact this
  -- assemble
  have hchain : (1 + ep) * Real.pi * r ^ 2 * u ^ 2
      < (u ^ 2 + 11 * (u + 1)) * (Real.pi * (r + 2 * u) ^ 2) := by
    calc (1 + ep) * Real.pi * r ^ 2 * u ^ 2 < (countInClosedBall C r : ℝ) * u ^ 2 :=
          mul_lt_mul_of_pos_right hcount (by positivity)
      _ ≤ (T.card : ℝ) * (Real.pi * (r + 2 * u) ^ 2) := hpig
      _ ≤ (u ^ 2 + 11 * (u + 1)) * (Real.pi * (r + 2 * u) ^ 2) := by
          refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rw [← hu2] at hchain
  have hfinal : (1 + ep) * u ^ 6 < (u ^ 2 + 11 * u + 11) * (u ^ 2 + 2 * u) ^ 2 := by
    have e1 : (1 + ep) * Real.pi * (u ^ 2) ^ 2 * u ^ 2 = Real.pi * ((1 + ep) * u ^ 6) := by ring
    have e2 : (u ^ 2 + 11 * (u + 1)) * (Real.pi * ((u ^ 2) + 2 * u) ^ 2)
        = Real.pi * ((u ^ 2 + 11 * u + 11) * (u ^ 2 + 2 * u) ^ 2) := by ring
    rw [e1, e2] at hchain
    exact lt_of_mul_lt_mul_left hchain Real.pi_pos.le
  -- purely polynomial contradiction
  have hexp : (u ^ 2 + 11 * u + 11) * (u ^ 2 + 2 * u) ^ 2
      = u ^ 6 + 15 * u ^ 5 + 59 * u ^ 4 + 88 * u ^ 3 + 44 * u ^ 2 := by ring
  rw [hexp] at hfinal
  exact periodization_poly_contradiction hu13 hueps hfinal

end Conjecture41
