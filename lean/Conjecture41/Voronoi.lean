import Mathlib.Geometry.Euclidean.PerpBisector
import Conjecture41.Definitions

set_option autoImplicit false

/-!
# Voronoi cells of a four-colored configuration

This file sets up the packing-theoretic bookkeeping that converts a *local*
area bound for Voronoi cells into the *global* radial density bound of
Cohn--Rajagopal Conjecture 4.1.

The Voronoi cells of a configuration tile the plane and overlap only in a set
of measure zero, so a lower bound `c` for the area of every (truncated) cell
immediately yields the counting estimate `#(C ∩ B(0,r)) * c ≤ π (r+D)^2`, hence
an upper radial density at most `π / c`.
-/

namespace Conjecture41

open Metric Set MeasureTheory
open scoped ENNReal

/-- The closed Voronoi cell of `p` relative to the configuration `C`: the set
of points of the plane that are at least as close to `p` as to any point of
the configuration. -/
def voronoiCell (C : FourColorConfig) (p : Plane) : Set Plane :=
  {x | ∀ q ∈ C.carrier, dist x p ≤ dist x q}

lemma mem_voronoiCell_self (C : FourColorConfig) (p : Plane) :
    p ∈ voronoiCell C p := by
  intro q _
  simp [dist_nonneg]

/-- Voronoi cells are closed, hence measurable. -/
lemma isClosed_voronoiCell (C : FourColorConfig) (p : Plane) :
    IsClosed (voronoiCell C p) := by
  have : voronoiCell C p = ⋂ q ∈ C.carrier, {x : Plane | dist x p ≤ dist x q} := by
    ext x; simp [voronoiCell]
  rw [this]
  exact isClosed_biInter fun q _ => isClosed_le (continuous_id.dist continuous_const)
    (continuous_id.dist continuous_const)

lemma measurableSet_voronoiCell (C : FourColorConfig) (p : Plane) :
    MeasurableSet (voronoiCell C p) :=
  (isClosed_voronoiCell C p).measurableSet

/-- Every Voronoi cell contains the closed ball of radius `1/2` around its
center: this is exactly the statement that the configuration is `1`-separated. -/
lemma closedBall_subset_voronoiCell (C : FourColorConfig) {p : Plane}
    (hp : p ∈ C.carrier) : closedBall p (1 / 2) ⊆ voronoiCell C p := by
  intro x hx q hq
  rcases eq_or_ne q p with rfl | hqp
  · exact le_rfl
  · have hsep : 1 ≤ dist p q := uniformlySeparated C hp hq (Ne.symm hqp)
    have hxp : dist x p ≤ 1 / 2 := by simpa [dist_comm] using hx
    have : dist p q ≤ dist p x + dist x q := dist_triangle _ _ _
    rw [dist_comm p x] at this
    linarith

/-- Every Voronoi cell contains the open ball of radius `1/2` around its
center. -/
lemma ball_subset_voronoiCell (C : FourColorConfig) {p : Plane}
    (hp : p ∈ C.carrier) : ball p (1 / 2) ⊆ voronoiCell C p :=
  ball_subset_closedBall.trans (closedBall_subset_voronoiCell C hp)

/-- The half-plane `{x | dist x p ≤ dist x q}` is convex. -/
lemma convex_setOf_dist_le (p q : Plane) : Convex ℝ {x : Plane | dist x p ≤ dist x q} := by
  have h : {x : Plane | dist x p ≤ dist x q}
      = {x : Plane | (inner ℝ x (q - p) : ℝ) ≤ (‖q‖ ^ 2 - ‖p‖ ^ 2) / 2} := by
    ext x
    simp only [Set.mem_setOf_eq, dist_eq_norm]
    rw [← Real.sqrt_sq (norm_nonneg (x - p)), ← Real.sqrt_sq (norm_nonneg (x - q)),
      Real.sqrt_le_sqrt_iff (by positivity), @norm_sub_sq_real, @norm_sub_sq_real,
      inner_sub_right]
    constructor <;> intro h <;> linarith
  rw [h]
  exact convex_halfSpace_le
    ⟨fun a b => inner_add_left _ _ _, fun c a => real_inner_smul_left _ _ _⟩ _

/-- Voronoi cells are convex, being intersections of half-planes. -/
lemma convex_voronoiCell (C : FourColorConfig) (p : Plane) :
    Convex ℝ (voronoiCell C p) := by
  have h : voronoiCell C p = ⋂ q ∈ C.carrier, {x : Plane | dist x p ≤ dist x q} := by
    ext x; simp [voronoiCell]
  rw [h]
  exact convex_iInter fun q => convex_iInter fun _ => convex_setOf_dist_le p q

/-- Distinct centers have Voronoi cells meeting only in their perpendicular
bisector. -/
lemma voronoiCell_inter_subset_perpBisector (C : FourColorConfig) {p q : Plane}
    (hp : p ∈ C.carrier) (hq : q ∈ C.carrier) :
    voronoiCell C p ∩ voronoiCell C q ⊆
      (AffineSubspace.perpBisector p q : Set Plane) := by
  rintro x ⟨hxp, hxq⟩
  exact AffineSubspace.mem_perpBisector_iff_dist_eq.mpr
    (le_antisymm (hxp q hq) (hxq p hp))

/-- Voronoi cells of distinct centers are almost everywhere disjoint. -/
lemma aedisjoint_voronoiCell (C : FourColorConfig) {p q : Plane}
    (hp : p ∈ C.carrier) (hq : q ∈ C.carrier) (hpq : p ≠ q) :
    AEDisjoint volume (voronoiCell C p) (voronoiCell C q) := by
  have hne : AffineSubspace.perpBisector p q ≠ ⊤ := by
    intro h
    have hmem : p ∈ AffineSubspace.perpBisector p q := by rw [h]; trivial
    have := AffineSubspace.mem_perpBisector_iff_dist_eq.mp hmem
    simp only [dist_self] at this
    exact hpq (dist_eq_zero.mp this.symm)
  refine measure_mono_null (voronoiCell_inter_subset_perpBisector C hp hq) ?_
  exact MeasureTheory.Measure.addHaar_affineSubspace volume _ hne

/--
The counting estimate.  If every truncated Voronoi cell of `C` has area at
least `c`, then the number of points of `C` in the closed ball of radius `r`
is at most `π (r+D)^2 / c`.
-/
theorem count_mul_le_of_cell_volume_ge
    (C : FourColorConfig) (c D : ℝ) (hD : 0 ≤ D)
    (hcell : ∀ p ∈ C.carrier,
      ENNReal.ofReal c ≤ volume (voronoiCell C p ∩ closedBall p D))
    (r : ℝ) (hr : 0 ≤ r) :
    (countInClosedBall C r : ℝ) * c ≤ Real.pi * (r + D) ^ 2 := by
  classical
  set F := pointsInClosedBall C r with hF
  set A : Plane → Set Plane := fun p => voronoiCell C p ∩ closedBall p D with hA
  have hsub : ∀ p ∈ F, A p ⊆ closedBall (0 : Plane) (r + D) := by
    intro p hpF x hx
    obtain ⟨hpc, hpr⟩ := mem_pointsInClosedBall.mp hpF
    have h1 : dist x p ≤ D := by simpa [hA] using hx.2
    have : dist x 0 ≤ dist x p + dist p 0 := dist_triangle _ _ _
    simp only [mem_closedBall]
    linarith
  have hmeas : ∀ p ∈ F, NullMeasurableSet (A p) volume := fun p _ =>
    ((measurableSet_voronoiCell C p).inter measurableSet_closedBall).nullMeasurableSet
  have hdisj : Set.Pairwise (↑F) (Function.onFun (AEDisjoint volume) A) := by
    intro p hp q hq hpq
    have hpc := (mem_pointsInClosedBall.mp (by simpa using hp)).1
    have hqc := (mem_pointsInClosedBall.mp (by simpa using hq)).1
    exact AEDisjoint.mono (aedisjoint_voronoiCell C hpc hqc hpq)
      Set.inter_subset_left Set.inter_subset_left
  have hkey : (F.card : ℝ≥0∞) * ENNReal.ofReal c ≤ volume (closedBall (0 : Plane) (r + D)) := by
    have h1 : ∑ p ∈ F, ENNReal.ofReal c ≤ ∑ p ∈ F, volume (A p) := by
      refine Finset.sum_le_sum fun p hpF => ?_
      exact hcell p (mem_pointsInClosedBall.mp hpF).1
    have h2 : ∑ p ∈ F, volume (A p) = volume (⋃ p ∈ F, A p) :=
      (measure_biUnion_finset₀ hdisj hmeas).symm
    have h3 : volume (⋃ p ∈ F, A p) ≤ volume (closedBall (0 : Plane) (r + D)) :=
      measure_mono (Set.iUnion₂_subset hsub)
    calc (F.card : ℝ≥0∞) * ENNReal.ofReal c = ∑ _p ∈ F, ENNReal.ofReal c := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ F, volume (A p) := h1
      _ = volume (⋃ p ∈ F, A p) := h2
      _ ≤ _ := h3
  rw [EuclideanSpace.volume_closedBall_fin_two] at hkey
  have hrD : 0 ≤ r + D := by linarith
  have hlhs : (F.card : ℝ≥0∞) * ENNReal.ofReal c = ENNReal.ofReal ((F.card : ℝ) * c) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  have hrhs : ENNReal.ofReal (r + D) ^ 2 * ENNReal.ofReal Real.pi
      = ENNReal.ofReal (Real.pi * (r + D) ^ 2) := by
    rw [← ENNReal.ofReal_pow hrD, ← ENNReal.ofReal_mul (by positivity)]
    ring_nf
  rw [hlhs, hrhs] at hkey
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hkey

/--
From the counting estimate with constant `c = 1` one gets exactly the
epsilon/eventual form of upper radial density at most one.
-/
theorem upperRadialDensity_of_count_bound
    (C : FourColorConfig) (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ r : ℝ, 0 ≤ r → (countInClosedBall C r : ℝ) ≤ Real.pi * (r + D) ^ 2) :
    UpperRadialDensityAtMostOne C := by
  intro ε hε
  set s := Real.sqrt (1 + ε) with hs
  have hssq : s ^ 2 = 1 + ε := Real.sq_sqrt (by linarith)
  have hsnn : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : 1 < s := by nlinarith [hssq, hsnn]
  refine ⟨max 1 (D / (s - 1)), le_max_left _ _, ?_⟩
  intro r hr
  have hr1 : (1 : ℝ) ≤ r := le_trans (le_max_left _ _) hr
  have hr0 : 0 < r := by linarith
  have hD' : D / (s - 1) ≤ r := le_trans (le_max_right _ _) hr
  have hsD : D ≤ (s - 1) * r := by
    rw [div_le_iff₀ (by linarith)] at hD'
    linarith
  have hkey : (r + D) ^ 2 ≤ (1 + ε) * r ^ 2 := by
    have h1 : r + D ≤ s * r := by linarith [hsD]
    have h2 : (r + D) ^ 2 ≤ (s * r) ^ 2 := by
      exact pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ r + D) h1 2
    calc (r + D) ^ 2 ≤ (s * r) ^ 2 := h2
      _ = s ^ 2 * r ^ 2 := by ring
      _ = (1 + ε) * r ^ 2 := by rw [hssq]
  calc (countInClosedBall C r : ℝ) ≤ Real.pi * (r + D) ^ 2 := hb r (by linarith)
    _ ≤ Real.pi * ((1 + ε) * r ^ 2) := by
        exact mul_le_mul_of_nonneg_left hkey Real.pi_pos.le
    _ = (1 + ε) * Real.pi * r ^ 2 := by ring

/-- Unconditional consequence of `1`-separation alone: every Voronoi cell
truncated at radius `1/2` has area at least `π/4`. -/
theorem quarterPi_le_voronoiCell_volume (C : FourColorConfig) {p : Plane}
    (hp : p ∈ C.carrier) :
    ENNReal.ofReal (Real.pi / 4) ≤
      volume (voronoiCell C p ∩ closedBall p (1 / 2)) := by
  have hsub : ball p (1 / 2) ⊆ voronoiCell C p ∩ closedBall p (1 / 2) :=
    Set.subset_inter (ball_subset_voronoiCell C hp) ball_subset_closedBall
  have hball : volume (ball p (1 / 2)) = ENNReal.ofReal (Real.pi / 4) := by
    rw [EuclideanSpace.volume_ball_fin_two, ← ENNReal.ofReal_pow (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rw [← hball]
  exact measure_mono hsub

/-- Unconditional density bound coming from `1`-separation alone.  This is
weaker than Conjecture 4.1 (it gives `4/π ≈ 1.273` instead of `1`), but it is
proved outright and is a sanity check on the counting machinery. -/
theorem count_le_four_of_separation (C : FourColorConfig) (r : ℝ) (hr : 0 ≤ r) :
    (countInClosedBall C r : ℝ) ≤ 4 * (r + 1 / 2) ^ 2 := by
  have h := count_mul_le_of_cell_volume_ge C (Real.pi / 4) (1 / 2) (by norm_num)
    (fun p hp => quarterPi_le_voronoiCell_volume C hp) r hr
  have hpi : 0 < Real.pi := Real.pi_pos
  nlinarith [h, hpi, sq_nonneg (r + 1 / 2)]

end Conjecture41
