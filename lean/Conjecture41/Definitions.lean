import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Finset.Sort
import Mathlib.Data.ZMod.Basic
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Conjecture41

open Metric Set

/-- The Euclidean plane with its standard Euclidean norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The four colors, with cyclic arithmetic modulo four. -/
abbrev Color := ZMod 4

/--
The squared exclusion distance between colors.  The values, in cyclic order,
are `2, 5/4, 1, 5/4`: equal colors, adjacent colors, opposite colors,
adjacent colors.
-/
noncomputable def exclusionSq (i j : Color) : ℝ :=
  if i = j then 2
  else if j = i + 2 then 1
  else 5 / 4

/-- The exclusion weights are always at least one. -/
lemma one_le_exclusionSq (i j : Color) : 1 ≤ exclusionSq i j := by
  unfold exclusionSq
  split_ifs <;> norm_num

/-- The exclusion weights are always at most two. -/
lemma exclusionSq_le_two (i j : Color) : exclusionSq i j ≤ 2 := by
  unfold exclusionSq
  split_ifs <;> norm_num

/-- Being at cyclic distance two is a symmetric relation on the four colors. -/
lemma opposite_symm : ∀ i j : Color, (j = i + 2) ↔ (i = j + 2) := by decide

/-- The exclusion weight is symmetric in its two arguments. -/
lemma exclusionSq_comm (i j : Color) : exclusionSq i j = exclusionSq j i := by
  unfold exclusionSq
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    by_cases h2 : j = i + 2
    · rw [if_pos h2, if_pos ((opposite_symm i j).mp h2)]
    · rw [if_neg h2, if_neg (fun hc => h2 ((opposite_symm i j).mpr hc))]

/--
A four-colored point configuration in the plane.  The color map is total, but
only its restriction to `carrier` is mathematically relevant.

No local-finiteness hypothesis is included: it must be derived from `valid`.
-/
structure FourColorConfig where
  carrier : Set Plane
  color : Plane → Color
  valid : ∀ ⦃x y : Plane⦄,
    x ∈ carrier → y ∈ carrier → x ≠ y →
      exclusionSq (color x) (color y) ≤ dist x y ^ 2

/-- Validity implies the color-independent separation distance one. -/
lemma uniformlySeparated
    (C : FourColorConfig) {x y : Plane}
    (hx : x ∈ C.carrier) (hy : y ∈ C.carrier) (hxy : x ≠ y) :
    1 ≤ dist x y := by
  have h := C.valid hx hy hxy
  have h1 : (1 : ℝ) ≤ dist x y ^ 2 := le_trans (one_le_exclusionSq _ _) h
  nlinarith [dist_nonneg (x := x) (y := y)]

/-- Validity implies finiteness in every bounded closed ball. -/
lemma finiteInClosedBall (C : FourColorConfig) (r : ℝ) :
    (C.carrier ∩ closedBall (0 : Plane) r).Finite := by
  classical
  obtain ⟨t, htf, hts⟩ :=
    (Metric.totallyBounded_iff.mp
      (isCompact_closedBall (0 : Plane) r).totallyBounded) (1 / 3) (by norm_num)
  have hmem : ∀ x ∈ C.carrier ∩ closedBall (0 : Plane) r,
      ∃ y ∈ t, dist x y < 1 / 3 := by
    intro x hx
    have hx' := hts hx.2
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hx'
    exact hx'
  choose! f hft hfd using hmem
  refine Set.Finite.of_finite_image (f := f) (htf.subset ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hft x hx
  · intro x hx y hy hxy
    by_contra hne
    have h1 : dist x (f x) < 1 / 3 := hfd x hx
    have h2 : dist y (f y) < 1 / 3 := hfd y hy
    rw [← hxy] at h2
    have : dist x y ≤ dist x (f x) + dist (f x) y := dist_triangle _ _ _
    rw [dist_comm (f x) y] at this
    have hsep := uniformlySeparated C hx.1 hy.1 hne
    linarith

/-- The exact finite set of points in the indicated closed ball. -/
noncomputable def pointsInClosedBall
    (C : FourColorConfig) (r : ℝ) : Finset Plane :=
  (finiteInClosedBall C r).toFinset

/-- Number of points in the closed Euclidean ball centered at the origin. -/
noncomputable def countInClosedBall (C : FourColorConfig) (r : ℝ) : ℕ :=
  (pointsInClosedBall C r).card

lemma mem_pointsInClosedBall {C : FourColorConfig} {r : ℝ} {x : Plane} :
    x ∈ pointsInClosedBall C r ↔ x ∈ C.carrier ∧ dist x 0 ≤ r := by
  simp [pointsInClosedBall, Set.Finite.mem_toFinset, mem_closedBall]

/--
The epsilon/eventual form of upper radial density at most one.  Once local
finiteness is proved, this is equivalent to the limsup statement in
Cohn--Rajagopal Conjecture 4.1.
-/
def UpperRadialDensityAtMostOne (C : FourColorConfig) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ R : ℝ, 1 ≤ R ∧
      ∀ r : ℝ, R ≤ r →
        (countInClosedBall C r : ℝ) ≤
          (1 + ε) * Real.pi * r ^ 2

/-- The radial density ratio whose `limsup` is the density of the published
statement. -/
noncomputable def densityRatio (C : FourColorConfig) (r : ℝ) : ℝ :=
  (countInClosedBall C r : ℝ) / (Real.pi * r ^ 2)

/-- The literal `limsup` form of Cohn--Rajagopal Conjecture 4.1. -/
def LimsupDensityAtMostOne (C : FourColorConfig) : Prop :=
  Filter.limsup (densityRatio C) Filter.atTop ≤ 1

end Conjecture41
