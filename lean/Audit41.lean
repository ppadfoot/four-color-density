import Conjecture41.Main

set_option autoImplicit false

/-!
Independent semantic bridge to Conjecture 4.1, arXiv:2412.00937v3, §4.1.
The input is an arbitrary set, colored only on that set, with the three
published (unsquared) distance thresholds. Local finiteness is a conclusion.
This file is an audit wrapper; it changes no declaration in the proof library.
-/

namespace Audit41

open Conjecture41

lemma adjacent_of_not_same_or_opposite : ∀ i j : Color,
    i ≠ j → j ≠ i + 2 → j = i + 1 ∨ j = i - 1 := by decide

noncomputable def extendColor (S : Set Plane) (c : S → Color) (x : Plane) : Color := by
  classical
  exact if hx : x ∈ S then c ⟨x, hx⟩ else 0

lemma extendColor_mem {S : Set Plane} (c : S → Color) {x : Plane} (hx : x ∈ S) :
    extendColor S c x = c ⟨x, hx⟩ := by
  classical
  simp [extendColor, hx]

/-- The literal published domain and the literal radial counting expression.
No infinitude or discreteness hypothesis is needed: validity gives bounded-set
finiteness, and the theorem also covers finite and empty configurations. -/
theorem published_statement (S : Set Plane) (c : S → Color)
    (hsame : ∀ x y : S, x ≠ y → c x = c y →
      Real.sqrt 2 ≤ dist (x : Plane) (y : Plane))
    (hadjacent : ∀ x y : S, x ≠ y → (c y = c x + 1 ∨ c y = c x - 1) →
      Real.sqrt 5 / 2 ≤ dist (x : Plane) (y : Plane))
    (hopposite : ∀ x y : S, x ≠ y → c y = c x + 2 →
      1 ≤ dist (x : Plane) (y : Plane)) :
    (∀ r : ℝ, (S ∩ Metric.closedBall (0 : Plane) r).Finite) ∧
    Filter.limsup (fun r : ℝ =>
      (((S ∩ Metric.closedBall (0 : Plane) r).ncard : ℕ) : ℝ) /
        (Real.pi * r ^ 2)) Filter.atTop ≤ 1 := by
  classical
  let C : FourColorConfig := {
    carrier := S
    color := extendColor S c
    valid := by
      intro x y hx hy hxy
      have hxy' : (⟨x, hx⟩ : S) ≠ ⟨y, hy⟩ :=
        fun h => hxy (congrArg Subtype.val h)
      rw [extendColor_mem c hx, extendColor_mem c hy]
      unfold exclusionSq
      split_ifs with heq hopp
      · have hd := hsame ⟨x, hx⟩ ⟨y, hy⟩ hxy' heq
        have hs := (sq_le_sq₀ (Real.sqrt_nonneg 2) dist_nonneg).2 hd
        simpa only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] using hs
      · have hd := hopposite ⟨x, hx⟩ ⟨y, hy⟩ hxy' hopp
        have hs := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) dist_nonneg).2 hd
        simpa using hs
      · have hd := hadjacent ⟨x, hx⟩ ⟨y, hy⟩ hxy'
          (adjacent_of_not_same_or_opposite _ _ heq hopp)
        have hs := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ Real.sqrt 5 / 2)
          dist_nonneg).2 hd
        norm_num [div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] at hs ⊢
        exact hs }
  refine ⟨finiteInClosedBall C, ?_⟩
  have hcount : ∀ r : ℝ,
      (S ∩ Metric.closedBall (0 : Plane) r).ncard = countInClosedBall C r := by
    intro r
    rw [Set.ncard_eq_toFinset_card _ (finiteInClosedBall C r)]
    rfl
  simpa only [hcount, LimsupDensityAtMostOne, densityRatio] using
    conjecture_4_1_limsup C

#print published_statement
#print axioms published_statement
#print conjecture_4_1
#print conjecture_4_1_limsup
#print axioms Conjecture41.periodic_density
#print axioms Conjecture41.exists_torusTriangulation
#print axioms Conjecture41.DeloneSet.exists_mem_delCell
#print axioms Conjecture41.PeriodicConfig.area_identity
#print axioms Conjecture41.PeriodicConfig.euler_identity

end Audit41
