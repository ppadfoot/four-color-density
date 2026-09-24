import Conjecture41.Voronoi

set_option autoImplicit false

/-!
# Semantic audit: the epsilon form versus the published `limsup` form

Cohn--Rajagopal Conjecture 4.1 is stated as
`limsup_{r → ∞} #(C ∩ B(0,r)) / (π r²) ≤ 1`.
The Lean skeleton states it in the epsilon/eventual form
`UpperRadialDensityAtMostOne`.

A real-valued `limsup` is a junk value (`sInf ∅ = 0`) when the function is
unbounded above, so the two forms are *not* formally equivalent for an
arbitrary function.  They are equivalent here because the density ratio of a
valid configuration is unconditionally bounded: `1`-separation alone gives
`densityRatio C r ≤ 9 / π` for `r ≥ 1` (`densityRatio_le_of_one_le`).  This
file proves the equivalence, so nothing is lost or gained by using the
epsilon form.
-/

namespace Conjecture41

open Metric Set MeasureTheory Filter

/-- The density ratio is nonnegative. -/
lemma densityRatio_nonneg (C : FourColorConfig) (r : ℝ) : 0 ≤ densityRatio C r := by
  unfold densityRatio
  positivity

/-- Unconditional upper bound for the density ratio, from `1`-separation alone. -/
lemma densityRatio_le_of_one_le (C : FourColorConfig) {r : ℝ} (hr : 1 ≤ r) :
    densityRatio C r ≤ 9 / Real.pi := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < Real.pi * r ^ 2 := by positivity
  have hcount := count_le_four_of_separation C r (by linarith)
  have hstep : 4 * (r + 1 / 2) ^ 2 ≤ 9 * r ^ 2 := by nlinarith
  unfold densityRatio
  rw [div_le_div_iff₀ hden hpi]
  nlinarith [hcount, hstep]

/-- The density ratio is eventually bounded above. -/
lemma isBoundedUnder_densityRatio (C : FourColorConfig) :
    IsBoundedUnder (· ≤ ·) atTop (densityRatio C) := by
  refine ⟨9 / Real.pi, ?_⟩
  rw [eventually_map]
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  exact densityRatio_le_of_one_le C hr

/-- The density ratio is cobounded from below, so its `limsup` is not a junk
value. -/
lemma isCoboundedUnder_densityRatio (C : FourColorConfig) :
    IsCoboundedUnder (· ≤ ·) atTop (densityRatio C) := by
  refine ⟨0, fun a ha => ?_⟩
  rw [eventually_map] at ha
  obtain ⟨r, hr⟩ := ha.exists
  exact le_trans (densityRatio_nonneg C r) hr

/-- The epsilon/eventual form and the `limsup` form of the statement agree. -/
theorem upperRadialDensity_iff_limsup (C : FourColorConfig) :
    UpperRadialDensityAtMostOne C ↔ LimsupDensityAtMostOne C := by
  constructor
  · intro h
    unfold LimsupDensityAtMostOne
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨R, hR1, hR⟩ := h ε hε
    refine limsup_le_of_le (isCoboundedUnder_densityRatio C) ?_
    filter_upwards [eventually_ge_atTop R] with r hr
    have hr1 : (1 : ℝ) ≤ r := le_trans hR1 hr
    have hden : 0 < Real.pi * r ^ 2 := by positivity
    have := hR r hr
    unfold densityRatio
    rw [div_le_iff₀ hden]
    nlinarith [this]
  · intro h ε hε
    have hlt : limsup (densityRatio C) atTop < 1 + ε := by
      have : limsup (densityRatio C) atTop ≤ 1 := h
      linarith
    have hev := eventually_lt_of_limsup_lt hlt (isBoundedUnder_densityRatio C)
    rw [eventually_atTop] at hev
    obtain ⟨a, ha⟩ := hev
    refine ⟨max 1 a, le_max_left _ _, ?_⟩
    intro r hr
    have hr1 : (1 : ℝ) ≤ r := le_trans (le_max_left _ _) hr
    have hra : a ≤ r := le_trans (le_max_right _ _) hr
    have hden : 0 < Real.pi * r ^ 2 := by positivity
    have hlt' := ha r hra
    unfold densityRatio at hlt'
    rw [div_lt_iff₀ hden] at hlt'
    nlinarith [hlt']

end Conjecture41
