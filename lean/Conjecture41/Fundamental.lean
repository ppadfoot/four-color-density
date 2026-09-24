import Conjecture41.PlaneUtil
import Conjecture41.Periodic

set_option autoImplicit false

/-!
# The half-open fundamental square of the period lattice

The quotient constructions of gates G5d and G5e need a *canonical* choice of
representative in every `L·ℤ²`-orbit of the plane.  We use the half-open
square `[0,L) × [0,L)` and the coordinate-wise floor reduction

```
fold L x = x - L·(⌊x₀/L⌋, ⌊x₁/L⌋) .
```

This file proves that `fold` lands in the fundamental square, differs from the
identity by a lattice vector, is lattice invariant, is the identity on the
fundamental square, and that the fundamental square contains at most one point
of every orbit.
-/

namespace Conjecture41

open Metric Set

@[simp] lemma sub_latticeVec_zero_apply (x : Plane) (L : ℝ) (m n : ℤ) :
    (x - latticeVec L m n) 0 = x 0 - L * m := by simp [latticeVec]

@[simp] lemma sub_latticeVec_one_apply (x : Plane) (L : ℝ) (m n : ℤ) :
    (x - latticeVec L m n) 1 = x 1 - L * n := by simp [latticeVec]

/-- Membership in the half-open fundamental square `[0,L) × [0,L)`. -/
def InFund (L : ℝ) (x : Plane) : Prop := 0 ≤ x 0 ∧ x 0 < L ∧ 0 ≤ x 1 ∧ x 1 < L

/-- The canonical lattice reduction into the half-open fundamental square. -/
noncomputable def fold (L : ℝ) (x : Plane) : Plane :=
  x - latticeVec L ⌊x 0 / L⌋ ⌊x 1 / L⌋

private lemma fold_coord {L : ℝ} (hL : 0 < L) (u : ℝ) :
    0 ≤ u - L * (⌊u / L⌋ : ℝ) ∧ u - L * (⌊u / L⌋ : ℝ) < L := by
  have h1 : (⌊u / L⌋ : ℝ) ≤ u / L := Int.floor_le _
  have h2 : u / L < (⌊u / L⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hL] at h1
  rw [div_lt_iff₀ hL] at h2
  constructor <;> nlinarith

/-- `fold` lands in the fundamental square. -/
lemma inFund_fold {L : ℝ} (hL : 0 < L) (x : Plane) : InFund L (fold L x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [fold] using (fold_coord hL (x 0)).1
  · simpa [fold] using (fold_coord hL (x 0)).2
  · simpa [fold] using (fold_coord hL (x 1)).1
  · simpa [fold] using (fold_coord hL (x 1)).2

/-- `fold` differs from the identity by a lattice vector. -/
lemma fold_add_shift (L : ℝ) (x : Plane) :
    fold L x + latticeVec L ⌊x 0 / L⌋ ⌊x 1 / L⌋ = x := by
  simp [fold]

lemma fold_eq_add (L : ℝ) (x : Plane) :
    fold L x = x + latticeVec L (-⌊x 0 / L⌋) (-⌊x 1 / L⌋) := by
  unfold fold
  rw [← latticeVec_neg]
  abel

lemma exists_fold_eq_add (L : ℝ) (x : Plane) : ∃ m n : ℤ, fold L x = x + latticeVec L m n :=
  ⟨_, _, fold_eq_add L x⟩

lemma exists_shift_fold (L : ℝ) (x : Plane) :
    ∃ m n : ℤ, fold L x + latticeVec L m n = x :=
  ⟨_, _, fold_add_shift L x⟩

/-- `fold` is invariant under the period lattice. -/
lemma fold_add_latticeVec {L : ℝ} (hL : 0 < L) (x : Plane) (m n : ℤ) :
    fold L (x + latticeVec L m n) = fold L x := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  have e0 : ((x + latticeVec L m n) 0) / L = x 0 / L + (m : ℝ) := by
    rw [add_latticeVec_zero_apply]
    field_simp
  have e1 : ((x + latticeVec L m n) 1) / L = x 1 / L + (n : ℝ) := by
    rw [add_latticeVec_one_apply]
    field_simp
  have f0 : ⌊((x + latticeVec L m n) 0) / L⌋ = ⌊x 0 / L⌋ + m := by
    rw [e0, Int.floor_add_intCast]
  have f1 : ⌊((x + latticeVec L m n) 1) / L⌋ = ⌊x 1 / L⌋ + n := by
    rw [e1, Int.floor_add_intCast]
  unfold fold
  rw [f0, f1, ← latticeVec_add]
  abel

/-- The fundamental square meets every orbit at most once. -/
lemma latticeVec_eq_zero_of_inFund {L : ℝ} (hL : 0 < L) {x y : Plane} (hx : InFund L x)
    (hy : InFund L y) {m n : ℤ} (h : x = y + latticeVec L m n) : m = 0 ∧ n = 0 := by
  have h0 : x 0 = y 0 + L * (m : ℝ) := by rw [h]; simp
  have h1 : x 1 = y 1 + L * (n : ℝ) := by rw [h]; simp
  obtain ⟨hx0, hx0', hx1, hx1'⟩ := hx
  obtain ⟨hy0, hy0', hy1, hy1'⟩ := hy
  constructor
  · have hm1 : L * (m : ℝ) < L := by linarith
    have hm2 : -L < L * (m : ℝ) := by linarith
    have : (-1 : ℝ) < (m : ℝ) := by
      by_contra hc
      push_neg at hc
      nlinarith
    have : (m : ℝ) < 1 := by
      by_contra hc
      push_neg at hc
      nlinarith
    have hm : (-1 : ℤ) < m := by exact_mod_cast ‹(-1 : ℝ) < (m : ℝ)›
    have hm' : m < 1 := by exact_mod_cast ‹(m : ℝ) < 1›
    omega
  · have hm1 : L * (n : ℝ) < L := by linarith
    have hm2 : -L < L * (n : ℝ) := by linarith
    have : (-1 : ℝ) < (n : ℝ) := by
      by_contra hc
      push_neg at hc
      nlinarith
    have : (n : ℝ) < 1 := by
      by_contra hc
      push_neg at hc
      nlinarith
    have hm : (-1 : ℤ) < n := by exact_mod_cast ‹(-1 : ℝ) < (n : ℝ)›
    have hm' : n < 1 := by exact_mod_cast ‹(n : ℝ) < 1›
    omega

lemma eq_of_inFund {L : ℝ} (hL : 0 < L) {x y : Plane} (hx : InFund L x)
    (hy : InFund L y) {m n : ℤ} (h : x = y + latticeVec L m n) : x = y := by
  obtain ⟨rfl, rfl⟩ := latticeVec_eq_zero_of_inFund hL hx hy h
  simpa using h

/-- `fold` fixes the fundamental square. -/
lemma fold_eq_self {L : ℝ} (hL : 0 < L) {x : Plane} (hx : InFund L x) : fold L x = x := by
  refine eq_of_inFund hL (inFund_fold hL x) hx (m := -⌊x 0 / L⌋) (n := -⌊x 1 / L⌋) ?_
  unfold fold
  rw [← latticeVec_neg]
  abel

/-- The fundamental square is bounded. -/
lemma norm_le_of_inFund {L : ℝ} (hL : 0 < L) {x : Plane} (hx : InFund L x) : ‖x‖ ≤ 2 * L := by
  obtain ⟨hx0, hx0', hx1, hx1'⟩ := hx
  have h0 : |x 0 - (0 : Plane) 0| ≤ L := by
    rw [show ((0 : Plane) 0) = 0 from rfl, sub_zero, abs_of_nonneg hx0]
    linarith
  have h1 : |x 1 - (0 : Plane) 1| ≤ L := by
    rw [show ((0 : Plane) 1) = 0 from rfl, sub_zero, abs_of_nonneg hx1]
    linarith
  have := dist_le_of_coord_le h0 h1
  rw [dist_zero_right] at this
  refine this.trans ?_
  have h2 : Real.sqrt (L ^ 2 + L ^ 2) ≤ Real.sqrt ((2 * L) ^ 2) := by
    apply Real.sqrt_le_sqrt; nlinarith
  rw [Real.sqrt_sq (by positivity)] at h2
  exact h2

end Conjecture41
