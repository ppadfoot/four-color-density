import Conjecture41.PlaneUtil

set_option autoImplicit false

/-!
# Square-periodic colored configurations

This file isolates the *periodic* form of Cohn--Rajagopal Conjecture 4.1.

A `PeriodicConfig` is a finite colored point set `S` together with a side
length `L > 0` such that the `L·ℤ²`-periodization of `S` is a valid
four-colored configuration.  The periodic theorem asserts `#S ≤ L²`, i.e.
`V ≤ A` for the torus `ℝ²/(L·ℤ²)`.

The unrestricted Conjecture 4.1 follows from the periodic theorem by the
buffered periodization argument in `Periodization.lean`.
-/

namespace Conjecture41

open Metric Set

/-- The lattice vector `L·(m, n)`. -/
noncomputable def latticeVec (L : ℝ) (m n : ℤ) : Plane := !₂[L * m, L * n]

@[simp] lemma latticeVec_zero_apply (L : ℝ) (m n : ℤ) :
    (latticeVec L m n) 0 = L * m := by simp [latticeVec]

@[simp] lemma latticeVec_one_apply (L : ℝ) (m n : ℤ) :
    (latticeVec L m n) 1 = L * n := by simp [latticeVec]

@[simp] lemma add_latticeVec_zero_apply (x : Plane) (L : ℝ) (m n : ℤ) :
    (x + latticeVec L m n) 0 = x 0 + L * m := by simp [latticeVec]

@[simp] lemma add_latticeVec_one_apply (x : Plane) (L : ℝ) (m n : ℤ) :
    (x + latticeVec L m n) 1 = x 1 + L * n := by simp [latticeVec]

@[simp] lemma latticeVec_zero_zero (L : ℝ) : latticeVec L 0 0 = 0 := by
  simp [latticeVec]

lemma latticeVec_add (L : ℝ) (m n m' n' : ℤ) :
    latticeVec L m n + latticeVec L m' n' = latticeVec L (m + m') (n + n') := by
  ext i; fin_cases i <;> simp [latticeVec] <;> ring

lemma latticeVec_neg (L : ℝ) (m n : ℤ) : -latticeVec L m n = latticeVec L (-m) (-n) := by
  ext i; fin_cases i <;> simp [latticeVec]

/--
A finite colored point set whose `L·ℤ²`-periodization is valid.

The validity condition is exactly that the (infinite, periodic) set
`{s + L·(m,n) | s ∈ points, (m,n) ∈ ℤ²}` satisfies all colored exclusion
inequalities: no periodicity, saturation, or triangulation is assumed.
-/
structure PeriodicConfig where
  /-- The side length of the square period lattice. -/
  side : ℝ
  side_pos : 0 < side
  /-- The finite set of representatives, one period's worth of points. -/
  points : Finset Plane
  /-- The color of each representative. -/
  color : Plane → Color
  /-- Validity of the whole periodization. -/
  valid : ∀ s ∈ points, ∀ t ∈ points, ∀ m n : ℤ,
    ¬(s = t ∧ m = 0 ∧ n = 0) →
      exclusionSq (color s) (color t) ≤ dist s (t + latticeVec side m n) ^ 2

/--
The periodic form of Conjecture 4.1: a square-periodic valid configuration has
at most one point per unit of fundamental-domain area, `V ≤ A`.

This is gate G6 of the formalization ledger; its proof is the periodic weak
Delaunay/cotangent argument specified in `AuthoritativeProof.lean`.
-/
def PeriodicDensityTheorem : Prop :=
  ∀ P : PeriodicConfig, (P.points.card : ℝ) ≤ P.side ^ 2

end Conjecture41
