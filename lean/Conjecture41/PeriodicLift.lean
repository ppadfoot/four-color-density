import Conjecture41.Periodic

set_option autoImplicit false

/-!
# The lifted configuration of a periodic configuration

A `PeriodicConfig` records a finite set of representatives together with the
statement that its `L·ℤ²`-periodization satisfies every colored exclusion
inequality.  Here we build that periodization as an honest `FourColorConfig`:
its carrier is the full periodic point set and its coloring is the periodic
extension of the coloring of the representatives.

The uniqueness of the representation `x = s + L·(m,n)` follows from validity
alone (distinct points of a valid configuration are at distance at least one),
so the periodic coloring is well defined.
-/

namespace Conjecture41

open Metric

namespace PeriodicConfig

variable (P : PeriodicConfig)

/-- The full periodic point set. -/
def latticeSet : Set Plane :=
  {x | ∃ s ∈ P.points, ∃ m n : ℤ, x = s + latticeVec P.side m n}

lemma latticeVec_sub (L : ℝ) (m n m' n' : ℤ) :
    latticeVec L m' n' - latticeVec L m n = latticeVec L (m' - m) (n' - n) := by
  ext i
  fin_cases i <;> simp [latticeVec] <;> ring

lemma latticeVec_injective {L : ℝ} (hL : 0 < L) {m n m' n' : ℤ}
    (h : latticeVec L m n = latticeVec L m' n') : m = m' ∧ n = n' := by
  have h0 : L * (m : ℝ) = L * (m' : ℝ) := by
    have := congrArg (fun x : Plane => x 0) h
    simpa using this
  have h1 : L * (n : ℝ) = L * (n' : ℝ) := by
    have := congrArg (fun x : Plane => x 1) h
    simpa using this
  refine ⟨?_, ?_⟩
  · have : (m : ℝ) = (m' : ℝ) := mul_left_cancel₀ (ne_of_gt hL) h0
    exact_mod_cast this
  · have : (n : ℝ) = (n' : ℝ) := mul_left_cancel₀ (ne_of_gt hL) h1
    exact_mod_cast this

/-- Translating both points by lattice vectors reduces to a single lattice
translation. -/
lemma dist_lattice_translate (s t : Plane) (m n m' n' : ℤ) :
    dist (s + latticeVec P.side m n) (t + latticeVec P.side m' n')
      = dist s (t + latticeVec P.side (m' - m) (n' - n)) := by
  rw [dist_eq_norm, dist_eq_norm, ← latticeVec_sub P.side m n m' n']
  congr 1
  abel

/-- Validity of the periodization, in the form needed for the lift. -/
lemma valid_lattice {s t : Plane} (hs : s ∈ P.points) (ht : t ∈ P.points) (m n m' n' : ℤ)
    (hne : s + latticeVec P.side m n ≠ t + latticeVec P.side m' n') :
    exclusionSq (P.color s) (P.color t)
      ≤ dist (s + latticeVec P.side m n) (t + latticeVec P.side m' n') ^ 2 := by
  rw [dist_lattice_translate]
  refine P.valid s hs t ht (m' - m) (n' - n) ?_
  rintro ⟨rfl, hm, hn⟩
  refine hne ?_
  have : m' = m := by omega
  have hn' : n' = n := by omega
  rw [this, hn']

/-- The representation of a point of the periodic set is unique. -/
lemma rep_unique {s t : Plane} (hs : s ∈ P.points) (ht : t ∈ P.points) {m n m' n' : ℤ}
    (h : s + latticeVec P.side m n = t + latticeVec P.side m' n') : s = t := by
  by_contra hst
  have hzero : dist s (t + latticeVec P.side (m' - m) (n' - n)) = 0 := by
    rw [← dist_lattice_translate, h, dist_self]
  have hval := P.valid s hs t ht (m' - m) (n' - n) (by rintro ⟨rfl, _, _⟩; exact hst rfl)
  rw [hzero] at hval
  have h1 := one_le_exclusionSq (P.color s) (P.color t)
  norm_num at hval
  linarith

/-- The periodic extension of the coloring. -/
noncomputable def liftColor (x : Plane) : Color := by
  classical
  exact if h : ∃ s, s ∈ P.points ∧ ∃ m n : ℤ, x = s + latticeVec P.side m n
    then P.color h.choose else 0

lemma liftColor_eq {s : Plane} (hs : s ∈ P.points) (m n : ℤ) :
    P.liftColor (s + latticeVec P.side m n) = P.color s := by
  classical
  have hex : ∃ s', s' ∈ P.points ∧ ∃ m' n' : ℤ,
      s + latticeVec P.side m n = s' + latticeVec P.side m' n' := ⟨s, hs, m, n, rfl⟩
  rw [liftColor, dif_pos hex]
  obtain ⟨hs', m', n', hrep⟩ := hex.choose_spec
  rw [P.rep_unique hs' hs hrep.symm]

/-- The lifted colouring is invariant under the period lattice. -/
lemma liftColor_add_latticeVec (x : Plane) (m n : ℤ) :
    P.liftColor (x + latticeVec P.side m n) = P.liftColor x := by
  classical
  by_cases hx : ∃ s, s ∈ P.points ∧ ∃ m' n' : ℤ, x = s + latticeVec P.side m' n'
  · obtain ⟨s, hs, m', n', rfl⟩ := hx
    rw [add_assoc, latticeVec_add, P.liftColor_eq hs, P.liftColor_eq hs]
  · have hx' : ¬ ∃ s, s ∈ P.points ∧ ∃ m' n' : ℤ,
        x + latticeVec P.side m n = s + latticeVec P.side m' n' := by
      rintro ⟨s, hs, m', n', h⟩
      refine hx ⟨s, hs, m' - m, n' - n, ?_⟩
      have : x = s + latticeVec P.side m' n' - latticeVec P.side m n := by
        rw [← h]; abel
      rw [this, ← latticeVec_sub P.side m n m' n']
      abel
    rw [liftColor, liftColor, dif_neg hx, dif_neg hx']

/-- The lifted colouring is invariant under subtracting a period. -/
lemma liftColor_sub_latticeVec (x : Plane) (m n : ℤ) :
    P.liftColor (x - latticeVec P.side m n) = P.liftColor x := by
  have : x - latticeVec P.side m n = x + latticeVec P.side (-m) (-n) := by
    rw [← latticeVec_neg]; abel
  rw [this, P.liftColor_add_latticeVec]

/-- The periodization of a `PeriodicConfig` as a four-colored configuration. -/
noncomputable def lift : FourColorConfig where
  carrier := P.latticeSet
  color := P.liftColor
  valid := by
    rintro x y ⟨s, hs, m, n, rfl⟩ ⟨t, ht, m', n', rfl⟩ hne
    rw [P.liftColor_eq hs, P.liftColor_eq ht]
    exact P.valid_lattice hs ht m n m' n' hne

@[simp] lemma lift_carrier : (P.lift).carrier = P.latticeSet := rfl

@[simp] lemma lift_color : (P.lift).color = P.liftColor := rfl

lemma mem_lift_carrier {s : Plane} (hs : s ∈ P.points) (m n : ℤ) :
    s + latticeVec P.side m n ∈ (P.lift).carrier := ⟨s, hs, m, n, rfl⟩

end PeriodicConfig

end Conjecture41
