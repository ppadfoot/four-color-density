import Conjecture41.PeriodicLift
import Conjecture41.PlaneUtil

set_option autoImplicit false

/-!
# Delone sets in the plane, and the Delone property of a periodic lift

This file introduces the semantic notion used by the geometric part of the
project: a *Delone set* is a subset of the plane which is uniformly discrete
(distinct points are at distance at least one) and relatively dense (every
point of the plane is within a fixed distance `cov` of the set).

We prove:

* local finiteness: a uniformly discrete set meets every closed ball in a
  finite set (`finite_inter_closedBall_of_separated`);
* existence of nearest points (`DeloneSet.exists_nearest`);
* that the `L·ℤ²`-periodization of a nonempty valid `PeriodicConfig` is a
  Delone set with the explicit covering radius `L/√2`
  (`PeriodicConfig.deloneLift`), the covering radius being obtained by
  coordinate rounding in the lattice orbit of a chosen representative.

This is gate G5a (Delone part) of the formalization ledger.
-/

namespace Conjecture41

open Metric Set

/-- A uniformly discrete set meets every closed ball in a finite set. -/
lemma finite_inter_closedBall_of_separated (S : Set Plane)
    (hsep : ∀ ⦃x y : Plane⦄, x ∈ S → y ∈ S → x ≠ y → 1 ≤ dist x y)
    (c : Plane) (r : ℝ) : (S ∩ closedBall c r).Finite := by
  classical
  obtain ⟨t, htf, hts⟩ :=
    (Metric.totallyBounded_iff.mp
      (isCompact_closedBall c r).totallyBounded) (1 / 3) (by norm_num)
  have hmem : ∀ x ∈ S ∩ closedBall c r, ∃ y ∈ t, dist x y < 1 / 3 := by
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
    have h3 : dist x y ≤ dist x (f x) + dist (f x) y := dist_triangle _ _ _
    rw [dist_comm (f x) y] at h3
    have := hsep hx.1 hy.1 hne
    linarith

/--
A Delone set in the plane: uniformly discrete with separation at least one,
and relatively dense with covering radius `cov`.
-/
structure DeloneSet where
  /-- The underlying point set. -/
  carrier : Set Plane
  /-- Distinct points are at distance at least one. -/
  sep : ∀ ⦃x y : Plane⦄, x ∈ carrier → y ∈ carrier → x ≠ y → 1 ≤ dist x y
  /-- The covering radius. -/
  cov : ℝ
  cov_pos : 0 < cov
  /-- Every point of the plane has a carrier point within `cov`. -/
  cover : ∀ z : Plane, ∃ x ∈ carrier, dist z x ≤ cov

namespace DeloneSet

variable (D : DeloneSet)

/-- A Delone set is locally finite. -/
lemma finite_inter_closedBall (c : Plane) (r : ℝ) :
    (D.carrier ∩ closedBall c r).Finite :=
  finite_inter_closedBall_of_separated D.carrier D.sep c r

/-- A Delone set is nonempty. -/
lemma nonempty : D.carrier.Nonempty := by
  obtain ⟨x, hx, -⟩ := D.cover 0
  exact ⟨x, hx⟩

/-- The (finite) set of carrier points in a closed ball, as a `Finset`. -/
noncomputable def ballFinset (c : Plane) (r : ℝ) : Finset Plane :=
  (D.finite_inter_closedBall c r).toFinset

lemma mem_ballFinset {c : Plane} {r : ℝ} {x : Plane} :
    x ∈ D.ballFinset c r ↔ x ∈ D.carrier ∧ dist x c ≤ r := by
  simp [ballFinset, Set.Finite.mem_toFinset, mem_closedBall]

/-- Every point of the plane has a nearest carrier point. -/
lemma exists_nearest (z : Plane) :
    ∃ x ∈ D.carrier, ∀ y ∈ D.carrier, dist z x ≤ dist z y := by
  classical
  obtain ⟨x0, hx0, hx0d⟩ := D.cover z
  set F : Finset Plane := D.ballFinset z D.cov with hF
  have hx0F : x0 ∈ F := by
    rw [hF, D.mem_ballFinset]
    exact ⟨hx0, by rwa [dist_comm]⟩
  have hFne : F.Nonempty := ⟨x0, hx0F⟩
  obtain ⟨x, hxF, hxmin⟩ := F.exists_min_image (fun y => dist z y) hFne
  refine ⟨x, ((D.mem_ballFinset).mp hxF).1, ?_⟩
  intro y hy
  by_cases hyF : y ∈ F
  · exact hxmin y hyF
  · have hyd : ¬ dist y z ≤ D.cov := by
      intro h; exact hyF ((D.mem_ballFinset).mpr ⟨hy, h⟩)
    have hx : dist z x ≤ D.cov := by
      have := ((D.mem_ballFinset).mp hxF).2
      rwa [dist_comm] at this
    have : D.cov < dist z y := by rw [dist_comm]; exact lt_of_not_ge hyd
    linarith

end DeloneSet

/-! ### The lifted periodic set is Delone -/

namespace PeriodicConfig

variable (P : PeriodicConfig)

/-- Points of the periodization are at distance at least one from each other. -/
lemma latticeSet_sep : ∀ ⦃x y : Plane⦄, x ∈ P.latticeSet → y ∈ P.latticeSet → x ≠ y →
    1 ≤ dist x y := by
  intro x y hx hy hxy
  exact uniformlySeparated P.lift (by simpa using hx) (by simpa using hy) hxy

/-- Coordinate rounding: every point of the plane is within `√(L²/2)` of the
lattice orbit of any chosen representative. -/
lemma exists_lattice_near (s : Plane) (z : Plane) :
    ∃ m n : ℤ, dist z (s + latticeVec P.side m n) ≤ Real.sqrt (P.side ^ 2 / 2) := by
  set L := P.side with hL
  have hLpos : 0 < L := P.side_pos
  refine ⟨round ((z 0 - s 0) / L), round ((z 1 - s 1) / L), ?_⟩
  set m := round ((z 0 - s 0) / L) with hm
  set n := round ((z 1 - s 1) / L) with hn
  have key : ∀ (a b : ℝ) (k : ℤ), k = round ((a - b) / L) → |a - (b + L * (k : ℝ))| ≤ L / 2 := by
    intro a b k hk
    have hr : |(a - b) / L - (k : ℝ)| ≤ 1 / 2 := by
      rw [hk]; exact abs_sub_round ((a - b) / L)
    have hL0 : L ≠ 0 := ne_of_gt hLpos
    have hfe : a - (b + L * (k : ℝ)) = L * ((a - b) / L - (k : ℝ)) := by
      field_simp
      ring
    rw [hfe, abs_mul, abs_of_pos hLpos]
    calc L * |(a - b) / L - (k : ℝ)| ≤ L * (1 / 2) :=
          mul_le_mul_of_nonneg_left hr (le_of_lt hLpos)
      _ = L / 2 := by ring
  have h0 : |z 0 - (s + latticeVec L m n) 0| ≤ L / 2 := by
    simp only [add_latticeVec_zero_apply]
    exact key (z 0) (s 0) m hm
  have h1 : |z 1 - (s + latticeVec L m n) 1| ≤ L / 2 := by
    simp only [add_latticeVec_one_apply]
    exact key (z 1) (s 1) n hn
  have := dist_le_of_coord_le h0 h1
  calc dist z (s + latticeVec L m n) ≤ Real.sqrt ((L / 2) ^ 2 + (L / 2) ^ 2) := this
    _ = Real.sqrt (L ^ 2 / 2) := by congr 1; ring

/-- The periodization of a nonempty valid periodic configuration is a Delone
set with covering radius `L/√2`. -/
noncomputable def deloneLift (hne : P.points.Nonempty) : DeloneSet where
  carrier := P.latticeSet
  sep := P.latticeSet_sep
  cov := Real.sqrt (P.side ^ 2 / 2)
  cov_pos := Real.sqrt_pos.mpr (by have := P.side_pos; positivity)
  cover := by
    intro z
    obtain ⟨s, hs⟩ := hne
    obtain ⟨m, n, h⟩ := P.exists_lattice_near s z
    exact ⟨s + latticeVec P.side m n, ⟨s, hs, m, n, rfl⟩, h⟩

@[simp] lemma deloneLift_carrier (hne : P.points.Nonempty) :
    (P.deloneLift hne).carrier = P.latticeSet := rfl

@[simp] lemma deloneLift_cov (hne : P.points.Nonempty) :
    (P.deloneLift hne).cov = Real.sqrt (P.side ^ 2 / 2) := rfl

end PeriodicConfig

end Conjecture41
