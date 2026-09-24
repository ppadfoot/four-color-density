import Conjecture41.VertexSum

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The quotient Euler identity `F = 2 V`

Every corner of a quotient face has a vertex in the periodization, hence a
*unique* representative in `P.points` together with a unique integer lattice
shift.  Regrouping the finitely many quotient corners by that representative is
an exact partition, and over each representative the corners are in bijection
with the corners of the global fan triangulation at that site.  Therefore the
total corner angle `∑_{k,j} dangleQ k j` can be evaluated in two ways:

* by faces, using `sum_dangleQ`, it equals `nF · π`;
* by vertex orbits, using `sum_dangleQ_at_site`, it equals `#points · 2π`.

Since `π > 0` this gives the Euler identity `nF = 2 · #points`.
-/

namespace Conjecture41

open MeasureTheory Set Metric EuclideanGeometry
open scoped Real

namespace PeriodicConfig

variable (P : PeriodicConfig) (hne : P.points.Nonempty)

/-! ### The representative of the vertex of a quotient corner -/

lemma vertQ_spec (k : Fin (P.nF hne)) (j : Fin 3) :
    ∃ s : Plane, s ∈ P.points ∧ ∃ mn : ℤ × ℤ,
      P.vertQ hne k j = s + latticeVec P.side mn.1 mn.2 := by
  obtain ⟨s, hs, m, n, h⟩ := P.vertQ_mem hne k j
  exact ⟨s, hs, (m, n), h⟩

/-- The representative in `P.points` of the vertex of the quotient corner
`(k, j)`. -/
noncomputable def cSite (k : Fin (P.nF hne)) (j : Fin 3) : Plane :=
  (P.vertQ_spec hne k j).choose

/-- The lattice shift carrying the representative onto the vertex of the
quotient corner `(k, j)`. -/
noncomputable def cShift (k : Fin (P.nF hne)) (j : Fin 3) : ℤ × ℤ :=
  (P.vertQ_spec hne k j).choose_spec.2.choose

lemma cSite_mem (k : Fin (P.nF hne)) (j : Fin 3) : P.cSite hne k j ∈ P.points :=
  (P.vertQ_spec hne k j).choose_spec.1

lemma vertQ_eq_cSite (k : Fin (P.nF hne)) (j : Fin 3) :
    P.vertQ hne k j
      = P.cSite hne k j + latticeVec P.side (P.cShift hne k j).1 (P.cShift hne k j).2 :=
  (P.vertQ_spec hne k j).choose_spec.2.choose_spec

/-- The representative and the shift of a quotient corner are unique. -/
lemma cSite_unique {k : Fin (P.nF hne)} {j : Fin 3} {t : Plane} (ht : t ∈ P.points) {a b : ℤ}
    (h : P.vertQ hne k j = t + latticeVec P.side a b) :
    P.cSite hne k j = t ∧ P.cShift hne k j = (a, b) := by
  have hrep := P.vertQ_eq_cSite hne k j
  have heq : P.cSite hne k j + latticeVec P.side (P.cShift hne k j).1 (P.cShift hne k j).2
      = t + latticeVec P.side a b := by rw [← hrep, h]
  have hst : P.cSite hne k j = t := P.rep_unique (P.cSite_mem hne k j) ht heq
  refine ⟨hst, ?_⟩
  rw [hst] at heq
  have hvec : latticeVec P.side (P.cShift hne k j).1 (P.cShift hne k j).2
      = latticeVec P.side a b := add_left_cancel heq
  obtain ⟨h1, h2⟩ := latticeVec_injective P.side_pos hvec
  exact Prod.ext h1 h2

/-! ### The family triangle attached to a quotient corner -/

/-- The member of the global triangle family whose corner `j` sits exactly at
the representative `cSite k j`. -/
noncomputable def cornerFam (k : Fin (P.nF hne)) (j : Fin 3) : Fin (P.nF hne) × ℤ × ℤ :=
  (k, -(P.cShift hne k j).1, -(P.cShift hne k j).2)

lemma vert_cornerFam (k : Fin (P.nF hne)) (j : Fin 3) :
    P.vertQ hne (P.cornerFam hne k j).1 j
        + latticeVec P.side (P.cornerFam hne k j).2.1 (P.cornerFam hne k j).2.2
      = P.cSite hne k j := by
  show P.vertQ hne k j + latticeVec P.side (-(P.cShift hne k j).1) (-(P.cShift hne k j).2)
      = P.cSite hne k j
  rw [P.vertQ_eq_cSite hne k j, add_assoc, latticeVec_add]
  simp

lemma cornerFam_mem_incF (k : Fin (P.nF hne)) (j : Fin 3) :
    P.cornerFam hne k j ∈ P.incF hne (P.cSite hne k j) := by
  rw [P.mem_incF hne, ← P.vert_cornerFam hne k j]
  exact P.mem_famTri_of_vert hne _ j

/-- A site is a vertex of a family triangle for exactly one of the three corner
indices. -/
lemma vertQ_index_unique {k : Fin (P.nF hne)} {m n : ℤ} {j j' : Fin 3}
    (h : P.vertQ hne k j + latticeVec P.side m n = P.vertQ hne k j' + latticeVec P.side m n) :
    j = j' :=
  (P.deloneLift hne).dvert_injective (P.isFanIndex_face hne k) (add_right_cancel h)

lemma cornerIdx_cornerFam (k : Fin (P.nF hne)) (j : Fin 3) :
    P.cornerIdx hne (P.cSite hne k j) (P.cornerFam hne k j) = j := by
  have hex : ∃ i : Fin 3, P.vertQ hne (P.cornerFam hne k j).1 i
      + latticeVec P.side (P.cornerFam hne k j).2.1 (P.cornerFam hne k j).2.2
        = P.cSite hne k j := ⟨j, P.vert_cornerFam hne k j⟩
  have hspec := P.cornerIdx_spec hne hex
  exact P.vertQ_index_unique hne (hspec.trans (P.vert_cornerFam hne k j).symm)

/-! ### Regrouping the corners by vertex orbit -/

lemma mem_carrier_of_mem_points {s : Plane} (hs : s ∈ P.points) :
    s ∈ (P.deloneLift hne).carrier := by
  refine ⟨s, hs, 0, 0, ?_⟩
  simp

/-- **The corners of the quotient faces sitting over a fixed representative are
in bijection with the corners of the global fan triangulation at that site.** -/
theorem sum_fiber_eq (s : Plane) (hs : s ∈ P.points) :
    ∑ c ∈ Finset.univ.filter (fun c : Fin (P.nF hne) × Fin 3 => P.cSite hne c.1 c.2 = s),
        P.dangleQ hne c.1 c.2
      = ∑ p ∈ P.incF hne s, P.dangleQ hne p.1 (P.cornerIdx hne s p) := by
  classical
  refine Finset.sum_nbij' (i := fun c => P.cornerFam hne c.1 c.2)
    (j := fun p => (p.1, P.cornerIdx hne s p)) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    have hcs : P.cSite hne c.1 c.2 = s := (Finset.mem_filter.mp hc).2
    have := P.cornerFam_mem_incF hne c.1 c.2
    rwa [hcs] at this
  · intro p hp
    have hmem : s ∈ P.famTri hne p := (P.mem_incF hne).mp hp
    have hex := P.exists_vert_eq_of_mem_famTri hne (P.mem_carrier_of_mem_points hne hs) hmem
    have hspec := P.cornerIdx_spec hne hex
    have hrep : P.vertQ hne p.1 (P.cornerIdx hne s p)
        = s + latticeVec P.side (-p.2.1) (-p.2.2) := by
      have hx : s + latticeVec P.side (-p.2.1) (-p.2.2)
          = (P.vertQ hne p.1 (P.cornerIdx hne s p) + latticeVec P.side p.2.1 p.2.2)
            + latticeVec P.side (-p.2.1) (-p.2.2) := by rw [hspec]
      rw [hx, add_assoc, latticeVec_add]
      simp
    have := (P.cSite_unique hne hs hrep).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩
  · intro c hc
    have hcs : P.cSite hne c.1 c.2 = s := (Finset.mem_filter.mp hc).2
    have h1 : P.cornerIdx hne s (P.cornerFam hne c.1 c.2) = c.2 := by
      rw [← hcs]; exact P.cornerIdx_cornerFam hne c.1 c.2
    exact Prod.ext rfl h1
  · intro p hp
    have hmem : s ∈ P.famTri hne p := (P.mem_incF hne).mp hp
    have hex := P.exists_vert_eq_of_mem_famTri hne (P.mem_carrier_of_mem_points hne hs) hmem
    have hspec := P.cornerIdx_spec hne hex
    have hrep : P.vertQ hne p.1 (P.cornerIdx hne s p)
        = s + latticeVec P.side (-p.2.1) (-p.2.2) := by
      have hx : s + latticeVec P.side (-p.2.1) (-p.2.2)
          = (P.vertQ hne p.1 (P.cornerIdx hne s p) + latticeVec P.side p.2.1 p.2.2)
            + latticeVec P.side (-p.2.1) (-p.2.2) := by rw [hspec]
      rw [hx, add_assoc, latticeVec_add]
      simp
    have h2 := (P.cSite_unique hne hs hrep).2
    show P.cornerFam hne p.1 (P.cornerIdx hne s p) = p
    rw [cornerFam, h2]
    exact Prod.ext rfl (Prod.ext (by simp) (by simp))
  · intro c hc
    have hcs : P.cSite hne c.1 c.2 = s := (Finset.mem_filter.mp hc).2
    have h1 : P.cornerIdx hne s (P.cornerFam hne c.1 c.2) = c.2 := by
      rw [← hcs]; exact P.cornerIdx_cornerFam hne c.1 c.2
    rw [h1]
    rfl

/-- **The total corner angle, summed by vertex orbits.** -/
theorem sum_dangleQ_by_vertices :
    ∑ k : Fin (P.nF hne), ∑ j : Fin 3, P.dangleQ hne k j = P.points.card * (2 * π) := by
  classical
  have hmaps : ∀ c : Fin (P.nF hne) × Fin 3, c ∈ (Finset.univ : Finset (Fin (P.nF hne) × Fin 3)) →
      P.cSite hne c.1 c.2 ∈ P.points := fun c _ => P.cSite_mem hne c.1 c.2
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun c : Fin (P.nF hne) × Fin 3 =>
    P.dangleQ hne c.1 c.2)
  have hval : ∀ s ∈ P.points,
      ∑ c ∈ Finset.univ.filter (fun c : Fin (P.nF hne) × Fin 3 => P.cSite hne c.1 c.2 = s),
        P.dangleQ hne c.1 c.2 = 2 * π := by
    intro s hs
    rw [P.sum_fiber_eq hne s hs]
    exact P.sum_dangleQ_at_site hne (P.mem_carrier_of_mem_points hne hs)
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul,
    Fintype.sum_prod_type] at hfib
  exact hfib.symm

/-- **The total corner angle, summed by faces.** -/
theorem sum_dangleQ_by_faces :
    ∑ k : Fin (P.nF hne), ∑ j : Fin 3, P.dangleQ hne k j = P.nF hne * π := by
  rw [Finset.sum_congr rfl (fun k _ => P.sum_dangleQ hne k), Finset.sum_const, nsmul_eq_mul]
  simp

/-- **The quotient Euler identity.** -/
theorem euler_identity : P.nF hne = 2 * P.points.card := by
  have h := (P.sum_dangleQ_by_faces hne).symm.trans (P.sum_dangleQ_by_vertices hne)
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hcast : ((P.nF hne : ℕ) : ℝ) = ((2 * P.points.card : ℕ) : ℝ) := by
    push_cast
    have h2 : (P.nF hne : ℝ) * π = (2 * P.points.card : ℝ) * π := by
      rw [h]; ring
    exact mul_right_cancel₀ (ne_of_gt hpi) h2
  exact Nat.cast_injective hcast

end PeriodicConfig

end Conjecture41
