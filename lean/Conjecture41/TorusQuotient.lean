import Conjecture41.Darts
import Conjecture41.Fundamental
import Conjecture41.PeriodicDelaunay

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The finite quotient of the periodic fan triangulation (gate G5d)

Let `P` be a nonempty periodic configuration with period lattice
`Λ = P.side · ℤ²` and let `D = P.deloneLift` be its periodization, a Delone
set.  The global canonical fan family of `D` (see `GlobalTriangulation.lean`)
is `Λ`-equivariant, so it descends to the quotient torus.  This file makes the
quotient explicit:

* `PeriodicConfig.FanRepSet` — the fan indices whose Delaunay centre lies in
  the half-open fundamental square; this set is finite and meets every
  `Λ`-orbit of fan indices exactly once;
* `PeriodicConfig.nF`, `PeriodicConfig.face` — the resulting indexing of the
  face orbits by `Fin nF`;
* `PeriodicConfig.pfQ`, `PeriodicConfig.trQ` — the dart pairing on the quotient
  and the *integer* lattice shift attached to each dart, together with the
  matching identities, the involution property, and fixed-point freeness.
-/

namespace Conjecture41

open Metric Set

/-- Reduce the centre of a dart into the fundamental square. -/
noncomputable def foldDart (L : ℝ) (d : Plane × ℕ × Fin 3) : Plane × ℕ × Fin 3 :=
  (fold L d.1, d.2)

namespace PeriodicConfig

variable (P : PeriodicConfig) (hne : P.points.Nonempty)

/-- The periodization is invariant under every period translation. -/
lemma latticeInv (m n : ℤ) :
    (fun p : Plane => p + latticeVec P.side m n) '' (P.deloneLift hne).carrier
      = (P.deloneLift hne).carrier := P.latticeSet_add_latticeVec m n

lemma isFanIndex_fold {v : Plane} {i : ℕ} (h : (P.deloneLift hne).IsFanIndex v i) :
    (P.deloneLift hne).IsFanIndex (fold P.side v) i := by
  obtain ⟨m, n, hmn⟩ := exists_fold_eq_add P.side v
  rw [hmn]
  exact ((P.deloneLift hne).isFanIndex_translate (P.latticeInv hne m n) v i).mpr h

/-! ### The finite set of face representatives -/

/-- Fan indices whose Delaunay centre lies in the half-open fundamental
square. -/
def FanRepSet : Set (Plane × ℕ) :=
  {p : Plane × ℕ | (P.deloneLift hne).IsFanIndex p.1 p.2 ∧ InFund P.side p.1}

/-- **There are only finitely many face orbits.** -/
theorem finite_fanRepSet : (P.FanRepSet hne).Finite := by
  refine ((P.deloneLift hne).finite_fanIndices 0
    (2 * P.side + (P.deloneLift hne).cov)).subset ?_
  rintro ⟨v, i⟩ ⟨hidx, hfund⟩
  refine ⟨hidx, ⟨(P.deloneLift hne).dvert v i 0, ?_, ?_⟩⟩
  · exact subset_convexHull ℝ _ (Set.mem_insert _ _)
  · have hmem : (P.deloneLift hne).dvert v i 0 ∈ (P.deloneLift hne).delTri v i :=
      subset_convexHull ℝ _ (Set.mem_insert _ _)
    have h1 : (P.deloneLift hne).dvert v i 0 ∈ closedBall v (P.deloneLift hne).cov :=
      (P.deloneLift hne).delCell_subset_closedBall v
        ((P.deloneLift hne).delTri_subset_delCell hidx.1 hidx.2.2 hmem)
    rw [mem_closedBall] at h1 ⊢
    have h2 : ‖v‖ ≤ 2 * P.side := norm_le_of_inFund P.side_pos hfund
    have h3 := dist_triangle ((P.deloneLift hne).dvert v i 0) v 0
    simp only [dist_zero_right] at h3 ⊢
    linarith

/-- The finite set of face representatives. -/
noncomputable def fanRep : Finset (Plane × ℕ) := (P.finite_fanRepSet hne).toFinset

lemma mem_fanRep {p : Plane × ℕ} : p ∈ P.fanRep hne ↔
    (P.deloneLift hne).IsFanIndex p.1 p.2 ∧ InFund P.side p.1 := by
  simp [fanRep, FanRepSet]

/-- The number of face orbits of the quotient torus. -/
noncomputable def nF : ℕ := (P.fanRep hne).card

/-- The chosen representative of the `k`-th face orbit. -/
noncomputable def face (k : Fin (P.nF hne)) : Plane × ℕ :=
  ((P.fanRep hne).equivFin.symm k : Plane × ℕ)

lemma face_mem (k : Fin (P.nF hne)) : P.face hne k ∈ P.fanRep hne :=
  ((P.fanRep hne).equivFin.symm k).2

lemma isFanIndex_face (k : Fin (P.nF hne)) :
    (P.deloneLift hne).IsFanIndex (P.face hne k).1 (P.face hne k).2 :=
  ((P.mem_fanRep hne).mp (P.face_mem hne k)).1

lemma inFund_face (k : Fin (P.nF hne)) : InFund P.side (P.face hne k).1 :=
  ((P.mem_fanRep hne).mp (P.face_mem hne k)).2

lemma face_injective : Function.Injective (P.face hne) := by
  intro a b h
  exact (P.fanRep hne).equivFin.symm.injective (Subtype.ext h)

lemma exists_face {p : Plane × ℕ} (hp : p ∈ P.fanRep hne) : ∃ k, P.face hne k = p :=
  ⟨(P.fanRep hne).equivFin ⟨p, hp⟩, by simp [face]⟩

/-! ### Darts of the quotient -/

/-- The plane dart underlying a quotient dart. -/
noncomputable def liftDart (d : Fin (P.nF hne) × Fin 3) : Plane × ℕ × Fin 3 :=
  ((P.face hne d.1).1, (P.face hne d.1).2, d.2)

lemma liftDart_injective : Function.Injective (P.liftDart hne) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ h
  simp only [liftDart, Prod.mk.injEq] at h
  have hab : P.face hne a = P.face hne b := Prod.ext h.1 h.2.1
  exact Prod.ext (P.face_injective hne hab) h.2.2

lemma isFanIndex_liftDart (d : Fin (P.nF hne) × Fin 3) :
    (P.deloneLift hne).IsFanIndex (P.liftDart hne d).1 (P.liftDart hne d).2.1 :=
  P.isFanIndex_face hne d.1

lemma inFund_liftDart (d : Fin (P.nF hne) × Fin 3) :
    InFund P.side (P.liftDart hne d).1 := P.inFund_face hne d.1

lemma exists_liftDart_foldDart (d : Fin (P.nF hne) × Fin 3) :
    ∃ e : Fin (P.nF hne) × Fin 3,
      P.liftDart hne e
        = foldDart P.side ((P.deloneLift hne).revDart (P.liftDart hne d)) := by
  set r := (P.deloneLift hne).revDart (P.liftDart hne d) with hr
  have hidx : (P.deloneLift hne).IsFanIndex r.1 r.2.1 :=
    (P.deloneLift hne).isFanIndex_revDart (P.isFanIndex_liftDart hne d)
  have hmem : (fold P.side r.1, r.2.1) ∈ P.fanRep hne :=
    (P.mem_fanRep hne).mpr ⟨P.isFanIndex_fold hne hidx, inFund_fold P.side_pos _⟩
  obtain ⟨k, hk⟩ := P.exists_face hne hmem
  refine ⟨(k, r.2.2), ?_⟩
  simp only [liftDart, hk, foldDart]

/-- The dart pairing of the quotient torus. -/
noncomputable def pfQ (d : Fin (P.nF hne) × Fin 3) : Fin (P.nF hne) × Fin 3 :=
  if h : ∃ e : Fin (P.nF hne) × Fin 3,
      P.liftDart hne e
        = foldDart P.side ((P.deloneLift hne).revDart (P.liftDart hne d))
    then h.choose else d

lemma liftDart_pfQ (d : Fin (P.nF hne) × Fin 3) :
    P.liftDart hne (P.pfQ hne d)
      = foldDart P.side ((P.deloneLift hne).revDart (P.liftDart hne d)) := by
  rw [pfQ, dif_pos (P.exists_liftDart_foldDart hne d)]
  exact (P.exists_liftDart_foldDart hne d).choose_spec

/-! ### Vertices of the quotient faces -/

/-- The three vertices of the `k`-th quotient face, in positive orientation. -/
noncomputable def vertQ (k : Fin (P.nF hne)) (j : Fin 3) : Plane :=
  (P.deloneLift hne).dvert (P.face hne k).1 (P.face hne k).2 j

lemma vertQ_eq (d : Fin (P.nF hne) × Fin 3) (j : Fin 3) :
    P.vertQ hne d.1 j
      = (P.deloneLift hne).dvert (P.liftDart hne d).1 (P.liftDart hne d).2.1 j := rfl

lemma vertQ_mem (k : Fin (P.nF hne)) (j : Fin 3) : P.vertQ hne k j ∈ (P.lift).carrier :=
  (P.deloneLift hne).dvert_mem_carrier (P.isFanIndex_face hne k) j

lemma cross_vertQ_pos (k : Fin (P.nF hne)) :
    0 < cross (P.vertQ hne k 0) (P.vertQ hne k 1) (P.vertQ hne k 2) :=
  (P.deloneLift hne).cross_dvert_pos (P.isFanIndex_face hne k)

/-! ### The lattice shift of a dart -/

/-- The reverse, in the plane, of the dart underlying a quotient dart. -/
noncomputable def revLift (d : Fin (P.nF hne) × Fin 3) : Plane × ℕ × Fin 3 :=
  (P.deloneLift hne).revDart (P.liftDart hne d)

lemma isFanIndex_revLift (d : Fin (P.nF hne) × Fin 3) :
    (P.deloneLift hne).IsFanIndex (P.revLift hne d).1 (P.revLift hne d).2.1 :=
  (P.deloneLift hne).isFanIndex_revDart (P.isFanIndex_liftDart hne d)

lemma isRev_revLift (d : Fin (P.nF hne) × Fin 3) :
    (P.deloneLift hne).IsRev (P.revLift hne d) (P.liftDart hne d) :=
  (P.deloneLift hne).isRev_revDart (P.isFanIndex_liftDart hne d)

lemma liftDart_pfQ' (d : Fin (P.nF hne) × Fin 3) :
    P.liftDart hne (P.pfQ hne d) = foldDart P.side (P.revLift hne d) := P.liftDart_pfQ hne d

lemma revDart_revLift (d : Fin (P.nF hne) × Fin 3) :
    (P.deloneLift hne).revDart (P.revLift hne d) = P.liftDart hne d :=
  (P.deloneLift hne).revDart_revDart (P.isFanIndex_liftDart hne d)

/-- The **integer** lattice shift attached to a quotient dart. -/
noncomputable def trIdx (d : Fin (P.nF hne) × Fin 3) : ℤ × ℤ :=
  (⌊(P.revLift hne d).1 0 / P.side⌋, ⌊(P.revLift hne d).1 1 / P.side⌋)

/-- The lattice translation attached to a quotient dart. -/
noncomputable def trQ (d : Fin (P.nF hne) × Fin 3) : Plane :=
  (P.revLift hne d).1 - fold P.side (P.revLift hne d).1

/-- The dart translation really is the period-lattice vector of the recorded
integer shift. -/
lemma trQ_eq_latticeVec (d : Fin (P.nF hne) × Fin 3) :
    P.trQ hne d = latticeVec P.side (P.trIdx hne d).1 (P.trIdx hne d).2 := by
  have h := fold_add_shift P.side (P.revLift hne d).1
  show (P.revLift hne d).1 - fold P.side (P.revLift hne d).1
      = latticeVec P.side ⌊(P.revLift hne d).1 0 / P.side⌋ ⌊(P.revLift hne d).1 1 / P.side⌋
  exact sub_eq_of_eq_add' h.symm

lemma latticeInv' {w : Plane} {m n : ℤ} (h : w = latticeVec P.side m n) :
    (fun p : Plane => p + w) '' (P.deloneLift hne).carrier = (P.deloneLift hne).carrier := by
  rw [h]; exact P.latticeInv hne m n

lemma neg_trQ_eq (d : Fin (P.nF hne) × Fin 3) :
    -(P.trQ hne d) = latticeVec P.side (-(P.trIdx hne d).1) (-(P.trIdx hne d).2) := by
  rw [← latticeVec_neg, P.trQ_eq_latticeVec hne d]

lemma fold_revLift (d : Fin (P.nF hne) × Fin 3) :
    fold P.side (P.revLift hne d).1 = (P.revLift hne d).1 + -(P.trQ hne d) := by
  unfold trQ; abel

/-! ### The pairing identities -/

lemma pfQ_snd (d : Fin (P.nF hne) × Fin 3) : (P.pfQ hne d).2 = (P.revLift hne d).2.2 := by
  have h := congrArg (fun e : Plane × ℕ × Fin 3 => e.2.2) (P.liftDart_pfQ hne d)
  exact h

lemma vertQ_pfQ_add_trQ (d : Fin (P.nF hne) × Fin 3) (j : Fin 3) :
    P.vertQ hne (P.pfQ hne d).1 j + P.trQ hne d
      = (P.deloneLift hne).dvert (P.revLift hne d).1 (P.revLift hne d).2.1 j := by
  have hw := P.latticeInv' hne (P.neg_trQ_eq hne d)
  rw [P.vertQ_eq hne (P.pfQ hne d) j, P.liftDart_pfQ hne d]
  show (P.deloneLift hne).dvert (fold P.side (P.revLift hne d).1) (P.revLift hne d).2.1 j
      + P.trQ hne d = _
  rw [P.fold_revLift hne d, (P.deloneLift hne).dvert_translate hw]
  abel

/-- **Endpoint matching, left.** -/
theorem match_leftQ (d : Fin (P.nF hne) × Fin 3) :
    P.vertQ hne (P.pfQ hne d).1 ((P.pfQ hne d).2 + 2) + P.trQ hne d
      = P.vertQ hne d.1 (d.2 + 1) := by
  rw [P.pfQ_snd hne d, P.vertQ_pfQ_add_trQ hne d ((P.revLift hne d).2.2 + 2)]
  exact (P.isRev_revLift hne d).2.2

/-- **Endpoint matching, right.** -/
theorem match_rightQ (d : Fin (P.nF hne) × Fin 3) :
    P.vertQ hne (P.pfQ hne d).1 ((P.pfQ hne d).2 + 1) + P.trQ hne d
      = P.vertQ hne d.1 (d.2 + 2) := by
  rw [P.pfQ_snd hne d, P.vertQ_pfQ_add_trQ hne d ((P.revLift hne d).2.2 + 1)]
  exact (P.isRev_revLift hne d).2.1

/-! ### The pairing is a fixed-point-free involution -/

/-- **The quotient dart pairing is an involution.** -/
theorem pfQ_pfQ (d : Fin (P.nF hne) × Fin 3) : P.pfQ hne (P.pfQ hne d) = d := by
  refine P.liftDart_injective hne ?_
  have hw := P.latticeInv' hne (P.neg_trQ_eq hne d)
  have hfd : P.liftDart hne (P.pfQ hne d)
      = ((P.revLift hne d).1 + -(P.trQ hne d), (P.revLift hne d).2) := by
    rw [P.liftDart_pfQ' hne d]
    unfold foldDart
    rw [P.fold_revLift hne d]
  have hfold : fold P.side ((P.liftDart hne d).1 + -(P.trQ hne d))
      = (P.liftDart hne d).1 := by
    rw [P.neg_trQ_eq hne d, fold_add_latticeVec P.side_pos,
      fold_eq_self P.side_pos (P.inFund_liftDart hne d)]
  rw [P.liftDart_pfQ hne (P.pfQ hne d), hfd,
    (P.deloneLift hne).revDart_translate hw (P.isFanIndex_revLift hne d),
    P.revDart_revLift hne d]
  unfold foldDart
  rw [hfold]

/-- **The quotient dart pairing is fixed-point free.** -/
theorem pfQ_ne (d : Fin (P.nF hne) × Fin 3) : P.pfQ hne d ≠ d := by
  intro hcon
  have hl : P.liftDart hne d = foldDart P.side (P.revLift hne d) := by
    rw [← P.liftDart_pfQ' hne d, hcon]
  have h1 : (P.liftDart hne d).1 = (P.revLift hne d).1 + -(P.trQ hne d) := by
    rw [hl]; unfold foldDart; rw [P.fold_revLift hne d]
  have h2 : (P.liftDart hne d).2 = (P.revLift hne d).2 := by rw [hl]; rfl
  have h21 : (P.liftDart hne d).2.1 = (P.revLift hne d).2.1 := congrArg Prod.fst h2
  have h22 : (P.liftDart hne d).2.2 = (P.revLift hne d).2.2 := congrArg Prod.snd h2
  have hw := P.latticeInv' hne (P.neg_trQ_eq hne d)
  have hkey : ∀ j : Fin 3,
      (P.deloneLift hne).dvert (P.liftDart hne d).1 (P.liftDart hne d).2.1 j
        = (P.deloneLift hne).dvert (P.revLift hne d).1 (P.revLift hne d).2.1 j
            + -(P.trQ hne d) := by
    intro j
    rw [h1, h21]
    exact (P.deloneLift hne).dvert_translate hw _ _ j
  have hrev := P.isRev_revLift hne d
  have hA : (P.deloneLift hne).dvert (P.revLift hne d).1 (P.revLift hne d).2.1
        ((P.revLift hne d).2.2 + 1)
      = (P.deloneLift hne).dvert (P.revLift hne d).1 (P.revLift hne d).2.1
        ((P.revLift hne d).2.2 + 2) + -(P.trQ hne d) := by
    rw [hrev.2.1, hkey, h22]
  have hB : (P.deloneLift hne).dvert (P.revLift hne d).1 (P.revLift hne d).2.1
        ((P.revLift hne d).2.2 + 2)
      = (P.deloneLift hne).dvert (P.revLift hne d).1 (P.revLift hne d).2.1
        ((P.revLift hne d).2.2 + 1) + -(P.trQ hne d) := by
    rw [hrev.2.2, hkey, h22]
  have hsum : (0 : Plane) = -(P.trQ hne d) + -(P.trQ hne d) := by
    have e1 : (P.deloneLift hne).dvert (P.revLift hne d).1 (P.revLift hne d).2.1
          ((P.revLift hne d).2.2 + 1)
        - (P.deloneLift hne).dvert (P.revLift hne d).1 (P.revLift hne d).2.1
          ((P.revLift hne d).2.2 + 2) = -(P.trQ hne d) := by
      rw [hA]; abel
    have e2 : (P.deloneLift hne).dvert (P.revLift hne d).1 (P.revLift hne d).2.1
          ((P.revLift hne d).2.2 + 2)
        - (P.deloneLift hne).dvert (P.revLift hne d).1 (P.revLift hne d).2.1
          ((P.revLift hne d).2.2 + 1) = -(P.trQ hne d) := by
      rw [hB]; abel
    calc (0 : Plane)
        = ((P.deloneLift hne).dvert (P.revLift hne d).1 (P.revLift hne d).2.1
              ((P.revLift hne d).2.2 + 1)
            - (P.deloneLift hne).dvert (P.revLift hne d).1 (P.revLift hne d).2.1
              ((P.revLift hne d).2.2 + 2))
          + ((P.deloneLift hne).dvert (P.revLift hne d).1 (P.revLift hne d).2.1
              ((P.revLift hne d).2.2 + 2)
            - (P.deloneLift hne).dvert (P.revLift hne d).1 (P.revLift hne d).2.1
              ((P.revLift hne d).2.2 + 1)) := by abel
      _ = -(P.trQ hne d) + -(P.trQ hne d) := by rw [e1, e2]
  have ht0 : P.trQ hne d = 0 := by
    have hneg : -(P.trQ hne d + P.trQ hne d) = 0 := by rw [neg_add]; exact hsum.symm
    have hdd : P.trQ hne d + P.trQ hne d = 0 := neg_eq_zero.mp hneg
    have h2s : (2 : ℝ) • P.trQ hne d = 0 := by rw [two_smul]; exact hdd
    rcases smul_eq_zero.mp h2s with h | h
    · exact absurd h (by norm_num)
    · exact h
  rw [ht0] at hA
  simp only [neg_zero, add_zero] at hA
  exact (P.deloneLift hne).dvert_ne_of_ne (P.isFanIndex_revLift hne d)
    (fin3_add_one_ne_add_two (P.revLift hne d).2.2) hA

/-! ### The weak Delaunay condition and the colour weights -/

/-- The apex of the paired face, translated onto the shared edge. -/
lemma vertQ_pfQ_apex (d : Fin (P.nF hne) × Fin 3) :
    P.vertQ hne (P.pfQ hne d).1 (P.pfQ hne d).2 + P.trQ hne d
      = (P.deloneLift hne).dvert (P.revLift hne d).1 (P.revLift hne d).2.1
          (P.revLift hne d).2.2 := by
  rw [P.pfQ_snd hne d, P.vertQ_pfQ_add_trQ hne d (P.revLift hne d).2.2]

/-- **The weak Delaunay in-circle inequality for every quotient dart.** -/
theorem delaunayQ (d : Fin (P.nF hne) × Fin 3) :
    0 ≤ inCircleDet (P.vertQ hne d.1 d.2) (P.vertQ hne d.1 (d.2 + 1))
      (P.vertQ hne d.1 (d.2 + 2)) (P.vertQ hne (P.pfQ hne d).1 (P.pfQ hne d).2 + P.trQ hne d) := by
  rw [P.vertQ_pfQ_apex hne d]
  have hmem := (P.deloneLift hne).dvert_mem_carrier (P.isFanIndex_revLift hne d)
    (P.revLift hne d).2.2
  exact (P.deloneLift hne).inCircleDet_dvert_nonneg (P.isFanIndex_liftDart hne d) d.2 hmem

lemma liftColor_add_trQ (d : Fin (P.nF hne) × Fin 3) (x : Plane) :
    P.liftColor (x + P.trQ hne d) = P.liftColor x := by
  rw [P.trQ_eq_latticeVec hne d]
  exact P.liftColor_add_latticeVec x _ _

/-- **The exclusion weight of an edge is the same seen from either side.** -/
theorem weight_eqQ (d : Fin (P.nF hne) × Fin 3) :
    exclusionSq ((P.lift).color (P.vertQ hne (P.pfQ hne d).1 ((P.pfQ hne d).2 + 1)))
        ((P.lift).color (P.vertQ hne (P.pfQ hne d).1 ((P.pfQ hne d).2 + 2)))
      = exclusionSq ((P.lift).color (P.vertQ hne d.1 (d.2 + 1)))
        ((P.lift).color (P.vertQ hne d.1 (d.2 + 2))) := by
  have c1 : (P.lift).color (P.vertQ hne (P.pfQ hne d).1 ((P.pfQ hne d).2 + 1))
      = (P.lift).color (P.vertQ hne d.1 (d.2 + 2)) := by
    show P.liftColor _ = P.liftColor _
    rw [← P.match_rightQ hne d]
    exact (P.liftColor_add_trQ hne d _).symm
  have c2 : (P.lift).color (P.vertQ hne (P.pfQ hne d).1 ((P.pfQ hne d).2 + 2))
      = (P.lift).color (P.vertQ hne d.1 (d.2 + 1)) := by
    show P.liftColor _ = P.liftColor _
    rw [← P.match_leftQ hne d]
    exact (P.liftColor_add_trQ hne d _).symm
  rw [c1, c2, exclusionSq_comm]

end PeriodicConfig

end Conjecture41
