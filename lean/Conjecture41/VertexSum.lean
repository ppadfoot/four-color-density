import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Conjecture41.VertexAngle
import Conjecture41.QuotientArea

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The angles around a site add up to `2π`

The fan triangles of the periodization tile the plane, and a *site* can only
occur as a vertex of a fan triangle (`exists_dvert_eq_of_mem_delTri`).  Hence
for a small enough radius `r` the disc of radius `r` around a site `s` is
covered, up to a null set, by the corners at `s` of the finitely many fan
triangles having `s` as a vertex.  Comparing areas gives

`∑ (angles at s) = 2π`.

This is the analytic half of the Euler identity `nF = 2 V`.
-/

namespace Conjecture41

open MeasureTheory Set Metric EuclideanGeometry
open scoped ENNReal Real

/-- The corner angle is translation invariant. -/
lemma DeloneSet.dangle_translate (D : DeloneSet) {w : Plane}
    (hw : (fun p : Plane => p + w) '' D.carrier = D.carrier) (v : Plane) (i : ℕ) (j : Fin 3) :
    D.dangle (v + w) i j = D.dangle v i j := by
  have h : ∀ k : Fin 3, D.dvert (v + w) i k = D.dvert v i k + w :=
    fun k => D.dvert_translate hw v i k
  simp only [dangle, h]
  simp only [EuclideanGeometry.angle, vsub_eq_sub]
  congr 1 <;> abel_nf

/-- The area of a disc of radius `r` in the plane. -/
lemma volume_ball_plane (c : Plane) {r : ℝ} (hr : 0 < r) :
    volume (ball c r) = ENNReal.ofReal (π * r ^ 2) := by
  rw [EuclideanSpace.volume_ball]
  have hc : Fintype.card (Fin 2) = 2 := by simp
  rw [hc, show ((2 : ℕ) : ℝ) / 2 + 1 = 2 by norm_num, Real.Gamma_two,
    Real.sq_sqrt Real.pi_pos.le, ← ENNReal.ofReal_pow hr.le,
    ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

namespace PeriodicConfig

variable (P : PeriodicConfig) (hne : P.points.Nonempty)

/-- The plane fan index of the member `p` of the global triangle family. -/
noncomputable def famIdx (p : Fin (P.nF hne) × ℤ × ℤ) : Plane × ℕ :=
  ((P.face hne p.1).1 + latticeVec P.side p.2.1 p.2.2, (P.face hne p.1).2)

lemma famTri_eq_delTri (p : Fin (P.nF hne) × ℤ × ℤ) :
    P.famTri hne p = (P.deloneLift hne).delTri (P.famIdx hne p).1 (P.famIdx hne p).2 := rfl

lemma isFanIndex_famIdx (p : Fin (P.nF hne) × ℤ × ℤ) :
    (P.deloneLift hne).IsFanIndex (P.famIdx hne p).1 (P.famIdx hne p).2 :=
  P.isFanIndex_famTri hne p

lemma famIdx_inj : Function.Injective (P.famIdx hne) := P.famIdx_injective hne

lemma dvert_famIdx (p : Fin (P.nF hne) × ℤ × ℤ) (j : Fin 3) :
    (P.deloneLift hne).dvert (P.famIdx hne p).1 (P.famIdx hne p).2 j
      = P.vertQ hne p.1 j + latticeVec P.side p.2.1 p.2.2 :=
  (P.deloneLift hne).dvert_translate (P.latticeInv hne p.2.1 p.2.2) _ _ j

/-- The corner angle of the `j`-th vertex of the `k`-th quotient face. -/
noncomputable def dangleQ (k : Fin (P.nF hne)) (j : Fin 3) : ℝ :=
  (P.deloneLift hne).dangle (P.face hne k).1 (P.face hne k).2 j

lemma dangleQ_eq (k : Fin (P.nF hne)) (j : Fin 3) :
    P.dangleQ hne k j = ∠ (P.vertQ hne k (j + 1)) (P.vertQ hne k j) (P.vertQ hne k (j + 2)) := rfl

lemma dangleQ_nonneg (k : Fin (P.nF hne)) (j : Fin 3) : 0 ≤ P.dangleQ hne k j :=
  (P.deloneLift hne).dangle_nonneg _ _ _

lemma dangle_famIdx (p : Fin (P.nF hne) × ℤ × ℤ) (j : Fin 3) :
    (P.deloneLift hne).dangle (P.famIdx hne p).1 (P.famIdx hne p).2 j = P.dangleQ hne p.1 j :=
  (P.deloneLift hne).dangle_translate (P.latticeInv hne p.2.1 p.2.2) _ _ j

/-- **The sum of the three angles of a quotient face is `π`.** -/
theorem sum_dangleQ (k : Fin (P.nF hne)) : ∑ j : Fin 3, P.dangleQ hne k j = π :=
  (P.deloneLift hne).sum_dangle (P.isFanIndex_face hne k)

/-! ### The triangles of the family meeting a small ball around a site -/

lemma finite_famMeet (s : Plane) (rad : ℝ) :
    {p : Fin (P.nF hne) × ℤ × ℤ | (P.famTri hne p ∩ closedBall s rad).Nonempty}.Finite := by
  have hfin := (P.deloneLift hne).finite_fanIndices s rad
  have hsub : {p : Fin (P.nF hne) × ℤ × ℤ | (P.famTri hne p ∩ closedBall s rad).Nonempty}
      ⊆ (P.famIdx hne) ⁻¹'
        {q : Plane × ℕ | (P.deloneLift hne).IsFanIndex q.1 q.2 ∧
          ((P.deloneLift hne).delTri q.1 q.2 ∩ closedBall s rad).Nonempty} := by
    intro p hp
    exact ⟨P.isFanIndex_famIdx hne p, by rw [← P.famTri_eq_delTri hne p]; exact hp⟩
  exact Set.Finite.subset (hfin.preimage (Set.injOn_of_injective (P.famIdx_inj hne))) hsub

/-- The vertices of a family triangle. -/
lemma mem_famTri_of_vert (p : Fin (P.nF hne) × ℤ × ℤ) (j : Fin 3) :
    P.vertQ hne p.1 j + latticeVec P.side p.2.1 p.2.2 ∈ P.famTri hne p := by
  rw [P.famTri_eq_delTri hne p, ← P.dvert_famIdx hne p j,
    (P.deloneLift hne).delTri_eq_convexHull_cyclic _ _ j]
  exact subset_convexHull ℝ _ (Set.mem_insert _ _)

lemma exists_vert_eq_of_mem_famTri {s : Plane} (hs : s ∈ (P.deloneLift hne).carrier)
    {p : Fin (P.nF hne) × ℤ × ℤ} (hmem : s ∈ P.famTri hne p) :
    ∃ j : Fin 3, P.vertQ hne p.1 j + latticeVec P.side p.2.1 p.2.2 = s := by
  obtain ⟨j, hj⟩ := (P.deloneLift hne).exists_dvert_eq_of_mem_delTri
    (P.isFanIndex_famIdx hne p) hs (by rw [← P.famTri_eq_delTri hne p]; exact hmem)
  exact ⟨j, by rw [← P.dvert_famIdx hne p j]; exact hj⟩

/-- The corner of the family triangle `p` which meets the site `s`. -/
noncomputable def cornerIdx (s : Plane) (p : Fin (P.nF hne) × ℤ × ℤ) : Fin 3 :=
  if h : ∃ j : Fin 3, P.vertQ hne p.1 j + latticeVec P.side p.2.1 p.2.2 = s
    then h.choose else 0

lemma cornerIdx_spec {s : Plane} {p : Fin (P.nF hne) × ℤ × ℤ}
    (h : ∃ j : Fin 3, P.vertQ hne p.1 j + latticeVec P.side p.2.1 p.2.2 = s) :
    P.vertQ hne p.1 (P.cornerIdx hne s p) + latticeVec P.side p.2.1 p.2.2 = s := by
  rw [cornerIdx, dif_pos h]
  exact h.choose_spec

/-! ### The corners incident to a site -/

lemma isCompact_famTri (p : Fin (P.nF hne) × ℤ × ℤ) : IsCompact (P.famTri hne p) := by
  rw [P.famTri_eq_delTri hne p, (P.deloneLift hne).delTri_eq_dvert]
  exact (((Set.finite_singleton _).insert _).insert _).isCompact_convexHull

lemma famTri_nonempty (p : Fin (P.nF hne) × ℤ × ℤ) : (P.famTri hne p).Nonempty :=
  ⟨_, P.mem_famTri_of_vert hne p 0⟩

lemma finite_incSet (s : Plane) :
    {p : Fin (P.nF hne) × ℤ × ℤ | s ∈ P.famTri hne p}.Finite := by
  refine (P.finite_famMeet hne s 0).subset ?_
  intro p hp
  exact ⟨s, hp, mem_closedBall_self le_rfl⟩

/-- The finite set of family triangles having the site `s` as a vertex. -/
noncomputable def incF (s : Plane) : Finset (Fin (P.nF hne) × ℤ × ℤ) :=
  (P.finite_incSet hne s).toFinset

lemma mem_incF {s : Plane} {p : Fin (P.nF hne) × ℤ × ℤ} :
    p ∈ P.incF hne s ↔ s ∈ P.famTri hne p := by
  simp [incF]

lemma dvert_cornerIdx {s : Plane} (hs : s ∈ (P.deloneLift hne).carrier)
    {p : Fin (P.nF hne) × ℤ × ℤ} (hp : s ∈ P.famTri hne p) :
    (P.deloneLift hne).dvert (P.famIdx hne p).1 (P.famIdx hne p).2 (P.cornerIdx hne s p) = s := by
  rw [P.dvert_famIdx hne p]
  exact P.cornerIdx_spec hne (P.exists_vert_eq_of_mem_famTri hne hs hp)

/-- The radius below which the corner of the family triangle `p` at the site
`s` is exactly a circular sector. -/
noncomputable def cornerThrF (s : Plane) (p : Fin (P.nF hne) × ℤ × ℤ) : ℝ :=
  (P.deloneLift hne).cornerThr (P.famIdx hne p).1 (P.famIdx hne p).2 (P.cornerIdx hne s p)

lemma cornerThrF_pos (s : Plane) (p : Fin (P.nF hne) × ℤ × ℤ) : 0 < P.cornerThrF hne s p :=
  (P.deloneLift hne).cornerThr_pos (P.isFanIndex_famIdx hne p) _

/-- Near an incident site a family triangle is a circular sector of its corner
angle. -/
lemma volume_famTri_inter_ball {s : Plane} (hs : s ∈ (P.deloneLift hne).carrier)
    {p : Fin (P.nF hne) × ℤ × ℤ} (hp : s ∈ P.famTri hne p) {r : ℝ} (hr : 0 < r)
    (hle : r ≤ P.cornerThrF hne s p) :
    volume (P.famTri hne p ∩ ball s r)
      = ENNReal.ofReal (P.dangleQ hne p.1 (P.cornerIdx hne s p) * r ^ 2 / 2) := by
  have hv := P.dvert_cornerIdx hne hs hp
  have h := (P.deloneLift hne).volume_delTri_inter_ball (P.isFanIndex_famIdx hne p)
    (P.cornerIdx hne s p) hr hle
  rw [hv] at h
  rw [P.famTri_eq_delTri hne p, h, P.dangle_famIdx hne p]

/-- **The corner angles at a site add up to `2π`.** -/
theorem sum_dangleQ_at_site {s : Plane} (hs : s ∈ (P.deloneLift hne).carrier) :
    ∑ p ∈ P.incF hne s, P.dangleQ hne p.1 (P.cornerIdx hne s p) = 2 * π := by
  classical
  set F : Finset (Fin (P.nF hne) × ℤ × ℤ) := (P.finite_famMeet hne s 1).toFinset with hF
  have hmemF : ∀ p : Fin (P.nF hne) × ℤ × ℤ,
      p ∈ F ↔ (P.famTri hne p ∩ closedBall s 1).Nonempty := by
    intro p; simp [hF]
  have hincsubF : P.incF hne s ⊆ F := by
    intro p hp
    rw [hmemF]
    exact ⟨s, (P.mem_incF hne).mp hp, mem_closedBall_self zero_le_one⟩
  set f : (Fin (P.nF hne) × ℤ × ℤ) → ℝ := fun p =>
    if p ∈ P.incF hne s then P.cornerThrF hne s p else infDist s (P.famTri hne p) with hf
  have hfpos : ∀ p ∈ F, 0 < f p := by
    intro p _
    by_cases hinc : p ∈ P.incF hne s
    · simp only [hf, if_pos hinc]
      exact P.cornerThrF_pos hne s p
    · simp only [hf, if_neg hinc]
      refine (IsClosed.notMem_iff_infDist_pos (P.isCompact_famTri hne p).isClosed
        (P.famTri_nonempty hne p)).mp ?_
      exact fun hcon => hinc ((P.mem_incF hne).mpr hcon)
  set R : Finset ℝ := insert 1 (F.image f) with hR
  have hRne : R.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  set r : ℝ := R.min' hRne with hrdef
  have hrpos : 0 < r := by
    have hmem : r ∈ R := R.min'_mem hRne
    rw [hR, Finset.mem_insert] at hmem
    rcases hmem with h | h
    · rw [h]; norm_num
    · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp h
      rw [← hpe]
      exact hfpos p hp
  have hr1 : r ≤ 1 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hrle : ∀ p ∈ F, r ≤ f p := fun p hp =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f hp))
  have hzero : ∀ p ∉ P.incF hne s, volume (P.famTri hne p ∩ ball s r) = 0 := by
    intro p hp
    have hempty : P.famTri hne p ∩ ball s r = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hx1, hx2⟩
      rw [mem_ball, dist_comm] at hx2
      by_cases hpF : p ∈ F
      · have hrf := hrle p hpF
        simp only [hf, if_neg hp] at hrf
        have hdd : infDist s (P.famTri hne p) ≤ dist s x := infDist_le_dist_of_mem hx1
        linarith
      · refine hpF ?_
        rw [hmemF]
        exact ⟨x, hx1, by rw [mem_closedBall, dist_comm]; linarith⟩
    rw [hempty, measure_empty]
  have hcover := tsum_volume_inter_of_cover (P.famTri hne)
    (fun p => (P.measurableSet_famTri hne p).nullMeasurableSet)
    (P.pairwise_aedisjoint_famTri hne) (P.iUnion_famTri hne)
    (measurableSet_ball (x := s) (ε := r))
  rw [tsum_eq_sum hzero, volume_ball_plane s hrpos] at hcover
  have hnn : ∀ p ∈ P.incF hne s,
      0 ≤ P.dangleQ hne p.1 (P.cornerIdx hne s p) * r ^ 2 / 2 := by
    intro p _
    have := P.dangleQ_nonneg hne p.1 (P.cornerIdx hne s p)
    have h2 : (0:ℝ) ≤ r ^ 2 := sq_nonneg r
    have := mul_nonneg this h2
    linarith
  have hsum : ∑ p ∈ P.incF hne s, volume (P.famTri hne p ∩ ball s r)
      = ENNReal.ofReal
        (∑ p ∈ P.incF hne s, P.dangleQ hne p.1 (P.cornerIdx hne s p) * r ^ 2 / 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg hnn]
    refine Finset.sum_congr rfl fun p hp => ?_
    refine P.volume_famTri_inter_ball hne hs ((P.mem_incF hne).mp hp) hrpos ?_
    have hrf := hrle p (hincsubF hp)
    simpa only [hf, if_pos hp] using hrf
  rw [hsum] at hcover
  have heq : ∑ p ∈ P.incF hne s, P.dangleQ hne p.1 (P.cornerIdx hne s p) * r ^ 2 / 2
      = π * r ^ 2 :=
    (ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg hnn) (by positivity)).mp hcover
  have hfac : (∑ p ∈ P.incF hne s, P.dangleQ hne p.1 (P.cornerIdx hne s p)) * (r ^ 2 / 2)
      = (2 * π) * (r ^ 2 / 2) := by
    rw [Finset.sum_mul]
    have : ∑ p ∈ P.incF hne s, P.dangleQ hne p.1 (P.cornerIdx hne s p) * (r ^ 2 / 2)
        = ∑ p ∈ P.incF hne s, P.dangleQ hne p.1 (P.cornerIdx hne s p) * r ^ 2 / 2 :=
      Finset.sum_congr rfl fun p _ => by ring
    rw [this, heq]; ring
  exact mul_right_cancel₀ (by positivity) hfac

end PeriodicConfig

end Conjecture41
