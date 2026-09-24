import Conjecture41.TorusQuotient
import Conjecture41.AreaAdditivity

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The quotient area identity (gate G5e, area)

The global canonical fan triangles of the periodization tile the plane and are
permuted freely and transitively over each of the `nF` face orbits by the
period lattice `Λ`.  Intersecting the tiling with the half-open fundamental
square `[0,L)²` and regrouping the (unconditional, `ℝ≥0∞`-valued) sum by orbit
gives

```
∑ f : Fin nF, cross (vert f 0) (vert f 1) (vert f 2) / 2 = L² .
```

The two tilings used are:

* the plane is tiled by the translates `gridSq L m n` of the half-open
  fundamental square, which are genuinely pairwise disjoint;
* the plane is covered by the triangles `famTri (k, m, n)`, which have
  pairwise disjoint interiors, hence are pairwise almost everywhere disjoint
  because they are convex.
-/

namespace Conjecture41

open MeasureTheory Set Metric

/-! ### The half-open fundamental square and its lattice translates -/

/-- The half-open fundamental square, as a set. -/
def fundSq (L : ℝ) : Set Plane := {x : Plane | InFund L x}

lemma fundSq_eq_boxSet (L : ℝ) : fundSq L = boxSet (Ico 0 L) (Ico 0 L) := by
  ext x
  simp only [fundSq, InFund, boxSet, Set.mem_setOf_eq, Set.mem_Ico, and_assoc]

lemma measurableSet_fundSq (L : ℝ) : MeasurableSet (fundSq L) := by
  rw [fundSq_eq_boxSet]
  exact measurableSet_boxSet measurableSet_Ico measurableSet_Ico

lemma volume_fundSq {L : ℝ} (hL : 0 < L) : volume (fundSq L) = ENNReal.ofReal (L ^ 2) := by
  rw [fundSq_eq_boxSet, volume_boxSet measurableSet_Ico measurableSet_Ico, Real.volume_Ico,
    sub_zero, ← ENNReal.ofReal_mul hL.le]
  congr 1
  ring

/-- Translation invariance of the plane Lebesgue measure. -/
lemma volume_image_add (v : Plane) (s : Set Plane) :
    volume ((fun p : Plane => p + v) '' s) = volume s := by
  rw [Set.image_add_right, measure_preimage_add_right]

lemma image_add_inter (v : Plane) (s t : Set Plane) :
    (fun p : Plane => p + v) '' (s ∩ t)
      = ((fun p : Plane => p + v) '' s) ∩ ((fun p : Plane => p + v) '' t) :=
  Set.image_inter (add_left_injective v)

lemma image_add_image_add (v : Plane) (s : Set Plane) :
    (fun p : Plane => p + -v) '' ((fun p : Plane => p + v) '' s) = s := by
  rw [Set.image_image]
  simp

/-- The grid square of index `(m,n)`. -/
def gridSq (L : ℝ) (m n : ℤ) : Set Plane :=
  (fun p : Plane => p + latticeVec L m n) '' fundSq L

lemma mem_gridSq {L : ℝ} {m n : ℤ} {x : Plane} :
    x ∈ gridSq L m n ↔ InFund L (x + latticeVec L (-m) (-n)) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h : y + latticeVec L m n + latticeVec L (-m) (-n) = y := by
      rw [add_assoc, latticeVec_add]; simp
    rw [h]; exact hy
  · intro h
    refine ⟨x + latticeVec L (-m) (-n), h, ?_⟩
    show x + latticeVec L (-m) (-n) + latticeVec L m n = x
    rw [add_assoc, latticeVec_add]
    simp

lemma measurableSet_gridSq (L : ℝ) (m n : ℤ) : MeasurableSet (gridSq L m n) := by
  have : gridSq L m n = (fun p : Plane => p + latticeVec L (-m) (-n)) ⁻¹' fundSq L := by
    ext x; rw [mem_gridSq]; rfl
  rw [this]
  exact (measurableSet_fundSq L).preimage (measurable_add_const _)

lemma pairwise_disjoint_gridSq {L : ℝ} (hL : 0 < L) :
    Pairwise (Function.onFun (AEDisjoint volume) (fun p : ℤ × ℤ => gridSq L p.1 p.2)) := by
  intro p q hpq
  refine measure_mono_null ?_ measure_empty
  rw [Set.subset_empty_iff, Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx1, hx2⟩
  rw [mem_gridSq] at hx1 hx2
  have hrel : x + latticeVec L (-p.1) (-p.2)
      = (x + latticeVec L (-q.1) (-q.2)) + latticeVec L (q.1 - p.1) (q.2 - p.2) := by
    rw [add_assoc, latticeVec_add]
    congr 2 <;> ring
  obtain ⟨h1, h2⟩ := latticeVec_eq_zero_of_inFund hL hx1 hx2 hrel
  exact hpq (Prod.ext (by omega) (by omega))

lemma iUnion_gridSq {L : ℝ} (hL : 0 < L) :
    (⋃ p : ℤ × ℤ, gridSq L p.1 p.2) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  refine ⟨(⌊x 0 / L⌋, ⌊x 1 / L⌋), ?_⟩
  rw [mem_gridSq]
  have h : x + latticeVec L (-⌊x 0 / L⌋) (-⌊x 1 / L⌋) = fold L x := (fold_eq_add L x).symm
  rw [h]
  exact inFund_fold hL x

/-- **The grid squares tile the plane.** -/
theorem tsum_volume_inter_gridSq {L : ℝ} (hL : 0 < L) {s : Set Plane} (hs : MeasurableSet s) :
    ∑' p : ℤ × ℤ, volume (gridSq L p.1 p.2 ∩ s) = volume s :=
  tsum_volume_inter_of_cover (fun p : ℤ × ℤ => gridSq L p.1 p.2)
    (fun p => (measurableSet_gridSq L p.1 p.2).nullMeasurableSet)
    (pairwise_disjoint_gridSq hL) (iUnion_gridSq hL) hs

namespace PeriodicConfig

variable (P : PeriodicConfig) (hne : P.points.Nonempty)

/-! ### The orbit family of triangles -/

/-- The representative triangle of the `k`-th face orbit. -/
noncomputable def faceTri (k : Fin (P.nF hne)) : Set Plane :=
  (P.deloneLift hne).delTri (P.face hne k).1 (P.face hne k).2

/-- The full family of triangles of the global fan tiling, indexed by a face
orbit together with an integer lattice shift. -/
noncomputable def famTri (p : Fin (P.nF hne) × ℤ × ℤ) : Set Plane :=
  (P.deloneLift hne).delTri ((P.face hne p.1).1 + latticeVec P.side p.2.1 p.2.2)
    (P.face hne p.1).2

lemma famTri_eq_image (p : Fin (P.nF hne) × ℤ × ℤ) :
    P.famTri hne p
      = (fun q : Plane => q + latticeVec P.side p.2.1 p.2.2) '' P.faceTri hne p.1 :=
  (P.deloneLift hne).delTri_translate (P.latticeInv hne p.2.1 p.2.2) _ _

lemma isFanIndex_famTri (p : Fin (P.nF hne) × ℤ × ℤ) :
    (P.deloneLift hne).IsFanIndex ((P.face hne p.1).1 + latticeVec P.side p.2.1 p.2.2)
      (P.face hne p.1).2 :=
  ((P.deloneLift hne).isFanIndex_translate (P.latticeInv hne p.2.1 p.2.2) _ _).mpr
    (P.isFanIndex_face hne p.1)

lemma famIdx_injective : Function.Injective
    (fun p : Fin (P.nF hne) × ℤ × ℤ =>
      ((P.face hne p.1).1 + latticeVec P.side p.2.1 p.2.2, (P.face hne p.1).2)) := by
  rintro ⟨k, m, n⟩ ⟨k', m', n'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hrel : (P.face hne k).1
      = (P.face hne k').1 + latticeVec P.side (m' - m) (n' - n) := by
    have h4 : (P.face hne k).1
        = (P.face hne k').1 + latticeVec P.side m' n' - latticeVec P.side m n := by
      rw [← h1]; abel
    rw [h4, ← latticeVec_sub P.side m n m' n']
    abel
  obtain ⟨e1, e2⟩ := latticeVec_eq_zero_of_inFund P.side_pos (P.inFund_face hne k)
    (P.inFund_face hne k') hrel
  have hm : m = m' := by omega
  have hn : n = n' := by omega
  subst hm; subst hn
  have hc : (P.face hne k).1 = (P.face hne k').1 := by
    have := h1
    exact add_right_cancel this
  have : P.face hne k = P.face hne k' := Prod.ext hc h2
  rw [P.face_injective hne this]

lemma measurableSet_famTri (p : Fin (P.nF hne) × ℤ × ℤ) : MeasurableSet (P.famTri hne p) := by
  have hfin : ({(P.deloneLift hne).dvert ((P.face hne p.1).1 + latticeVec P.side p.2.1 p.2.2)
      (P.face hne p.1).2 0,
    (P.deloneLift hne).dvert ((P.face hne p.1).1 + latticeVec P.side p.2.1 p.2.2)
      (P.face hne p.1).2 1,
    (P.deloneLift hne).dvert ((P.face hne p.1).1 + latticeVec P.side p.2.1 p.2.2)
      (P.face hne p.1).2 2} : Set Plane).Finite :=
    ((Set.finite_singleton _).insert _).insert _
  exact (hfin.isCompact_convexHull).measurableSet

lemma convex_famTri (p : Fin (P.nF hne) × ℤ × ℤ) : Convex ℝ (P.famTri hne p) :=
  convex_convexHull ℝ _

lemma pairwise_aedisjoint_famTri :
    Pairwise (Function.onFun (AEDisjoint volume) (P.famTri hne)) := by
  intro p q hpq
  refine aedisjoint_of_disjoint_interior (P.convex_famTri hne p) (P.convex_famTri hne q) ?_
  exact (P.deloneLift hne).disjoint_interior_delTri (P.isFanIndex_famTri hne p)
    (P.isFanIndex_famTri hne q) (fun h => hpq (P.famIdx_injective hne h))

lemma iUnion_famTri : (⋃ p : Fin (P.nF hne) × ℤ × ℤ, P.famTri hne p) = Set.univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  obtain ⟨v, i, hidx, hz⟩ := (P.deloneLift hne).exists_delTri z
  have hmem : (fold P.side v, i) ∈ P.fanRep hne :=
    (P.mem_fanRep hne).mpr ⟨P.isFanIndex_fold hne hidx, inFund_fold P.side_pos v⟩
  obtain ⟨k, hk⟩ := P.exists_face hne hmem
  refine ⟨(k, ⌊v 0 / P.side⌋, ⌊v 1 / P.side⌋), ?_⟩
  show z ∈ (P.deloneLift hne).delTri
    ((P.face hne k).1 + latticeVec P.side ⌊v 0 / P.side⌋ ⌊v 1 / P.side⌋) (P.face hne k).2
  rw [hk]
  simpa [fold_add_shift P.side v] using hz

/-! ### The two summations -/

lemma tsum_volume_famTri_inter (k : Fin (P.nF hne)) :
    ∑' mn : ℤ × ℤ, volume (P.famTri hne (k, mn) ∩ fundSq P.side)
      = volume (P.faceTri hne k) := by
  have hmeasT : MeasurableSet (P.faceTri hne k) := by
    have := P.measurableSet_famTri hne (k, 0, 0)
    have heq : P.famTri hne (k, 0, 0) = P.faceTri hne k := by
      simp [famTri, faceTri]
    rwa [heq] at this
  have hstep : ∀ mn : ℤ × ℤ, volume (P.famTri hne (k, mn) ∩ fundSq P.side)
      = volume (gridSq P.side (-mn.1) (-mn.2) ∩ P.faceTri hne k) := by
    intro mn
    rw [P.famTri_eq_image hne (k, mn)]
    have h1 : volume ((fun q : Plane => q + latticeVec P.side mn.1 mn.2) '' P.faceTri hne k
          ∩ fundSq P.side)
        = volume ((fun q : Plane => q + -latticeVec P.side mn.1 mn.2) ''
            (((fun q : Plane => q + latticeVec P.side mn.1 mn.2) '' P.faceTri hne k)
              ∩ fundSq P.side)) := (volume_image_add _ _).symm
    rw [h1, image_add_inter, image_add_image_add]
    have h2 : (fun q : Plane => q + -latticeVec P.side mn.1 mn.2) '' fundSq P.side
        = gridSq P.side (-mn.1) (-mn.2) := by
      rw [gridSq, ← latticeVec_neg]
    rw [h2, Set.inter_comm]
  simp only [hstep]
  have hre : ∑' mn : ℤ × ℤ, volume (gridSq P.side (-mn.1) (-mn.2) ∩ P.faceTri hne k)
      = ∑' mn : ℤ × ℤ, volume (gridSq P.side mn.1 mn.2 ∩ P.faceTri hne k) := by
    refine Equiv.tsum_eq (Equiv.neg (ℤ × ℤ)) (fun mn : ℤ × ℤ =>
      volume (gridSq P.side mn.1 mn.2 ∩ P.faceTri hne k))
  rw [hre]
  exact tsum_volume_inter_gridSq P.side_pos hmeasT

lemma tsum_volume_faceTri :
    ∑' k : Fin (P.nF hne), volume (P.faceTri hne k) = ENNReal.ofReal (P.side ^ 2) := by
  have hcover := tsum_volume_inter_of_cover (P.famTri hne)
    (fun p => (P.measurableSet_famTri hne p).nullMeasurableSet)
    (P.pairwise_aedisjoint_famTri hne) (P.iUnion_famTri hne) (measurableSet_fundSq P.side)
  have hprod : ∑' p : Fin (P.nF hne) × ℤ × ℤ, volume (P.famTri hne p ∩ fundSq P.side)
      = ∑' (k : Fin (P.nF hne)) (mn : ℤ × ℤ),
          volume (P.famTri hne (k, mn) ∩ fundSq P.side) := ENNReal.tsum_prod'
  rw [← volume_fundSq P.side_pos, ← hcover, hprod]
  exact tsum_congr fun k => (P.tsum_volume_famTri_inter hne k).symm

/-! ### The area identity -/

lemma volume_faceTri (k : Fin (P.nF hne)) :
    volume (P.faceTri hne k)
      = ENNReal.ofReal (cross (P.vertQ hne k 0) (P.vertQ hne k 1) (P.vertQ hne k 2) / 2) := by
  have hpos := P.cross_vertQ_pos hne k
  have h := volume_triangle (P.vertQ hne k 0) (P.vertQ hne k 1) (P.vertQ hne k 2)
  rw [abs_of_pos hpos] at h
  exact h

/-- **The quotient area identity.**  The total area of the `nF` representative
faces is the area of a fundamental domain. -/
theorem area_identity :
    ∑ k : Fin (P.nF hne), cross (P.vertQ hne k 0) (P.vertQ hne k 1) (P.vertQ hne k 2) / 2
      = P.side ^ 2 := by
  have hnn : ∀ k : Fin (P.nF hne),
      0 ≤ cross (P.vertQ hne k 0) (P.vertQ hne k 1) (P.vertQ hne k 2) / 2 :=
    fun k => le_of_lt (by linarith [P.cross_vertQ_pos hne k])
  have h1 : ∑' k : Fin (P.nF hne), volume (P.faceTri hne k)
      = ENNReal.ofReal
        (∑ k : Fin (P.nF hne),
          cross (P.vertQ hne k 0) (P.vertQ hne k 1) (P.vertQ hne k 2) / 2) := by
    rw [tsum_fintype]
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hnn k)]
    exact Finset.sum_congr rfl fun k _ => P.volume_faceTri hne k
  rw [P.tsum_volume_faceTri hne] at h1
  have h2 : (0 : ℝ) ≤ P.side ^ 2 := sq_nonneg _
  have h3 : (0 : ℝ) ≤ ∑ k : Fin (P.nF hne),
      cross (P.vertQ hne k 0) (P.vertQ hne k 1) (P.vertQ hne k 2) / 2 :=
    Finset.sum_nonneg fun k _ => hnn k
  exact ((ENNReal.ofReal_eq_ofReal_iff h2 h3).mp h1).symm

end PeriodicConfig

end Conjecture41
