import Conjecture41.ColoredTriangle
import Conjecture41.GlobalSum

set_option autoImplicit false

/-!
# The periodic density bound from a weak Delaunay torus triangulation

This file assembles gates G2, G3, and G4 with the abstract global summation of
`GlobalSum.lean` into the implication

```
(equivariant weak Delaunay triangulation of the periodic configuration)  →  V ≤ A .
```

A `TorusTriangulation C A` is the finite **numerical certificate** extracted
from a `Λ`-equivariant triangulation of the quotient torus of area `A`.  It is
given by `nF` representative faces, an involutive pairing of the `3 nF` darts
(corners), and, for each dart, the translation that carries the paired face
onto the shared edge.  Its fields say:

* each face is a positively oriented triangle whose vertices lie in the
  configuration;
* the dart pairing is a fixed-point-free involution matching the two copies of
  every edge;
* the weak Delaunay condition, in the form of the in-circle determinant, holds
  for each dart;
* the exclusion weight is invariant under the pairing (a consequence of the
  periodicity of the coloring);
* the quotient Euler identity `F = 2 V`;
* the area partition `Σ_faces area = A`.

The structure deliberately contains only what the cotangent summation below
uses.  In particular it does not itself encode coverage of the plane,
disjoint interiors, face-to-face incidence, local finiteness, exact vertex
orbits, or that `tr` is a period-lattice vector; `nV`, `euler`, and `area` are
otherwise free fields.  Consequently `PeriodicCertificate.lean` derives this
record from the semantically genuine periodic Delaunay tiling constructed in
the preceding modules, as specified in `AuthoritativeProof.lean`.  This weak
record is not treated as the definition of that geometric tiling.

None of these is a hypothesis of the final theorem `conjecture_4_1`: they
describe the object constructed for a periodic configuration in gates G5a--G5f
and then consumed by the global summation theorem.
-/

namespace Conjecture41

open Finset

/-- Translation invariance of the doubled signed area. -/
lemma cross_add_right (a b c v : Plane) : cross (a + v) (b + v) (c + v) = cross a b c := by
  simp only [cross]
  simp only [PiLp.add_apply]
  ring

/-- Translation invariance of the cotangent at a vertex. -/
lemma cotOpp_add_right (a b c v : Plane) : cotOpp (a + v) (b + v) (c + v) = cotOpp a b c := by
  simp only [cotOpp, cross_add_right, dist_add_right]

/-- The finite cotangent certificate derived from a genuine
`Λ`-equivariant weak Delaunay triangulation of a quotient torus of area `A`.
This record alone is not the semantic definition of such a triangulation; see
the module documentation and `AuthoritativeProof.lean`. -/
structure TorusTriangulation (C : FourColorConfig) (A : ℝ) where
  /-- Number of faces per fundamental domain. -/
  nF : ℕ
  /-- Number of vertices per fundamental domain. -/
  nV : ℕ
  /-- The three vertices of each face, in positive orientation. -/
  vert : Fin nF → Fin 3 → Plane
  vert_mem : ∀ f i, vert f i ∈ C.carrier
  pos : ∀ f, 0 < cross (vert f 0) (vert f 1) (vert f 2)
  /-- The pairing of darts across edges. -/
  pf : Fin nF × Fin 3 → Fin nF × Fin 3
  pf_invol : ∀ d, pf (pf d) = d
  pf_ne : ∀ d, pf d ≠ d
  /-- The translation carrying the paired face onto the shared edge. -/
  tr : Fin nF × Fin 3 → Plane
  match_left : ∀ d : Fin nF × Fin 3,
    vert (pf d).1 ((pf d).2 + 2) + tr d = vert d.1 (d.2 + 1)
  match_right : ∀ d : Fin nF × Fin 3,
    vert (pf d).1 ((pf d).2 + 1) + tr d = vert d.1 (d.2 + 2)
  /-- The weak Delaunay (empty circumcircle) condition. -/
  delaunay : ∀ d : Fin nF × Fin 3,
    0 ≤ inCircleDet (vert d.1 d.2) (vert d.1 (d.2 + 1)) (vert d.1 (d.2 + 2))
      (vert (pf d).1 (pf d).2 + tr d)
  /-- The exclusion weight of an edge does not depend on which side it is seen from. -/
  weight_eq : ∀ d : Fin nF × Fin 3,
    exclusionSq (C.color (vert (pf d).1 ((pf d).2 + 1))) (C.color (vert (pf d).1 ((pf d).2 + 2)))
      = exclusionSq (C.color (vert d.1 (d.2 + 1))) (C.color (vert d.1 (d.2 + 2)))
  /-- The Euler identity of the quotient torus. -/
  euler : nF = 2 * nV
  /-- The area partition of the quotient torus. -/
  area : ∑ f : Fin nF, cross (vert f 0) (vert f 1) (vert f 2) / 2 = A

namespace TorusTriangulation

variable {C : FourColorConfig} {A : ℝ} (S : TorusTriangulation C A)

/-- The cotangent at the apex of a dart. -/
noncomputable def cotDart (d : Fin S.nF × Fin 3) : ℝ :=
  cotOpp (S.vert d.1 d.2) (S.vert d.1 (d.2 + 1)) (S.vert d.1 (d.2 + 2))

/-- The squared length of the edge opposite a dart. -/
noncomputable def edgeSq (d : Fin S.nF × Fin 3) : ℝ :=
  dist (S.vert d.1 (d.2 + 1)) (S.vert d.1 (d.2 + 2)) ^ 2

/-- The exclusion weight of the edge opposite a dart. -/
noncomputable def wDart (d : Fin S.nF × Fin 3) : ℝ :=
  exclusionSq (C.color (S.vert d.1 (d.2 + 1))) (C.color (S.vert d.1 (d.2 + 2)))

/-- Every corner of every face is positively oriented. -/
lemma pos_cyclic (f : Fin S.nF) (i : Fin 3) :
    0 < cross (S.vert f i) (S.vert f (i + 1)) (S.vert f (i + 2)) := by
  have h := S.pos f
  fin_cases i
  · simpa using h
  · have : cross (S.vert f 1) (S.vert f 2) (S.vert f 0) = cross (S.vert f 0) (S.vert f 1) (S.vert f 2) :=
      (cross_cyclic _ _ _).symm
    simpa [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, this] using h
  · have : cross (S.vert f 2) (S.vert f 0) (S.vert f 1) = cross (S.vert f 0) (S.vert f 1) (S.vert f 2) := by
      rw [cross_cyclic, cross_cyclic]
    simpa [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, this] using h
  
/-- The endpoints of an edge are distinct. -/
lemma vert_ne (f : Fin S.nF) (i : Fin 3) : S.vert f (i + 1) ≠ S.vert f (i + 2) := by
  intro hEq
  have h := S.pos_cyclic f i
  rw [hEq, cross_eq_zero_of_eq_last] at h
  exact lt_irrefl 0 h

/-- Validity of the configuration bounds the exclusion weight of every edge. -/
lemma wDart_le_edgeSq (d : Fin S.nF × Fin 3) : S.wDart d ≤ S.edgeSq d :=
  C.valid (S.vert_mem d.1 (d.2 + 1)) (S.vert_mem d.1 (d.2 + 2)) (S.vert_ne d.1 d.2)

/-- The squared edge length is the same seen from either side. -/
lemma edgeSq_pf (d : Fin S.nF × Fin 3) : S.edgeSq (S.pf d) = S.edgeSq d := by
  have h1 := S.match_left d
  have h2 := S.match_right d
  unfold edgeSq
  rw [← h1, ← h2, dist_add_right, dist_comm]

/-- The exclusion weight is the same seen from either side. -/
lemma wDart_pf (d : Fin S.nF × Fin 3) : S.wDart (S.pf d) = S.wDart d := S.weight_eq d

/-- The paired cotangent weight of an edge is nonnegative: this is the weak
Delaunay condition, via `cotOpp_add_cotOpp_nonneg`. -/
lemma cotDart_add_cotDart_pf_nonneg (d : Fin S.nF × Fin 3) :
    0 ≤ S.cotDart d + S.cotDart (S.pf d) := by
  set a := S.vert d.1 d.2 with ha
  set b := S.vert d.1 (d.2 + 1) with hb
  set c := S.vert d.1 (d.2 + 2) with hc
  set e := S.vert (S.pf d).1 (S.pf d).2 + S.tr d with he
  have hbl : S.vert (S.pf d).1 ((S.pf d).2 + 2) + S.tr d = b := S.match_left d
  have hbr : S.vert (S.pf d).1 ((S.pf d).2 + 1) + S.tr d = c := S.match_right d
  have h1 : 0 < cross a b c := S.pos_cyclic d.1 d.2
  have h2 : 0 < cross e c b := by
    rw [he, ← hbr, ← hbl, cross_add_right]
    exact S.pos_cyclic (S.pf d).1 (S.pf d).2
  have hdel : 0 ≤ inCircleDet a b c e := S.delaunay d
  have hcot : cotOpp e c b = S.cotDart (S.pf d) := by
    rw [he, ← hbr, ← hbl, cotOpp_add_right]
    rfl
  have := cotOpp_add_cotOpp_nonneg h1 h2 hdel
  rw [hcot] at this
  exact this

/-- The per-face cotangent area identity. -/
lemma face_area_identity (f : Fin S.nF) :
    ∑ i : Fin 3, S.edgeSq (f, i) * S.cotDart (f, i)
      = 4 * (cross (S.vert f 0) (S.vert f 1) (S.vert f 2) / 2) := by
  have hid := four_area_eq_cot_weighted_sum (a := S.vert f 0) (b := S.vert f 1) (c := S.vert f 2)
    (ne_of_gt (S.pos f))
  rw [Fin.sum_univ_three]
  simp only [edgeSq, cotDart, show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  rw [dist_comm (S.vert f 2) (S.vert f 0)]
  linarith [hid]

/-- The per-face marked budget. -/
lemma face_budget (f : Fin S.nF) : 2 ≤ ∑ i : Fin 3, S.wDart (f, i) * S.cotDart (f, i) := by
  have hbud := cot_marked_budget C.color (a := S.vert f 0) (b := S.vert f 1) (c := S.vert f 2)
    (S.pos f)
  rw [Fin.sum_univ_three]
  simp only [wDart, cotDart, show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  rw [exclusionSq_comm (C.color (S.vert f 2)) (C.color (S.vert f 0))]
  linarith [hbud]

/-! ### Nondegeneracy: a positive-area torus needs faces and points -/

/-- A torus triangulation of a quotient of positive area has at least one face. -/
lemma nF_pos (hA : 0 < A) : 0 < S.nF := by
  classical
  rcases Nat.eq_zero_or_pos S.nF with h0 | h
  · exfalso
    have huniv : (Finset.univ : Finset (Fin S.nF)) = ∅ :=
      Finset.card_eq_zero.mp (by simp [h0])
    have harea := S.area
    rw [huniv, Finset.sum_empty] at harea
    exact absurd harea.symm (ne_of_gt hA)
  · exact h

include S in
/-- Consequently the underlying configuration is nonempty.  This is why the
existence of a torus triangulation must be asserted only for *nonempty*
periodic configurations: an empty configuration has no faces at all, so its
face areas cannot add up to the positive area of a fundamental domain. -/
lemma carrier_nonempty (hA : 0 < A) : C.carrier.Nonempty :=
  ⟨S.vert ⟨0, S.nF_pos hA⟩ 0, S.vert_mem _ _⟩

/-! ### The global sum -/

/-- A numerical key used to choose a representative dart on each edge. -/
def dartKey (d : Fin S.nF × Fin 3) : ℕ := 3 * (d.1 : ℕ) + (d.2 : ℕ)

lemma dartKey_injective : Function.Injective S.dartKey := by
  rintro ⟨f, i⟩ ⟨g, j⟩ h
  simp only [dartKey] at h
  have hi := i.isLt
  have hj := j.isLt
  have : (f : ℕ) = g ∧ (i : ℕ) = j := by omega
  obtain ⟨h1, h2⟩ := this
  simp [Prod.ext_iff, Fin.ext_iff, h1, h2]

/-- The chosen representative dart of the edge of `d`. -/
noncomputable def side (d : Fin S.nF × Fin 3) : Fin S.nF × Fin 3 :=
  if S.dartKey d ≤ S.dartKey (S.pf d) then d else S.pf d

lemma side_eq_or (d : Fin S.nF × Fin 3) : S.side d = d ∨ S.side d = S.pf d := by
  unfold side; split_ifs <;> simp

lemma side_pf (d : Fin S.nF × Fin 3) : S.side (S.pf d) = S.side d := by
  have hne : S.dartKey (S.pf d) ≠ S.dartKey d := fun h => S.pf_ne d (S.dartKey_injective h)
  unfold side
  rw [S.pf_invol d]
  by_cases h : S.dartKey d ≤ S.dartKey (S.pf d)
  · have h' : ¬ S.dartKey (S.pf d) ≤ S.dartKey d := by omega
    rw [if_pos h, if_neg h']
  · have h' : S.dartKey (S.pf d) ≤ S.dartKey d := by omega
    rw [if_neg h, if_pos h']

lemma side_idem (d : Fin S.nF × Fin 3) : S.side (S.side d) = S.side d := by
  rcases S.side_eq_or d with h | h
  · rw [h, h]
  · rw [h, S.side_pf d, h]

/-- The edge quantities factor through the chosen representative. -/
lemma edgeSq_side (d : Fin S.nF × Fin 3) : S.edgeSq (S.side d) = S.edgeSq d := by
  rcases S.side_eq_or d with h | h
  · rw [h]
  · rw [h, S.edgeSq_pf]

lemma wDart_side (d : Fin S.nF × Fin 3) : S.wDart (S.side d) = S.wDart d := by
  rcases S.side_eq_or d with h | h
  · rw [h]
  · rw [h, S.wDart_pf]

/-- The fiber of `side` over a representative consists of the two darts of the
edge. -/
lemma fiber_side (e : Fin S.nF × Fin 3) (he : S.side e = e) :
    (univ.filter (fun d => S.side d = e)) = {e, S.pf e} := by
  classical
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro h
    rcases S.side_eq_or d with h' | h'
    · exact Or.inl (by rw [← h', h])
    · refine Or.inr ?_
      have : S.pf d = e := by rw [← h', h]
      rw [← this, S.pf_invol]
  · rintro (rfl | rfl)
    · exact he
    · rw [S.side_pf, he]

/--
The periodic density bound from a weak Delaunay torus triangulation:
the number of vertices per fundamental domain is at most its area.
-/
theorem card_le_area : (S.nV : ℝ) ≤ A := by
  classical
  set D : Finset (Fin S.nF × Fin 3) := univ with hD
  set E : Finset (Fin S.nF × Fin 3) := univ.image S.side with hE
  have hmain := marked_global_sum (ι := Fin S.nF) (κ := Fin S.nF × Fin 3)
    (F := univ) (E := E) (side := S.side) (lsq := S.edgeSq) (w := S.wDart)
    (cot := S.cotDart)
    (K := fun f => cross (S.vert f 0) (S.vert f 1) (S.vert f 2) / 2)
    ?_ ?_ ?_ ?_ ?_
  · -- conclude
    have harea : ∑ f : Fin S.nF, cross (S.vert f 0) (S.vert f 1) (S.vert f 2) / 2 = A := S.area
    rw [harea] at hmain
    have hcard : ((univ : Finset (Fin S.nF)).card : ℝ) = (S.nF : ℝ) := by simp
    rw [hcard, S.euler] at hmain
    push_cast at hmain
    linarith
  · -- `side` maps darts to representatives
    intro d _
    exact Finset.mem_image_of_mem _ (Finset.mem_univ d)
  · -- the paired cotangent weight of each edge is nonnegative
    intro e he
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp he
    have hfix : S.side (S.side d) = S.side d := S.side_idem d
    rw [Finset.univ_product_univ, S.fiber_side (S.side d) hfix]
    rw [Finset.sum_pair (by
      intro h
      exact S.pf_ne (S.side d) h.symm)]
    exact S.cotDart_add_cotDart_pf_nonneg (S.side d)
  · -- validity
    intro e _
    exact S.wDart_le_edgeSq e
  · -- the per-face area identity
    intro f _
    calc ∑ i : Fin 3, S.edgeSq (S.side (f, i)) * S.cotDart (f, i)
        = ∑ i : Fin 3, S.edgeSq (f, i) * S.cotDart (f, i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [S.edgeSq_side]
      _ = _ := S.face_area_identity f
  · -- the per-face marked budget
    intro f _
    calc (2 : ℝ) ≤ ∑ i : Fin 3, S.wDart (f, i) * S.cotDart (f, i) := S.face_budget f
      _ = ∑ i : Fin 3, S.wDart (S.side (f, i)) * S.cotDart (f, i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [S.wDart_side]

end TorusTriangulation

end Conjecture41
