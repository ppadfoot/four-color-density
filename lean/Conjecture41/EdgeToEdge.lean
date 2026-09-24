import Conjecture41.EdgeNeighbour
import Conjecture41.LocalFiniteness

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The global fan triangulation is edge-to-edge

A *dart* of the global canonical fan family is a triangle of the family
together with one of its three directed edges, taken in the positive cyclic
order.  This file proves

```
DeloneSet.exists_unique_reverse_dart :
  every dart `(v, i, x, y)` has exactly one reverse dart `(v', i', y, x)` .
```

Existence splits into two cases.  The *diagonals* of a fan (the edges
`vert 0 → vert i` with `2 ≤ i`) are shared by two consecutive triangles of the
same fan.  The *boundary edges* of a cell are shared with the neighbouring cell
produced by `DeloneSet.exists_adjacent_center`, and
`DeloneSet.consecutive_of_edge` identifies them as consecutive vertices of the
canonical fan of that neighbour.

Uniqueness is a local convexity argument: two positively oriented triangles
with the same directed edge both contain all points sufficiently close to the
midpoint of that edge and strictly on its left, so their interiors meet.
-/

namespace Conjecture41

open Metric Set

/-- The midpoint of two points of the plane. -/
noncomputable def mid (x y : Plane) : Plane := (2 : ℝ)⁻¹ • (x + y)

lemma cross_mid (a b x y : Plane) : cross a b (mid x y) = (cross a b x + cross a b y) / 2 := by
  simp only [cross, mid, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  ring

lemma cross_self_left (a b : Plane) : cross a b a = 0 := by simp only [cross]; ring

lemma cross_self_right (a b : Plane) : cross a b b = 0 := by simp only [cross]; ring

/-- Every point close enough to the midpoint of a directed edge and strictly on
its left lies in the interior of the triangle. -/
lemma interior_nbhd_of_edge {x y z : Plane} (h : 0 < cross x y z) :
    ∃ δ > 0, ∀ p : Plane, dist p (mid x y) < δ → 0 < cross x y p →
      p ∈ interior (convexHull ℝ ({x, y, z} : Set Plane)) := by
  have hyzx : cross y z x = cross x y z := (cross_cyclic x y z).symm
  have hzxy : cross z x y = cross x y z := by rw [cross_cyclic x y z, cross_cyclic y z x]
  have h1 : 0 < cross y z (mid x y) := by
    rw [cross_mid, cross_self_left y z, hyzx]; linarith
  have h2 : 0 < cross z x (mid x y) := by
    rw [cross_mid, cross_self_right z x, hzxy]; linarith
  have hopen : IsOpen {p : Plane | 0 < cross y z p ∧ 0 < cross z x p} :=
    IsOpen.inter (isOpen_lt continuous_const (continuous_cross y z))
      (isOpen_lt continuous_const (continuous_cross z x))
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen (mid x y) ⟨h1, h2⟩
  refine ⟨δ, hδ, fun p hp hpc => ?_⟩
  rw [interior_triangle_eq h]
  have := hball (by simpa [Metric.mem_ball] using hp)
  exact ⟨hpc, this.1, this.2⟩

/-- A point strictly on the left of a directed edge, arbitrarily close to its
midpoint. -/
lemma exists_left_near_mid {x y z : Plane} (h : 0 < cross x y z) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : Plane, dist p (mid x y) < δ ∧ 0 < cross x y p := by
  set w : Plane := z - mid x y with hw
  by_cases hw0 : ‖w‖ = 0
  · exfalso
    have hz : z = mid x y := by
      have : w = 0 := norm_eq_zero.mp hw0
      rw [hw] at this
      exact sub_eq_zero.mp this
    rw [hz, cross_mid, cross_self_left x y, cross_self_right x y] at h
    norm_num at h
  · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw0)
    set t : ℝ := min (1 / 2) (δ / (2 * ‖w‖)) with ht
    have htpos : 0 < t := lt_min (by norm_num) (by positivity)
    refine ⟨mid x y + t • w, ?_, ?_⟩
    · rw [dist_eq_norm]
      have : mid x y + t • w - mid x y = t • w := by abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      have h1 : t ≤ δ / (2 * ‖w‖) := min_le_right _ _
      calc t * ‖w‖ ≤ (δ / (2 * ‖w‖)) * ‖w‖ := by nlinarith
        _ = δ / 2 := by field_simp
        _ < δ := by linarith
    · have hkey : cross x y (mid x y + t • w) = t * cross x y z := by
        simp only [cross, hw, mid, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        ring
      rw [hkey]
      exact mul_pos htpos h

/-- Two positively oriented triangles sharing a directed edge have intersecting
interiors. -/
theorem not_disjoint_of_common_edge {x y z₁ z₂ : Plane} (h1 : 0 < cross x y z₁)
    (h2 : 0 < cross x y z₂) :
    ¬ Disjoint (interior (convexHull ℝ ({x, y, z₁} : Set Plane)))
      (interior (convexHull ℝ ({x, y, z₂} : Set Plane))) := by
  obtain ⟨δ₁, hδ₁, hn₁⟩ := interior_nbhd_of_edge h1
  obtain ⟨δ₂, hδ₂, hn₂⟩ := interior_nbhd_of_edge h2
  obtain ⟨p, hp, hpc⟩ := exists_left_near_mid h1 (lt_min hδ₁ hδ₂)
  intro hdisj
  exact Set.disjoint_left.mp hdisj (hn₁ p (lt_of_lt_of_le hp (min_le_left _ _)) hpc)
    (hn₂ p (lt_of_lt_of_le hp (min_le_right _ _)) hpc)

namespace DeloneSet

variable (D : DeloneSet)

/-- `IsDart v i x y` says that `x → y` is one of the three directed edges of the
canonical fan triangle `(v, i)`, in positive cyclic order. -/
def IsDart (v : Plane) (i : ℕ) (x y : Plane) : Prop :=
  D.IsFanIndex v i ∧
    ((x = D.delVert v 0 ∧ y = D.delVert v i) ∨
      (x = D.delVert v i ∧ y = D.delVert v (i + 1)) ∨
      (x = D.delVert v (i + 1) ∧ y = D.delVert v 0))

/-- The third vertex of the triangle carrying a dart. -/
lemma isDart_cross_pos {v : Plane} {i : ℕ} {x y : Plane} (h : D.IsDart v i x y) :
    ∃ z : Plane, 0 < cross x y z ∧
      (D.delTri v i = convexHull ℝ ({x, y, z} : Set Plane)) := by
  obtain ⟨hidx, hcase⟩ := h
  have hpos := D.cross_delTri_pos hidx.1 hidx.2.1 hidx.2.2
  set A := D.delVert v 0
  set B := D.delVert v i
  set C := D.delVert v (i + 1)
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨C, hpos, rfl⟩
  · refine ⟨A, by rw [← cross_cyclic A B C]; exact hpos, ?_⟩
    unfold delTri
    congr 1
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · refine ⟨B, ?_, ?_⟩
    · rw [← cross_cyclic B C A, ← cross_cyclic A B C]
      exact hpos
    · unfold delTri
      congr 1
      ext w
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto

/-- **Uniqueness of the reverse dart.** -/
theorem dart_unique {v v' : Plane} {i i' : ℕ} {x y : Plane} (h : D.IsDart v i x y)
    (h' : D.IsDart v' i' x y) : (v, i) = (v', i') := by
  by_contra hne
  obtain ⟨z₁, hz₁, hT₁⟩ := D.isDart_cross_pos h
  obtain ⟨z₂, hz₂, hT₂⟩ := D.isDart_cross_pos h'
  have hdisj := D.disjoint_interior_delTri h.1 h'.1 hne
  rw [hT₁, hT₂] at hdisj
  exact not_disjoint_of_common_edge hz₁ hz₂ hdisj

/-! ### Existence of the reverse dart -/

lemma isDart_consecutive {v : Plane} (h3 : 3 ≤ D.nsCard v) {p : ℕ} (hp : p + 1 ≤ D.delLast v) :
    ∃ i : ℕ, D.IsDart v i (D.delVert v p) (D.delVert v (p + 1)) := by
  have hlast := D.two_le_delLast h3
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · exact ⟨1, ⟨h3, le_rfl, by omega⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨p, ⟨h3, hp0, by omega⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

lemma isDart_closing {v : Plane} (h3 : 3 ≤ D.nsCard v) :
    ∃ i : ℕ, D.IsDart v i (D.delVert v (D.delLast v)) (D.delVert v 0) := by
  have hlast := D.two_le_delLast h3
  refine ⟨D.delLast v - 1, ⟨h3, by omega, by omega⟩, Or.inr (Or.inr ⟨?_, rfl⟩)⟩
  rw [show D.delLast v - 1 + 1 = D.delLast v by omega]

/-- The boundary-edge condition for a consecutive pair, in the form required by
`exists_adjacent_center`. -/
lemma edge_cond_consecutive {v : Plane} (h3 : 3 ≤ D.nsCard v) {k : ℕ} (hk : k < D.delLast v) :
    ∀ y ∈ D.nearestSet v, y ≠ D.delVert v k → y ≠ D.delVert v (k + 1) →
      0 < cross (D.delVert v k) (D.delVert v (k + 1)) y := by
  have hpos := D.nd_pos_of_three_nearest h3
  intro y hy hyk hyk1
  obtain ⟨m, hm, rfl⟩ := D.exists_delVert_eq hpos hy
  exact D.cross_delVert_edge_pos h3 hk hm (fun hc => hyk (by rw [hc])) (fun hc => hyk1 (by rw [hc]))

lemma edge_cond_closing {v : Plane} (h3 : 3 ≤ D.nsCard v) :
    ∀ y ∈ D.nearestSet v, y ≠ D.delVert v (D.delLast v) → y ≠ D.delVert v 0 →
      0 < cross (D.delVert v (D.delLast v)) (D.delVert v 0) y := by
  have hpos := D.nd_pos_of_three_nearest h3
  intro y hy hyl hy0
  obtain ⟨m, hm, rfl⟩ := D.exists_delVert_eq hpos hy
  exact D.cross_delVert_close_pos h3 hm (fun hc => hy0 (by rw [hc])) (fun hc => hyl (by rw [hc]))

/-- Three distinct nearest sites make a centre full-dimensional. -/
lemma three_le_nsCard {v a b c : Plane} (ha : a ∈ D.nearestSet v) (hb : b ∈ D.nearestSet v)
    (hc : c ∈ D.nearestSet v) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ D.nsCard v := by
  classical
  have hsub : ({a, b, c} : Finset Plane) ⊆ D.nearFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (D.mem_nearFinset).mpr ha
    · exact (D.mem_nearFinset).mpr hb
    · exact (D.mem_nearFinset).mpr hc
  have hcard : ({a, b, c} : Finset Plane).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  have := Finset.card_le_card hsub
  rw [hcard] at this
  simpa [card_nearFinset] using this

/-- **The reverse of a boundary-edge dart exists.** -/
theorem exists_reverse_dart_boundary {v a b : Plane} (ha : a ∈ D.nearestSet v)
    (hb : b ∈ D.nearestSet v) (hab : a ≠ b)
    (hedge : ∀ y ∈ D.nearestSet v, y ≠ a → y ≠ b → 0 < cross a b y) :
    ∃ (v' : Plane) (i' : ℕ), D.IsDart v' i' b a := by
  obtain ⟨v', -, ha', hb', hright, y, hy, hya, hyb⟩ :=
    D.exists_adjacent_center ha hb hab hedge
  have h3' : 3 ≤ D.nsCard v' := D.three_le_nsCard ha' hb' hy hab (Ne.symm hya) (Ne.symm hyb)
  have hedge' : ∀ z ∈ D.nearestSet v', z ≠ b → z ≠ a → 0 < cross b a z := by
    intro z hz hzb hza
    have := hright z hz hza hzb
    rw [cross_swap_left b a z]
    linarith
  obtain ⟨p, q, hp, hq, hpb, hqa, hcase⟩ :=
    D.consecutive_of_edge h3' hb' ha' (Ne.symm hab) hedge'
  rcases hcase with rfl | ⟨hpl, hq0⟩
  · obtain ⟨i, hi⟩ := D.isDart_consecutive h3' (p := p) hq
    exact ⟨v', i, by rw [hpb, hqa] at hi; exact hi⟩
  · obtain ⟨i, hi⟩ := D.isDart_closing h3'
    refine ⟨v', i, ?_⟩
    rw [← hpl, hpb, ← hq0, hqa] at hi
    exact hi

/-- **Every dart has a reverse dart, and it is unique.**  This is the
edge-to-edge (face-to-face) property of the global canonical fan
triangulation. -/
theorem exists_unique_reverse_dart {v : Plane} {i : ℕ} {x y : Plane} (h : D.IsDart v i x y) :
    ∃! p : Plane × ℕ, D.IsDart p.1 p.2 y x := by
  obtain ⟨hidx, hcase⟩ := h
  have h3 := hidx.1
  have h1i : 1 ≤ i := hidx.2.1
  have hilast : i < D.delLast v := hidx.2.2
  have hpos := D.nd_pos_of_three_nearest h3
  have hlast := D.two_le_delLast h3
  have hexists : ∃ (v' : Plane) (i' : ℕ), D.IsDart v' i' y x := by
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- edge `vert 0 → vert i`
      rcases Nat.lt_or_ge i 2 with hi2 | hi2
      · -- `i = 1`: a boundary edge
        have hi1 : i = 1 := by omega
        subst hi1
        refine D.exists_reverse_dart_boundary (a := D.delVert v 0) (b := D.delVert v 1)
          (D.delVert_mem_nearestSet hpos (Nat.zero_le _))
          (D.delVert_mem_nearestSet hpos (by omega))
          (fun hc => absurd (D.delVert_injOn hpos (Nat.zero_le _) (by omega) hc) (by omega))
          ?_
        exact D.edge_cond_consecutive h3 (k := 0) (by omega)
      · -- a diagonal: the previous triangle of the same fan
        refine ⟨v, i - 1, ⟨h3, by omega, by omega⟩, Or.inr (Or.inr ⟨?_, rfl⟩)⟩
        rw [show i - 1 + 1 = i by omega]
    · -- edge `vert i → vert (i+1)`: a boundary edge
      refine D.exists_reverse_dart_boundary (a := D.delVert v i) (b := D.delVert v (i + 1))
        (D.delVert_mem_nearestSet hpos (le_of_lt hidx.2.2))
        (D.delVert_mem_nearestSet hpos hidx.2.2)
        (fun hc => absurd (D.delVert_injOn hpos (le_of_lt hidx.2.2) hidx.2.2 hc) (by omega))
        (D.edge_cond_consecutive h3 hidx.2.2)
    · -- edge `vert (i+1) → vert 0`
      rcases Nat.lt_or_ge (i + 1) (D.delLast v) with hi | hi
      · -- a diagonal: the next triangle of the same fan
        exact ⟨v, i + 1, ⟨h3, by omega, by omega⟩, Or.inl ⟨rfl, rfl⟩⟩
      · -- the closing boundary edge
        have hil : i + 1 = D.delLast v := by omega
        rw [hil]
        refine D.exists_reverse_dart_boundary (a := D.delVert v (D.delLast v))
          (b := D.delVert v 0) (D.delVert_mem_nearestSet hpos le_rfl)
          (D.delVert_mem_nearestSet hpos (Nat.zero_le _))
          (fun hc => absurd (D.delVert_injOn hpos le_rfl (Nat.zero_le _) hc) (by omega))
          (D.edge_cond_closing h3)
  obtain ⟨v', i', hd⟩ := hexists
  refine ⟨(v', i'), hd, fun q hq => ?_⟩
  exact (D.dart_unique hq hd)

end DeloneSet

end Conjecture41
