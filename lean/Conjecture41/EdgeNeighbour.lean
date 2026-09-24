import Conjecture41.EdgeGrowth
import Conjecture41.GlobalTriangulation
import Conjecture41.TriangleInterior

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The cell on the other side of a boundary edge

This file turns the analytic growth statement `DeloneSet.exists_grow_edge` into
the combinatorial statement needed for the triangulation:

* `DeloneSet.exists_adjacent_center` — if `[a,b]` is a boundary edge of the
  Delaunay cell of `v` (all the other nearest sites of `v` lie strictly to the
  left of the directed line `a → b`), then there is a *different* centre `v'`
  which also has `a` and `b` as nearest sites and all of whose other nearest
  sites lie strictly to the right;
* `DeloneSet.consecutive_of_edge` — a boundary edge of a full-dimensional cell
  consists of two angularly consecutive vertices of the canonical fan (or of
  the last and the first vertex);
* `DeloneSet.cross_delVert_edge_pos` and `DeloneSet.cross_delVert_close_pos` —
  conversely, consecutive canonical fan vertices, and the closing pair, do form
  boundary edges.

Together these say that the Delaunay tiling is edge-to-edge: every boundary
edge of a full-dimensional cell is a boundary edge of exactly one further
full-dimensional cell, with the opposite orientation.
-/

namespace Conjecture41

open Metric Set

/-- The unit normal of the directed edge `a → b`, pointing to its right. -/
noncomputable def edgeNormal (a b : Plane) : Plane := -(unitPerp (b - a))

lemma pdot_edgeNormal_self (a b : Plane) : pdot (edgeNormal a b) (edgeNormal a b) = 1 := by
  unfold edgeNormal
  have h := pdot_unitPerp_self (b - a)
  simp only [pdot, PiLp.neg_apply] at *
  linarith [h]

lemma pdot_sub_sq_ne_zero {a b : Plane} (hab : a ≠ b) : pdot (b - a) (b - a) ≠ 0 := by
  rw [pdot_self_eq_dist_sq]
  have : dist b a ≠ 0 := dist_ne_zero.mpr (Ne.symm hab)
  positivity

/-- The signed distance to the line `ab`, in the direction of the right normal,
is the doubled signed area divided by the length of the edge. -/
lemma pdot_edgeNormal_apply {a b : Plane} (hab : a ≠ b) (y : Plane) :
    pdot (edgeNormal a b) (a - y)
      = (Real.sqrt (pdot (b - a) (b - a)))⁻¹ * cross a b y := by
  have hw : pdot (b - a) (b - a) ≠ 0 := pdot_sub_sq_ne_zero hab
  unfold edgeNormal unitPerp
  rw [if_neg hw]
  simp only [pdot, PiLp.neg_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, cross,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma inv_sqrt_pdot_pos {a b : Plane} (hab : a ≠ b) :
    0 < (Real.sqrt (pdot (b - a) (b - a)))⁻¹ := by
  have hw : 0 < pdot (b - a) (b - a) := by
    rw [pdot_self_eq_dist_sq]
    have : dist b a ≠ 0 := dist_ne_zero.mpr (Ne.symm hab)
    positivity
  positivity

namespace DeloneSet

variable (D : DeloneSet)

/-- **The cell across a boundary edge.** -/
theorem exists_adjacent_center {v a b : Plane} (ha : a ∈ D.nearestSet v)
    (hb : b ∈ D.nearestSet v) (hab : a ≠ b)
    (hedge : ∀ y ∈ D.nearestSet v, y ≠ a → y ≠ b → 0 < cross a b y) :
    ∃ v' : Plane, v' ≠ v ∧ a ∈ D.nearestSet v' ∧ b ∈ D.nearestSet v' ∧
      (∀ y ∈ D.nearestSet v', y ≠ a → y ≠ b → cross a b y < 0) ∧
      (∃ y ∈ D.nearestSet v', y ≠ a ∧ y ≠ b) := by
  set d : Plane := edgeNormal a b with hdef
  set k : ℝ := (Real.sqrt (pdot (b - a) (b - a)))⁻¹ with hk
  have hkpos : 0 < k := inv_sqrt_pdot_pos hab
  have hval : ∀ y : Plane, pdot d (a - y) = k * cross a b y := fun y =>
    pdot_edgeNormal_apply hab y
  have hd : pdot d d = 1 := pdot_edgeNormal_self a b
  have hperp : pdot d (a - b) = 0 := by
    rw [hval b]
    have : cross a b b = 0 := by simp only [cross]; ring
    rw [this, mul_zero]
  have hleft : ∀ y ∈ D.nearestSet v, y ≠ a → y ≠ b → 0 < pdot d (a - y) := by
    intro y hy hya hyb
    rw [hval y]
    exact mul_pos hkpos (hedge y hy hya hyb)
  obtain ⟨t, htpos, ha', hb', ⟨y, hy, hylt⟩, hall⟩ :=
    D.exists_grow_edge hd ha hb hperp hleft
  have hne : v + t • d ≠ v := by
    intro hcon
    have h1 : dist (v + t • d) (v + (0 : ℝ) • d) = |t - 0| := dist_move v d 0 t hd
    rw [zero_smul, add_zero, sub_zero, hcon, dist_self, abs_of_pos htpos] at h1
    exact absurd h1.symm (ne_of_gt htpos)
  refine ⟨v + t • d, hne, ha', hb', ?_, ?_⟩
  · intro z hz hza hzb
    have := hall z hz hza hzb
    rw [hval z] at this
    nlinarith
  · rw [hval y] at hylt
    refine ⟨y, hy, ?_, ?_⟩
    · intro hya
      rw [hya] at hylt
      have hz : cross a b a = 0 := by simp only [cross]; ring
      rw [hz, mul_zero] at hylt
      exact lt_irrefl 0 hylt
    · intro hyb
      rw [hyb] at hylt
      have hz : cross a b b = 0 := by simp only [cross]; ring
      rw [hz, mul_zero] at hylt
      exact lt_irrefl 0 hylt

/-! ### Orientation of the canonical fan vertices -/

lemma cross_delVert_pos {v : Plane} (h3 : 3 ≤ D.nsCard v) {i j l : ℕ} (hij : i < j) (hjl : j < l)
    (hl : l ≤ D.delLast v) :
    0 < cross (D.delVert v i) (D.delVert v j) (D.delVert v l) := by
  obtain ⟨P, -, -, hlast, hvert, -, -⟩ := D.exists_delPoly h3
  have := P.cross_vert_pos hij hjl (by rw [hlast]; exact hl)
  rwa [hvert i, hvert j, hvert l] at this

lemma cross_delVert_wrap {v : Plane} (h3 : 3 ≤ D.nsCard v) {i j m : ℕ} (hij : i < j)
    (hj : j ≤ D.delLast v) (hmi : m < i) :
    0 < cross (D.delVert v i) (D.delVert v j) (D.delVert v m) := by
  obtain ⟨P, -, -, hlast, hvert, -, -⟩ := D.exists_delPoly h3
  have := P.cross_vert_wrap hij (by rw [hlast]; exact hj) hmi
  rwa [hvert i, hvert j, hvert m] at this

lemma delVert_injOn {v : Plane} (hpos : 0 < D.nd v) {i j : ℕ} (hi : i ≤ D.delLast v)
    (hj : j ≤ D.delLast v) (h : D.delVert v i = D.delVert v j) : i = j := by
  by_contra hne
  have hang : D.delAngle v i ≠ D.delAngle v j := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ne_of_lt (D.delAngle_lt hpos hlt hj)
    · exact ne_of_gt (D.delAngle_lt hpos hlt hi)
  refine hang ?_
  refine circlePoint_inj_of_window hpos ?_ h
  have h1 := D.delAngle_mem_Ioc hpos hi
  have h2 := D.delAngle_mem_Ioc hpos hj
  have := Real.pi_pos
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Consecutive canonical fan vertices form a boundary edge. -/
theorem cross_delVert_edge_pos {v : Plane} (h3 : 3 ≤ D.nsCard v) {k : ℕ} (hk : k < D.delLast v)
    {m : ℕ} (hm : m ≤ D.delLast v) (hmk : m ≠ k) (hmk1 : m ≠ k + 1) :
    0 < cross (D.delVert v k) (D.delVert v (k + 1)) (D.delVert v m) := by
  rcases lt_trichotomy m k with h | h | h
  · exact D.cross_delVert_wrap h3 (Nat.lt_succ_self k) hk h
  · exact absurd h hmk
  · have : k + 1 < m := by omega
    exact D.cross_delVert_pos h3 (Nat.lt_succ_self k) this hm

/-- The closing pair of canonical fan vertices forms a boundary edge. -/
theorem cross_delVert_close_pos {v : Plane} (h3 : 3 ≤ D.nsCard v) {m : ℕ}
    (hm : m ≤ D.delLast v) (hm0 : m ≠ 0) (hmlast : m ≠ D.delLast v) :
    0 < cross (D.delVert v (D.delLast v)) (D.delVert v 0) (D.delVert v m) := by
  have h1 : 0 < cross (D.delVert v 0) (D.delVert v m) (D.delVert v (D.delLast v)) :=
    D.cross_delVert_pos h3 (Nat.pos_of_ne_zero hm0) (lt_of_le_of_ne hm hmlast) le_rfl
  rw [cross_cyclic (D.delVert v (D.delLast v)) (D.delVert v 0) (D.delVert v m)]
  exact h1

/-- **A boundary edge is a pair of consecutive canonical fan vertices.** -/
theorem consecutive_of_edge {v a b : Plane} (h3 : 3 ≤ D.nsCard v) (ha : a ∈ D.nearestSet v)
    (hb : b ∈ D.nearestSet v) (hab : a ≠ b)
    (hedge : ∀ y ∈ D.nearestSet v, y ≠ a → y ≠ b → 0 < cross a b y) :
    ∃ p q : ℕ, p ≤ D.delLast v ∧ q ≤ D.delLast v ∧ D.delVert v p = a ∧ D.delVert v q = b ∧
      (q = p + 1 ∨ (p = D.delLast v ∧ q = 0)) := by
  have hpos := D.nd_pos_of_three_nearest h3
  obtain ⟨p, hp, hpa⟩ := D.exists_delVert_eq hpos ha
  obtain ⟨q, hq, hqb⟩ := D.exists_delVert_eq hpos hb
  have hpq : p ≠ q := by
    rintro rfl
    exact hab (by rw [← hpa, ← hqb])
  -- the hypothesis, transported to indices
  have hidx : ∀ m : ℕ, m ≤ D.delLast v → m ≠ p → m ≠ q →
      0 < cross (D.delVert v p) (D.delVert v q) (D.delVert v m) := by
    intro m hm hmp hmq
    rw [hpa, hqb]
    refine hedge _ (D.delVert_mem_nearestSet hpos hm) ?_ ?_
    · rw [← hpa]; exact fun hc => hmp (D.delVert_injOn hpos hm hp hc)
    · rw [← hqb]; exact fun hc => hmq (D.delVert_injOn hpos hm hq hc)
  refine ⟨p, q, hp, hq, hpa, hqb, ?_⟩
  rcases lt_or_gt_of_ne hpq with hlt | hlt
  · -- `p < q`: no index strictly between
    left
    by_contra hcon
    have hmid : p + 1 < q := by omega
    have h1 := hidx (p + 1) (by omega) (by omega) (by omega)
    have h2 : 0 < cross (D.delVert v p) (D.delVert v (p + 1)) (D.delVert v q) :=
      D.cross_delVert_pos h3 (Nat.lt_succ_self p) hmid hq
    rw [cross_swap (D.delVert v p) (D.delVert v q) (D.delVert v (p + 1))] at h1
    linarith
  · -- `q < p`: nothing below `q` and nothing above `p`
    right
    constructor
    · by_contra hcon
      have hplt : p < D.delLast v := lt_of_le_of_ne hp hcon
      have h1 := hidx (p + 1) (by omega) (by omega) (by omega)
      have h2 : 0 < cross (D.delVert v q) (D.delVert v p) (D.delVert v (p + 1)) :=
        D.cross_delVert_pos h3 hlt (Nat.lt_succ_self p) (by omega)
      rw [cross_swap_left (D.delVert v p) (D.delVert v q) (D.delVert v (p + 1))] at h1
      linarith
    · by_contra hcon
      have hq0 : 0 < q := Nat.pos_of_ne_zero hcon
      have h1 := hidx (q - 1) (by omega) (by omega) (by omega)
      have h2 : 0 < cross (D.delVert v q) (D.delVert v p) (D.delVert v (q - 1)) :=
        D.cross_delVert_wrap h3 hlt hp (by omega)
      rw [cross_swap_left (D.delVert v p) (D.delVert v q) (D.delVert v (q - 1))] at h1
      linarith

end DeloneSet

end Conjecture41
