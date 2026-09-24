import Conjecture41.EdgeToEdge

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Darts of the global fan triangulation and their reversal

A *dart* of the global canonical fan family is a triple `(v, i, j)` consisting
of a fan index `(v, i)` together with a corner `j : Fin 3`; the directed edge
of the dart is `(dvert v i (j+1), dvert v i (j+2))`, where

```
dvert v i = ![delVert v 0, delVert v i, delVert v (i+1)]
```

lists the three vertices of the triangle `delTri v i` in positive orientation.

`EdgeToEdge.lean` shows that a directed edge determines the triangle carrying
it.  Together with the fact that the three vertices of a triangle are pairwise
distinct, this gives the *dart reversal involution*
`DeloneSet.revDart`, characterized by

```
DeloneSet.isRev_revDart :   IsRev (revDart d) d
DeloneSet.revDart_revDart : revDart (revDart d) = d
DeloneSet.revDart_ne :      revDart d ≠ d
DeloneSet.revDart_translate : revDart (d + w) = revDart d + w
```

the last of which is the lattice equivariance used to descend the pairing to
the quotient torus.
-/

namespace Conjecture41

open Set

lemma fin3_add_one_ne_add_two (j : Fin 3) : j + 1 ≠ j + 2 := by
  revert j; decide

/-- Cyclic invariance of the in-circle determinant in its first three
arguments. -/
lemma inCircleDet_cyclic (a b c d : Plane) : inCircleDet a b c d = inCircleDet b c a d := by
  simp only [inCircleDet]
  ring

namespace DeloneSet

variable (D : DeloneSet)

/-- The three vertices of the fan triangle `(v, i)`, in positive orientation. -/
noncomputable def dvert (v : Plane) (i : ℕ) : Fin 3 → Plane :=
  ![D.delVert v 0, D.delVert v i, D.delVert v (i + 1)]

@[simp] lemma dvert_zero (v : Plane) (i : ℕ) : D.dvert v i 0 = D.delVert v 0 := rfl
@[simp] lemma dvert_one (v : Plane) (i : ℕ) : D.dvert v i 1 = D.delVert v i := rfl
@[simp] lemma dvert_two (v : Plane) (i : ℕ) : D.dvert v i 2 = D.delVert v (i + 1) := rfl

lemma delTri_eq_dvert (v : Plane) (i : ℕ) :
    D.delTri v i = convexHull ℝ ({D.dvert v i 0, D.dvert v i 1, D.dvert v i 2} : Set Plane) := rfl

lemma cross_dvert_pos {v : Plane} {i : ℕ} (hidx : D.IsFanIndex v i) :
    0 < cross (D.dvert v i 0) (D.dvert v i 1) (D.dvert v i 2) :=
  D.cross_delTri_pos hidx.1 hidx.2.1 hidx.2.2

lemma cross_dvert_cyclic {v : Plane} {i : ℕ} (hidx : D.IsFanIndex v i) (j : Fin 3) :
    0 < cross (D.dvert v i j) (D.dvert v i (j + 1)) (D.dvert v i (j + 2)) := by
  have h := D.cross_dvert_pos hidx
  have e1 : cross (D.dvert v i 1) (D.dvert v i 2) (D.dvert v i 0)
      = cross (D.dvert v i 0) (D.dvert v i 1) (D.dvert v i 2) := (cross_cyclic _ _ _).symm
  have e2 : cross (D.dvert v i 2) (D.dvert v i 0) (D.dvert v i 1)
      = cross (D.dvert v i 0) (D.dvert v i 1) (D.dvert v i 2) := by
    rw [cross_cyclic (D.dvert v i 2)]
  fin_cases j
  · exact h
  · show 0 < cross (D.dvert v i 1) (D.dvert v i 2) (D.dvert v i 0)
    rw [e1]; exact h
  · show 0 < cross (D.dvert v i 2) (D.dvert v i 0) (D.dvert v i 1)
    rw [e2]; exact h

lemma dvert_ne_of_ne {v : Plane} {i : ℕ} (hidx : D.IsFanIndex v i) {j k : Fin 3} (h : j ≠ k) :
    D.dvert v i j ≠ D.dvert v i k := by
  have h012 := D.cross_dvert_pos hidx
  have h01 : D.dvert v i 0 ≠ D.dvert v i 1 := by
    intro he; rw [he] at h012; simp only [cross] at h012; nlinarith [h012]
  have h02 : D.dvert v i 0 ≠ D.dvert v i 2 := by
    intro he; rw [he] at h012; simp only [cross] at h012; nlinarith [h012]
  have h12 : D.dvert v i 1 ≠ D.dvert v i 2 := by
    intro he; rw [he] at h012; simp only [cross] at h012; nlinarith [h012]
  have h10 : D.dvert v i 1 ≠ D.dvert v i 0 := Ne.symm h01
  have h20 : D.dvert v i 2 ≠ D.dvert v i 0 := Ne.symm h02
  have h21 : D.dvert v i 2 ≠ D.dvert v i 1 := Ne.symm h12
  fin_cases j <;> fin_cases k <;> simp_all

lemma dvert_injective {v : Plane} {i : ℕ} (hidx : D.IsFanIndex v i) :
    Function.Injective (D.dvert v i) := by
  intro j k h
  by_contra hne
  exact D.dvert_ne_of_ne hidx hne h

lemma dvert_mem_carrier {v : Plane} {i : ℕ} (hidx : D.IsFanIndex v i) (j : Fin 3) :
    D.dvert v i j ∈ D.carrier := by
  fin_cases j
  · exact D.delVert_mem_carrier hidx.1 (Nat.zero_le _)
  · exact D.delVert_mem_carrier hidx.1 (le_of_lt hidx.2.2)
  · exact D.delVert_mem_carrier hidx.1 hidx.2.2

/-- The weak Delaunay in-circle inequality at every corner of every triangle of
the global fan family. -/
lemma inCircleDet_dvert_nonneg {v : Plane} {i : ℕ} (hidx : D.IsFanIndex v i) (j : Fin 3)
    {e : Plane} (he : e ∈ D.carrier) :
    0 ≤ inCircleDet (D.dvert v i j) (D.dvert v i (j + 1)) (D.dvert v i (j + 2)) e := by
  have h := D.inCircleDet_delTri_nonneg hidx.1 hidx.2.1 hidx.2.2 he
  have h0 : 0 ≤ inCircleDet (D.dvert v i 0) (D.dvert v i 1) (D.dvert v i 2) e := h
  fin_cases j
  · exact h0
  · show 0 ≤ inCircleDet (D.dvert v i 1) (D.dvert v i 2) (D.dvert v i 0) e
    rw [← inCircleDet_cyclic]
    exact h0
  · show 0 ≤ inCircleDet (D.dvert v i 2) (D.dvert v i 0) (D.dvert v i 1) e
    rw [← inCircleDet_cyclic, ← inCircleDet_cyclic]
    exact h0

/-! ### Darts and the `IsDart` predicate -/

lemma isDart_of_corner {v : Plane} {i : ℕ} (hidx : D.IsFanIndex v i) (j : Fin 3) :
    D.IsDart v i (D.dvert v i (j + 1)) (D.dvert v i (j + 2)) := by
  refine ⟨hidx, ?_⟩
  fin_cases j
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exact Or.inl ⟨rfl, rfl⟩

lemma corner_of_isDart {v : Plane} {i : ℕ} {x y : Plane} (h : D.IsDart v i x y) :
    ∃ j : Fin 3, x = D.dvert v i (j + 1) ∧ y = D.dvert v i (j + 2) := by
  rcases h.2 with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact ⟨2, hx, hy⟩
  · exact ⟨0, hx, hy⟩
  · exact ⟨1, hx, hy⟩

/-! ### The reversal involution -/

/-- `IsRev e d` says that the dart `e` carries the reverse of the directed edge
of the dart `d`. -/
def IsRev (e d : Plane × ℕ × Fin 3) : Prop :=
  D.IsFanIndex e.1 e.2.1 ∧
    D.dvert e.1 e.2.1 (e.2.2 + 1) = D.dvert d.1 d.2.1 (d.2.2 + 2) ∧
      D.dvert e.1 e.2.1 (e.2.2 + 2) = D.dvert d.1 d.2.1 (d.2.2 + 1)

lemma isRev_symm {e d : Plane × ℕ × Fin 3} (hd : D.IsFanIndex d.1 d.2.1) (h : D.IsRev e d) :
    D.IsRev d e :=
  ⟨hd, h.2.2.symm, h.2.1.symm⟩

/-- **Existence and uniqueness of the reverse dart.** -/
theorem existsUnique_isRev {d : Plane × ℕ × Fin 3} (hd : D.IsFanIndex d.1 d.2.1) :
    ∃! e : Plane × ℕ × Fin 3, D.IsRev e d := by
  obtain ⟨v, i, j⟩ := d
  have hdart : D.IsDart v i (D.dvert v i (j + 1)) (D.dvert v i (j + 2)) :=
    D.isDart_of_corner hd j
  obtain ⟨⟨v', i'⟩, hd', huniq⟩ := D.exists_unique_reverse_dart hdart
  obtain ⟨j', hj1, hj2⟩ := D.corner_of_isDart hd'
  refine ⟨(v', i', j'), ⟨hd'.1, hj1.symm, hj2.symm⟩, ?_⟩
  rintro ⟨w, k, l⟩ ⟨hidx, he1, he2⟩
  have hdartl : D.IsDart w k (D.dvert v i (j + 2)) (D.dvert v i (j + 1)) := by
    rw [← he1, ← he2]
    exact D.isDart_of_corner hidx l
  have hwk : (w, k) = (v', i') := huniq (w, k) hdartl
  have hw : w = v' := congrArg Prod.fst hwk
  have hk : k = i' := congrArg Prod.snd hwk
  subst hw; subst hk
  have hll : l + 1 = j' + 1 := by
    refine D.dvert_injective hidx ?_
    rw [he1, hj1]
  have : l = j' := by
    have := congrArg (fun t : Fin 3 => t + 2) hll
    simpa [add_assoc] using this
  simp [this]

open Classical in
/-- The reverse dart. -/
noncomputable def revDart (d : Plane × ℕ × Fin 3) : Plane × ℕ × Fin 3 :=
  if h : ∃ e : Plane × ℕ × Fin 3, D.IsRev e d then h.choose else d

lemma revDart_eq {d e : Plane × ℕ × Fin 3} (hd : D.IsFanIndex d.1 d.2.1) (he : D.IsRev e d) :
    D.revDart d = e := by
  classical
  obtain ⟨e', -, huniq⟩ := D.existsUnique_isRev hd
  have hex : ∃ e : Plane × ℕ × Fin 3, D.IsRev e d := ⟨e, he⟩
  rw [revDart, dif_pos hex]
  rw [huniq _ hex.choose_spec, huniq _ he]

lemma isRev_revDart {d : Plane × ℕ × Fin 3} (hd : D.IsFanIndex d.1 d.2.1) :
    D.IsRev (D.revDart d) d := by
  obtain ⟨e, he, -⟩ := D.existsUnique_isRev hd
  rw [D.revDart_eq hd he]
  exact he

lemma isFanIndex_revDart {d : Plane × ℕ × Fin 3} (hd : D.IsFanIndex d.1 d.2.1) :
    D.IsFanIndex (D.revDart d).1 (D.revDart d).2.1 := (D.isRev_revDart hd).1

/-- **The dart reversal is an involution.** -/
theorem revDart_revDart {d : Plane × ℕ × Fin 3} (hd : D.IsFanIndex d.1 d.2.1) :
    D.revDart (D.revDart d) = d := by
  have h1 := D.isRev_revDart hd
  exact D.revDart_eq (D.isFanIndex_revDart hd) (D.isRev_symm hd h1)

/-- **The dart reversal is fixed-point free.** -/
theorem revDart_ne {d : Plane × ℕ × Fin 3} (hd : D.IsFanIndex d.1 d.2.1) :
    D.revDart d ≠ d := by
  intro hcon
  have h := D.isRev_revDart hd
  rw [hcon] at h
  have := h.2.1
  exact D.dvert_ne_of_ne hd (fin3_add_one_ne_add_two d.2.2) this

/-! ### Equivariance -/

variable {w : Plane}

lemma dvert_translate (hw : (fun p : Plane => p + w) '' D.carrier = D.carrier)
    (v : Plane) (i : ℕ) (j : Fin 3) : D.dvert (v + w) i j = D.dvert v i j + w := by
  have h0 : D.dvert (v + w) i 0 = D.dvert v i 0 + w := D.delVert_translate hw v 0
  have h1 : D.dvert (v + w) i 1 = D.dvert v i 1 + w := D.delVert_translate hw v i
  have h2 : D.dvert (v + w) i 2 = D.dvert v i 2 + w := D.delVert_translate hw v (i + 1)
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

lemma isRev_translate (hw : (fun p : Plane => p + w) '' D.carrier = D.carrier)
    (e d : Plane × ℕ × Fin 3) :
    D.IsRev (e.1 + w, e.2) (d.1 + w, d.2) ↔ D.IsRev e d := by
  unfold IsRev
  simp only [D.dvert_translate hw, D.isFanIndex_translate hw]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, add_right_cancel h2, add_right_cancel h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by rw [h2], by rw [h3]⟩

/-- **The dart reversal is equivariant.** -/
theorem revDart_translate (hw : (fun p : Plane => p + w) '' D.carrier = D.carrier)
    {d : Plane × ℕ × Fin 3} (hd : D.IsFanIndex d.1 d.2.1) :
    D.revDart (d.1 + w, d.2) = ((D.revDart d).1 + w, (D.revDart d).2) := by
  have hd' : D.IsFanIndex ((d.1 + w, d.2) : Plane × ℕ × Fin 3).1
      ((d.1 + w, d.2) : Plane × ℕ × Fin 3).2.1 := by
    simpa [D.isFanIndex_translate hw] using hd
  refine D.revDart_eq hd' ?_
  exact (D.isRev_translate hw (D.revDart d) d).mpr (D.isRev_revDart hd)

end DeloneSet

end Conjecture41
