import Conjecture41.CanonicalFan

set_option autoImplicit false

/-!
# The global canonical fan triangulation of a Delone set

Using the canonical fan of `CanonicalFan.lean` on every full-dimensional
Delaunay cell we obtain a single global family of triangles

```
  delTri v i ,   3 ≤ nsCard v ,  1 ≤ i < delLast v
```

and this file proves its basic properties:

* `DeloneSet.delVert_mem_carrier` — all vertices are sites;
* `DeloneSet.cross_delTri_pos` — every triangle is positively oriented, hence
  nondegenerate;
* `DeloneSet.exists_delTri` — the triangles cover the plane;
* `DeloneSet.disjoint_interior_delTri` — distinct triangles have disjoint
  interiors;
* `DeloneSet.inCircleDet_delTri_nonneg` — every triangle satisfies the weak
  Delaunay in-circle inequality against every site;
* `DeloneSet.mem_nearestSet_of_mem_delCell` — a site lying in a Delaunay cell
  is a vertex of that cell, whence `DeloneSet.exists_delTri_vertex`: every site
  is a vertex of some triangle of the family;
* `DeloneSet.delTri_translate` — the family is equivariant under every
  translation preserving the Delone set.
-/

namespace Conjecture41

open Set

namespace DeloneSet

variable (D : DeloneSet)

/-- The `i`-th triangle of the canonical fan of the Delaunay cell of `v`. -/
noncomputable def delTri (v : Plane) (i : ℕ) : Set Plane :=
  convexHull ℝ ({D.delVert v 0, D.delVert v i, D.delVert v (i + 1)} : Set Plane)

/-- The index set of the global triangle family. -/
def IsFanIndex (v : Plane) (i : ℕ) : Prop := 3 ≤ D.nsCard v ∧ 1 ≤ i ∧ i < D.delLast v

lemma delTri_eq_tri {v : Plane} {P : InscribedPolygon} (hvert : ∀ i : ℕ, P.vert i = D.delVert v i)
    (i : ℕ) : P.tri i = D.delTri v i := by
  unfold InscribedPolygon.tri delTri
  rw [hvert 0, hvert i, hvert (i + 1)]

/-! ### Vertices -/

lemma delVert_mem_carrier {v : Plane} (h3 : 3 ≤ D.nsCard v) {i : ℕ} (hi : i ≤ D.delLast v) :
    D.delVert v i ∈ D.carrier :=
  (D.delVert_mem_nearestSet (D.nd_pos_of_three_nearest h3) hi).1

/-! ### Orientation -/

lemma cross_delTri_pos {v : Plane} (h3 : 3 ≤ D.nsCard v) {i : ℕ} (hi : 1 ≤ i)
    (hlt : i < D.delLast v) :
    0 < cross (D.delVert v 0) (D.delVert v i) (D.delVert v (i + 1)) := by
  obtain ⟨P, -, -, hlast, hvert, -, -⟩ := D.exists_delPoly h3
  have := P.cross_tri_pos hi (by rw [hlast]; exact hlt)
  rwa [hvert 0, hvert i, hvert (i + 1)] at this

/-! ### Covering -/

lemma delCell_eq_iUnion_delTri {v : Plane} (h3 : 3 ≤ D.nsCard v) :
    D.delCell v = ⋃ i ∈ Finset.Ico 1 (D.delLast v), D.delTri v i := by
  obtain ⟨P, -, -, hlast, hvert, -, hpoly⟩ := D.exists_delPoly h3
  rw [← hpoly, P.poly_eq_iUnion_tri, hlast]
  exact Set.iUnion₂_congr fun i _ => D.delTri_eq_tri hvert i

lemma delTri_subset_delCell {v : Plane} (h3 : 3 ≤ D.nsCard v) {i : ℕ} (hlt : i < D.delLast v) :
    D.delTri v i ⊆ D.delCell v := by
  obtain ⟨P, -, -, hlast, hvert, -, hpoly⟩ := D.exists_delPoly h3
  rw [← hpoly, ← D.delTri_eq_tri hvert i]
  exact P.tri_subset_poly (by rw [hlast]; exact hlt)

/-- **The canonical fan triangles cover the plane.** -/
theorem exists_delTri (z : Plane) : ∃ (v : Plane) (i : ℕ), D.IsFanIndex v i ∧ z ∈ D.delTri v i := by
  obtain ⟨v, hz, h3⟩ := D.exists_delCell_three z
  rw [D.delCell_eq_iUnion_delTri h3] at hz
  obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp hz
  rw [Finset.mem_Ico] at hi
  exact ⟨v, i, ⟨h3, hi.1, hi.2⟩, hzi⟩

/-! ### Disjoint interiors -/

lemma disjoint_interior_delTri_same {v : Plane} (h3 : 3 ≤ D.nsCard v) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i < j) (hj : j < D.delLast v) :
    Disjoint (interior (D.delTri v i)) (interior (D.delTri v j)) := by
  obtain ⟨P, -, -, hlast, hvert, -, -⟩ := D.exists_delPoly h3
  have := P.disjoint_interior_tri hi hij (by rw [hlast]; exact hj)
  rwa [D.delTri_eq_tri hvert i, D.delTri_eq_tri hvert j] at this

/-- **Distinct triangles of the global family have disjoint interiors.** -/
theorem disjoint_interior_delTri {v v' : Plane} {i j : ℕ} (hv : D.IsFanIndex v i)
    (hv' : D.IsFanIndex v' j) (hne : (v, i) ≠ (v', j)) :
    Disjoint (interior (D.delTri v i)) (interior (D.delTri v' j)) := by
  by_cases hvv : v = v'
  · subst hvv
    have hij : i ≠ j := fun h => hne (by rw [h])
    rcases lt_or_gt_of_ne hij with h | h
    · exact D.disjoint_interior_delTri_same hv.1 hv.2.1 h hv'.2.2
    · exact (D.disjoint_interior_delTri_same hv.1 hv'.2.1 h hv.2.2).symm
  · refine Set.disjoint_left.mpr fun x hx hx' => hvv ?_
    have h1 : x ∈ interior (D.delCell v) :=
      interior_mono (D.delTri_subset_delCell hv.1 hv.2.2) hx
    have h2 : x ∈ D.delCell v' :=
      interior_subset (interior_mono (D.delTri_subset_delCell hv'.1 hv'.2.2) hx')
    exact D.center_eq_of_mem_interior h1 h2

/-! ### The weak Delaunay inequality -/

/-- **The weak Delaunay (empty circumcircle) inequality** for every triangle of
the global family. -/
theorem inCircleDet_delTri_nonneg {v : Plane} (h3 : 3 ≤ D.nsCard v) {i : ℕ} (hi : 1 ≤ i)
    (hlt : i < D.delLast v) {e : Plane} (he : e ∈ D.carrier) :
    0 ≤ inCircleDet (D.delVert v 0) (D.delVert v i) (D.delVert v (i + 1)) e := by
  have hpos := D.nd_pos_of_three_nearest h3
  exact D.inCircleDet_nonneg_of_nearestSet
    (D.delVert_mem_nearestSet hpos (Nat.zero_le _))
    (D.delVert_mem_nearestSet hpos (le_of_lt hlt))
    (D.delVert_mem_nearestSet hpos hlt) he (D.cross_delTri_pos h3 hi hlt)

/-! ### Sites in a Delaunay cell are vertices of the cell -/

lemma nd_eq_zero_of_mem_carrier {x : Plane} (hx : x ∈ D.carrier) : D.nd x = 0 :=
  Metric.infDist_zero_of_mem hx

/-- A site lying in a Delaunay cell is one of the nearest sites of its
centre. -/
theorem mem_nearestSet_of_mem_delCell {v x : Plane} (hx : x ∈ D.carrier)
    (hxc : x ∈ D.delCell v) : x ∈ D.nearestSet v := by
  have h1 : D.pw v x ≤ D.pw x x := D.pw_le_of_mem_delCell hxc x
  have h2 : D.pw x x = 0 := by
    simp [pw, D.nd_eq_zero_of_mem_carrier hx]
  have h3 : 0 ≤ D.pw v x := D.pw_nonneg hx
  exact (D.pw_eq_zero_iff hx).mp (le_antisymm (by linarith) h3)

/-- **Every site is a vertex of a triangle of the global family.** -/
theorem exists_delTri_vertex {x : Plane} (hx : x ∈ D.carrier) :
    ∃ (v : Plane) (i : ℕ), D.IsFanIndex v i ∧
      (x = D.delVert v 0 ∨ x = D.delVert v i ∨ x = D.delVert v (i + 1)) := by
  obtain ⟨v, hxc, h3⟩ := D.exists_delCell_three x
  have hpos := D.nd_pos_of_three_nearest h3
  obtain ⟨j, hj, hje⟩ := D.exists_delVert_eq hpos (D.mem_nearestSet_of_mem_delCell hx hxc)
  have hlast : 2 ≤ D.delLast v := by
    have h1 : D.delLast v = D.nsCard v - 1 := rfl
    omega
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · exact ⟨v, 1, ⟨h3, le_rfl, by omega⟩, Or.inl (by rw [← hje, hj0])⟩
  rcases lt_or_eq_of_le hj with hjlt | hjeq
  · exact ⟨v, j, ⟨h3, hj0, hjlt⟩, Or.inr (Or.inl hje.symm)⟩
  · refine ⟨v, D.delLast v - 1, ⟨h3, by omega, by omega⟩, Or.inr (Or.inr ?_)⟩
    rw [show D.delLast v - 1 + 1 = D.delLast v by omega, ← hjeq, hje]

/-! ### Equivariance -/

variable {w : Plane}

lemma delTri_translate (hw : (fun p : Plane => p + w) '' D.carrier = D.carrier)
    (v : Plane) (i : ℕ) :
    D.delTri (v + w) i = (fun p : Plane => p + w) '' D.delTri v i := by
  have himg : ∀ S : Set Plane, (fun p : Plane => p + w) '' convexHull ℝ S
      = convexHull ℝ ((fun p : Plane => p + w) '' S) := by
    intro S
    have := AffineMap.image_convexHull (AffineMap.const ℝ Plane w +ᵥ AffineMap.id ℝ Plane) S
    simpa [add_comm] using this
  unfold delTri
  rw [himg, D.delVert_translate hw v 0, D.delVert_translate hw v i,
    D.delVert_translate hw v (i + 1)]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨D.delVert v 0, Or.inl rfl, rfl⟩
    · exact ⟨D.delVert v i, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨D.delVert v (i + 1), Or.inr (Or.inr rfl), rfl⟩
  · rintro ⟨z, (rfl | rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

lemma isFanIndex_translate (hw : (fun p : Plane => p + w) '' D.carrier = D.carrier)
    (v : Plane) (i : ℕ) : D.IsFanIndex (v + w) i ↔ D.IsFanIndex v i := by
  unfold IsFanIndex
  rw [D.nsCard_translate hw v, D.delLast_translate hw v]

end DeloneSet

end Conjecture41
