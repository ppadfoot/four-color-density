import Conjecture41.DelaunayFan
import Conjecture41.DelaunayGrow

set_option autoImplicit false

/-!
# The canonical (equivariant) fan of a Delaunay cell

`DelaunayFan.lean` proves the *existence* of an inscribed polygon presenting a
full-dimensional Delaunay cell.  For the periodic construction we need a
*canonical* choice, so that the fan of a translated cell is the translate of
the fan of the cell.  This file provides it.

The construction is the obvious one and is manifestly translation equivariant:

* `angleSet v A` is the finite set of angular coordinates `circleAngle v a`,
  `a ∈ A`;
* `nthAngle S i` is the `i`-th smallest element of a finite set `S ⊆ ℝ`;
* `DeloneSet.delAngle v i` is the `i`-th smallest angular coordinate of the
  nearest sites of `v`, and `DeloneSet.delVert v i` the corresponding site.

Translation invariance of `circleAngle` (`circleAngle_add`) gives
`angleSet (v + w) (A + w) = angleSet v A`, hence
`delAngle (v + w) i = delAngle v i` and `delVert (v + w) i = delVert v i + w`
whenever the translation `w` preserves the Delone set.  No choice of orbit
representatives is involved.

`DeloneSet.exists_delPoly` shows that these canonical data really are the data
of an `InscribedPolygon` whose convex hull is the Delaunay cell, so all the
results of `Fan.lean` transfer verbatim.
-/

namespace Conjecture41

open Set

/-- Translating the centre translates the point of the circle. -/
lemma circlePoint_add (v w : Plane) (R t : ℝ) :
    circlePoint (v + w) R t = circlePoint v R t + w := by
  unfold circlePoint
  abel

/-- The finite set of angular coordinates of `A` as seen from `v`. -/
noncomputable def angleSet (v : Plane) (A : Finset Plane) : Finset ℝ :=
  A.image (circleAngle v)

lemma mem_angleSet {v : Plane} {A : Finset Plane} {t : ℝ} :
    t ∈ angleSet v A ↔ ∃ a ∈ A, circleAngle v a = t := by
  simp [angleSet]

/-- The angular coordinates are translation invariant. -/
lemma angleSet_translate (v w : Plane) (A : Finset Plane) :
    angleSet (v + w) (A.image (fun p => p + w)) = angleSet v A := by
  classical
  unfold angleSet
  rw [Finset.image_image]
  refine Finset.image_congr ?_
  intro x _
  exact circleAngle_add v x w

/-- The `i`-th smallest element of a finite set of reals (junk value `0` when
the index is out of range). -/
noncomputable def nthAngle (S : Finset ℝ) (i : ℕ) : ℝ :=
  if h : i < S.card then S.orderEmbOfFin rfl ⟨i, h⟩ else 0

lemma nthAngle_mem {S : Finset ℝ} {i : ℕ} (h : i < S.card) : nthAngle S i ∈ S := by
  rw [nthAngle, dif_pos h]
  exact S.orderEmbOfFin_mem rfl ⟨i, h⟩

lemma nthAngle_strictMono {S : Finset ℝ} {i j : ℕ} (hij : i < j) (hj : j < S.card) :
    nthAngle S i < nthAngle S j := by
  have hi : i < S.card := lt_trans hij hj
  rw [nthAngle, dif_pos hi, nthAngle, dif_pos hj]
  exact (S.orderEmbOfFin rfl).strictMono (show (⟨i, hi⟩ : Fin S.card) < ⟨j, hj⟩ from hij)

lemma exists_nthAngle {S : Finset ℝ} {t : ℝ} (ht : t ∈ S) :
    ∃ i : ℕ, i < S.card ∧ nthAngle S i = t := by
  have : t ∈ Set.range (S.orderEmbOfFin (k := S.card) rfl) := by
    rw [S.range_orderEmbOfFin rfl]; exact ht
  obtain ⟨i, hi⟩ := this
  exact ⟨(i : ℕ), i.isLt, by rw [nthAngle, dif_pos i.isLt]; simpa using hi⟩

namespace DeloneSet

variable (D : DeloneSet)

/-- The nearest sites of `v`, as a `Finset`. -/
noncomputable def nearFinset (v : Plane) : Finset Plane := (D.nearestSet_finite v).toFinset

@[simp] lemma mem_nearFinset {v x : Plane} : x ∈ D.nearFinset v ↔ x ∈ D.nearestSet v := by
  simp [nearFinset]

@[simp] lemma coe_nearFinset (v : Plane) : (D.nearFinset v : Set Plane) = D.nearestSet v := by
  ext x; simp

lemma card_nearFinset (v : Plane) : (D.nearFinset v).card = D.nsCard v := rfl

/-- The `i`-th smallest angular coordinate of the nearest sites of `v`. -/
noncomputable def delAngle (v : Plane) (i : ℕ) : ℝ := nthAngle (angleSet v (D.nearFinset v)) i

/-- The `i`-th vertex of the canonical fan of the Delaunay cell of `v`. -/
noncomputable def delVert (v : Plane) (i : ℕ) : Plane :=
  circlePoint v (D.nd v) (D.delAngle v i)

/-- The index of the last vertex of the canonical fan of the cell of `v`. -/
noncomputable def delLast (v : Plane) : ℕ := D.nsCard v - 1

lemma nsCard_pos (v : Plane) : 0 < D.nsCard v := by
  obtain ⟨x, hx⟩ := D.nearestSet_nonempty v
  exact Finset.card_pos.mpr ⟨x, by simpa using hx⟩

lemma dist_mem_nearFinset {v a : Plane} (ha : a ∈ D.nearFinset v) : dist a v = D.nd v := by
  rw [dist_comm]
  exact ((D.mem_nearFinset).mp ha).2

lemma injOn_circleAngle_nearFinset {v : Plane} (hpos : 0 < D.nd v) :
    Set.InjOn (circleAngle v) (D.nearFinset v : Set Plane) := by
  intro a ha b hb hab
  exact circleAngle_injOn hpos (D.dist_mem_nearFinset (by simpa using ha))
    (D.dist_mem_nearFinset (by simpa using hb)) hab

lemma card_angleSet {v : Plane} (hpos : 0 < D.nd v) :
    (angleSet v (D.nearFinset v)).card = D.nsCard v := by
  classical
  rw [angleSet, Finset.card_image_of_injOn (D.injOn_circleAngle_nearFinset hpos)]
  rfl

lemma delAngle_lt {v : Plane} (hpos : 0 < D.nd v) {i j : ℕ} (hij : i < j)
    (hj : j ≤ D.delLast v) : D.delAngle v i < D.delAngle v j := by
  refine nthAngle_strictMono hij ?_
  rw [D.card_angleSet hpos]
  have h1 : D.delLast v = D.nsCard v - 1 := rfl
  have h2 := D.nsCard_pos v
  omega

lemma delAngle_mem_Ioc {v : Plane} (hpos : 0 < D.nd v) {i : ℕ} (hi : i ≤ D.delLast v) :
    -Real.pi < D.delAngle v i ∧ D.delAngle v i ≤ Real.pi := by
  have hcard : i < (angleSet v (D.nearFinset v)).card := by
    rw [D.card_angleSet hpos]
    have h1 : D.delLast v = D.nsCard v - 1 := rfl
    have h2 := D.nsCard_pos v
    omega
  obtain ⟨a, -, ha⟩ := mem_angleSet.mp (nthAngle_mem (S := angleSet v (D.nearFinset v)) hcard)
  refine ⟨?_, ?_⟩
  · rw [delAngle, ← ha]; exact neg_pi_lt_circleAngle v a
  · rw [delAngle, ← ha]; exact circleAngle_le_pi v a

lemma delVert_mem_nearestSet {v : Plane} (hpos : 0 < D.nd v) {i : ℕ} (hi : i ≤ D.delLast v) :
    D.delVert v i ∈ D.nearestSet v := by
  have hcard : i < (angleSet v (D.nearFinset v)).card := by
    rw [D.card_angleSet hpos]
    have h1 : D.delLast v = D.nsCard v - 1 := rfl
    have h2 := D.nsCard_pos v
    omega
  obtain ⟨a, ha, hae⟩ := mem_angleSet.mp (nthAngle_mem (S := angleSet v (D.nearFinset v)) hcard)
  have : D.delVert v i = a := by
    rw [delVert, delAngle, ← hae]
    exact circlePoint_circleAngle hpos (D.dist_mem_nearFinset ha)
  rw [this]
  exact (D.mem_nearFinset).mp ha

lemma exists_delVert_eq {v : Plane} (hpos : 0 < D.nd v) {a : Plane}
    (ha : a ∈ D.nearestSet v) : ∃ i : ℕ, i ≤ D.delLast v ∧ D.delVert v i = a := by
  have haF : a ∈ D.nearFinset v := (D.mem_nearFinset).mpr ha
  obtain ⟨i, hi, hie⟩ :=
    exists_nthAngle (S := angleSet v (D.nearFinset v)) (Finset.mem_image_of_mem _ haF)
  refine ⟨i, ?_, ?_⟩
  · rw [D.card_angleSet hpos] at hi
    have h1 : D.delLast v = D.nsCard v - 1 := rfl
    omega
  · rw [delVert, delAngle, hie]
    exact circlePoint_circleAngle hpos (D.dist_mem_nearFinset haF)

/-- **The canonical fan of a full-dimensional Delaunay cell.**  The canonical
angular data of `v` are the data of an inscribed polygon whose convex hull is
the Delaunay cell of `v`. -/
theorem exists_delPoly {v : Plane} (h3 : 3 ≤ D.nsCard v) :
    ∃ P : InscribedPolygon, P.center = v ∧ P.radius = D.nd v ∧ P.last = D.delLast v ∧
      (∀ i : ℕ, P.vert i = D.delVert v i) ∧ P.verts = D.nearestSet v ∧
      P.poly = D.delCell v := by
  have hpos : 0 < D.nd v := D.nd_pos_of_three_nearest h3
  have hlast : D.delLast v = D.nsCard v - 1 := rfl
  refine ⟨{ center := v
            radius := D.nd v
            radius_pos := hpos
            last := D.delLast v
            two_le := by omega
            angle := D.delAngle v
            angle_mono := fun i j hij hj => D.delAngle_lt hpos hij hj
            window := by
              have h1 := (D.delAngle_mem_Ioc hpos (le_refl (D.delLast v))).2
              have h2 := (D.delAngle_mem_Ioc hpos (Nat.zero_le (D.delLast v))).1
              have := Real.pi_pos
              linarith }, rfl, rfl, rfl, fun i => rfl, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact D.delVert_mem_nearestSet hpos hi
    · intro hx
      obtain ⟨i, hi, hie⟩ := D.exists_delVert_eq hpos hx
      exact ⟨i, hi, hie⟩
  · show convexHull ℝ _ = D.delCell v
    congr 1
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact D.delVert_mem_nearestSet hpos hi
    · intro hx
      obtain ⟨i, hi, hie⟩ := D.exists_delVert_eq hpos hx
      exact ⟨i, hi, hie⟩

/-! ### Equivariance -/

variable {w : Plane}

lemma nearFinset_translate (hw : (fun p : Plane => p + w) '' D.carrier = D.carrier) (v : Plane) :
    D.nearFinset (v + w) = (D.nearFinset v).image (fun p => p + w) := by
  classical
  ext x
  rw [Finset.mem_image, mem_nearFinset, D.nearestSet_translate hw v]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, (D.mem_nearFinset).mpr hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, (D.mem_nearFinset).mp hy, rfl⟩

lemma delAngle_translate (hw : (fun p : Plane => p + w) '' D.carrier = D.carrier)
    (v : Plane) (i : ℕ) : D.delAngle (v + w) i = D.delAngle v i := by
  unfold delAngle
  rw [D.nearFinset_translate hw v, angleSet_translate]

lemma nsCard_translate (hw : (fun p : Plane => p + w) '' D.carrier = D.carrier) (v : Plane) :
    D.nsCard (v + w) = D.nsCard v := by
  classical
  have h := D.nearFinset_translate hw v
  have : (D.nearFinset (v + w)).card = (D.nearFinset v).card := by
    rw [h, Finset.card_image_of_injective _ (add_left_injective w)]
  simp [card_nearFinset] at this ⊢
  exact this

lemma delLast_translate (hw : (fun p : Plane => p + w) '' D.carrier = D.carrier) (v : Plane) :
    D.delLast (v + w) = D.delLast v := by
  show D.nsCard (v + w) - 1 = D.nsCard v - 1
  rw [D.nsCard_translate hw v]

/-- **Equivariance of the canonical fan.** -/
lemma delVert_translate (hw : (fun p : Plane => p + w) '' D.carrier = D.carrier)
    (v : Plane) (i : ℕ) : D.delVert (v + w) i = D.delVert v i + w := by
  unfold delVert
  rw [D.delAngle_translate hw v i, D.nd_translate hw v, circlePoint_add]

end DeloneSet

end Conjecture41
