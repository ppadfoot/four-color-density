import Conjecture41.CocircularFan
import Conjecture41.DelaunayTiling

set_option autoImplicit false

/-!
# Fan triangulation of a full-dimensional Delaunay cell

Combining the two previous layers:

* the nearest-site set of a Delaunay centre `v` is a finite set of sites all at
  distance `nd v` from `v` — a finite cocircular set (`DelaunayCell.lean`);
* a finite cocircular set of at least three points is an `InscribedPolygon`
  (`CocircularFan.lean`);
* an `InscribedPolygon` is triangulated by the fan based at its first vertex
  (`Fan.lean`),

we obtain that every Delaunay cell with at least three sites on its empty
circle is the union of finitely many positively oriented triangles with
vertices among those sites, with pairwise disjoint interiors.

Every triangle of the fan also satisfies the weak Delaunay (empty circumcircle)
inequality, because its three vertices lie on the empty circle of `v`; this is
`DeloneSet.inCircleDet_nonneg_of_nearestSet`, recorded here in the form
`DeloneSet.fan_delaunay`.
-/

namespace Conjecture41

open Set

namespace DeloneSet

variable (D : DeloneSet)

/-- With at least three nearest sites, the empty circle has positive radius. -/
lemma nd_pos_of_three_nearest {v : Plane}
    (hcard : 3 ≤ (D.nearestSet_finite v).toFinset.card) : 0 < D.nd v := by
  rcases (D.nd_nonneg v).lt_or_eq with h | h
  · exact h
  exfalso
  have hsub : (D.nearestSet_finite v).toFinset ⊆ {v} := by
    intro x hx
    have hx' : x ∈ D.nearestSet v := by simpa using hx
    have : dist v x = 0 := by rw [hx'.2, ← h]
    simp only [Finset.mem_singleton]
    exact (dist_eq_zero.mp this).symm
  have := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at this
  omega

/-- **The fan triangulation of a full-dimensional Delaunay cell.**  If at least
three sites lie on the empty circle of `v`, then those sites, sorted by angle,
form an inscribed polygon whose convex hull is exactly the Delaunay cell. -/
theorem exists_inscribedPolygon_delCell {v : Plane}
    (hcard : 3 ≤ (D.nearestSet_finite v).toFinset.card) :
    ∃ P : InscribedPolygon, P.center = v ∧ P.radius = D.nd v ∧
      P.verts = D.nearestSet v ∧ P.poly = D.delCell v := by
  classical
  have hpos := D.nd_pos_of_three_nearest hcard
  obtain ⟨P, hc, hr, hv, _⟩ :=
    exists_inscribedPolygon hpos (D.nearestSet_finite v).toFinset
      (by
        intro a ha
        have ha' : a ∈ D.nearestSet v := by simpa using ha
        rw [dist_comm]
        exact ha'.2)
      hcard
  refine ⟨P, hc, hr, ?_, ?_⟩
  · rw [hv]
    simp
  · unfold InscribedPolygon.poly delCell
    rw [hv]
    simp

/-- Every vertex of the fan is a site of the configuration. -/
lemma vert_mem_carrier {v : Plane} {P : InscribedPolygon}
    (hv : P.verts = D.nearestSet v) {i : ℕ} (hi : i ≤ P.last) : P.vert i ∈ D.carrier := by
  have : P.vert i ∈ P.verts := ⟨i, hi, rfl⟩
  rw [hv] at this
  exact this.1

/-- The weak Delaunay inequality for a positively oriented fan triangle. -/
lemma fan_inCircleDet_nonneg {v : Plane} {P : InscribedPolygon}
    (hv : P.verts = D.nearestSet v) {i j l : ℕ} (hi : i ≤ P.last) (hj : j ≤ P.last)
    (hl : l ≤ P.last) (hpos : 0 < cross (P.vert i) (P.vert j) (P.vert l))
    {e : Plane} (he : e ∈ D.carrier) :
    0 ≤ inCircleDet (P.vert i) (P.vert j) (P.vert l) e := by
  have hmem : ∀ m : ℕ, m ≤ P.last → P.vert m ∈ D.nearestSet v := by
    intro m hm
    have : P.vert m ∈ P.verts := ⟨m, hm, rfl⟩
    rwa [hv] at this
  exact D.inCircleDet_nonneg_of_nearestSet (hmem i hi) (hmem j hj) (hmem l hl) he hpos

end DeloneSet

end Conjecture41
