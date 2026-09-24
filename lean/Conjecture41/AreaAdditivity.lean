import Conjecture41.TriangleArea

set_option autoImplicit false

/-!
# Additivity of area over a tiling with disjoint interiors

The area gate of the periodic construction needs to turn a geometric tiling of
the plane by convex cells into an identity between the total area of the cells
meeting a fundamental domain and the area of that domain.  This file records
the two general measure-theoretic steps involved:

* `aedisjoint_of_disjoint_interior`: two closed convex sets with disjoint
  interiors are almost everywhere disjoint, because their intersection is
  contained in the union of their frontiers, and the frontier of a convex set
  is Lebesgue null;
* `tsum_volume_inter_of_cover`: a countable, almost everywhere disjoint,
  measurable cover of the plane splits the measure of any measurable set into
  the sum of the measures of its pieces.

Both are stated for `Plane`, which is all that is needed here.
-/

namespace Conjecture41

open MeasureTheory Set

/-- The frontier of a convex subset of the plane is Lebesgue null. -/
lemma volume_frontier_eq_zero_of_convex {s : Set Plane} (hs : Convex ℝ s) :
    volume (frontier s) = 0 :=
  hs.addHaar_frontier volume

/-- Two convex sets with disjoint interiors are almost everywhere disjoint. -/
lemma aedisjoint_of_disjoint_interior {s t : Set Plane} (hs : Convex ℝ s) (ht : Convex ℝ t)
    (h : Disjoint (interior s) (interior t)) : AEDisjoint volume s t := by
  have hsub : s ∩ t ⊆ frontier s ∪ frontier t := by
    rintro x ⟨hxs, hxt⟩
    by_cases hx : x ∈ interior s
    · refine Or.inr ⟨subset_closure hxt, ?_⟩
      intro hxt'
      exact (Set.disjoint_left.mp h hx) hxt'
    · exact Or.inl ⟨subset_closure hxs, hx⟩
  refine measure_mono_null hsub ?_
  exact measure_union_null (volume_frontier_eq_zero_of_convex hs)
    (volume_frontier_eq_zero_of_convex ht)

/-- A countable almost everywhere disjoint measurable cover of the plane
decomposes the area of any measurable set. -/
theorem tsum_volume_inter_of_cover {ι : Type*} [Countable ι] (K : ι → Set Plane)
    (hmeas : ∀ i, NullMeasurableSet (K i) volume)
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) K))
    (hcover : (⋃ i, K i) = Set.univ) {D : Set Plane} (hD : MeasurableSet D) :
    ∑' i, volume (K i ∩ D) = volume D := by
  have hDeq : D = ⋃ i, K i ∩ D := by
    rw [← Set.iUnion_inter, hcover, Set.univ_inter]
  calc ∑' i, volume (K i ∩ D)
      = volume (⋃ i, K i ∩ D) := by
        refine (measure_iUnion₀ ?_ ?_).symm
        · intro i j hij
          exact AEDisjoint.mono (hdisj hij) Set.inter_subset_left Set.inter_subset_left
        · intro i
          exact (hmeas i).inter hD.nullMeasurableSet
    _ = volume D := by rw [← hDeq]

end Conjecture41
