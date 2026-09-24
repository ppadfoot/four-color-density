import Conjecture41.Cotangent

set_option autoImplicit false

/-!
# The global summation of the marked cotangent budget

This file isolates the *combinatorial* heart of the periodic weak-Delaunay
argument, in a form that makes no geometric assumption at all: the regrouping
of a sum over triangle corners into a sum over unoriented edges, followed by
the replacement of each squared edge length by its exclusion weight.

`marked_global_sum` says: if

* every corner (`dart`) of every face is assigned an edge,
* the *paired* cotangent weight of every edge is nonnegative,
* every exclusion weight is at most the corresponding squared edge length,
* every face satisfies the cotangent area identity `Σ ℓ² cot = 4K`, and
* every face satisfies the marked budget `Σ w cot ≥ 2`,

then `2 · #faces ≤ 4 · Σ_faces K`.

Combined with the Euler identity `F = 2V` and the area partition
`Σ_faces K = A` on the quotient torus, this yields `V ≤ A`.

Note that only the *sum* of the cotangents over the darts of an edge is
assumed nonnegative; individual cotangents may be negative, as they must be
for obtuse weak-Delaunay triangles.
-/

namespace Conjecture41

open Finset

/--
Global regrouping and estimate.  Faces are indexed by `F`, edges by `E`; the
`3` corners of a face are its darts, and `side` assigns to each dart the
opposite edge.
-/
theorem marked_global_sum
    {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (F : Finset ι) (E : Finset κ)
    (side : ι × Fin 3 → κ) (lsq w : κ → ℝ) (cot : ι × Fin 3 → ℝ) (K : ι → ℝ)
    (hmap : ∀ d ∈ F ×ˢ (univ : Finset (Fin 3)), side d ∈ E)
    (hcotpair : ∀ e ∈ E,
      0 ≤ ∑ d ∈ (F ×ˢ (univ : Finset (Fin 3))).filter (fun d => side d = e), cot d)
    (hw : ∀ e ∈ E, w e ≤ lsq e)
    (harea : ∀ T ∈ F, ∑ i : Fin 3, lsq (side (T, i)) * cot (T, i) = 4 * K T)
    (hbudget : ∀ T ∈ F, 2 ≤ ∑ i : Fin 3, w (side (T, i)) * cot (T, i)) :
    2 * (F.card : ℝ) ≤ 4 * ∑ T ∈ F, K T := by
  classical
  set D := F ×ˢ (univ : Finset (Fin 3)) with hD
  -- the two dart sums, regrouped over edges
  have hsum : ∀ f : κ → ℝ,
      ∑ d ∈ D, f (side d) * cot d = ∑ e ∈ E, f e * ∑ d ∈ D.filter (fun d => side d = e), cot d := by
    intro f
    rw [← Finset.sum_fiberwise_of_maps_to hmap (fun d => f (side d) * cot d)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [(Finset.mem_filter.mp hd).2]
  -- the dart sum equals the sum over faces of the per-face sum
  have hfaces : ∀ f : κ → ℝ,
      ∑ d ∈ D, f (side d) * cot d
        = ∑ T ∈ F, ∑ i : Fin 3, f (side (T, i)) * cot (T, i) := by
    intro f
    rw [hD, Finset.sum_product]
  -- lower bound from the marked budget
  have hlow : 2 * (F.card : ℝ) ≤ ∑ d ∈ D, w (side d) * cot d := by
    rw [hfaces]
    calc 2 * (F.card : ℝ) = ∑ _T ∈ F, (2 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ T ∈ F, ∑ i : Fin 3, w (side (T, i)) * cot (T, i) :=
          Finset.sum_le_sum hbudget
  -- upper bound from the edgewise comparison
  have hupp : ∑ d ∈ D, w (side d) * cot d ≤ ∑ d ∈ D, lsq (side d) * cot d := by
    rw [hsum w, hsum lsq]
    refine Finset.sum_le_sum fun e he => ?_
    exact mul_le_mul_of_nonneg_right (hw e he) (hcotpair e he)
  -- the top sum is four times the total area
  have htop : ∑ d ∈ D, lsq (side d) * cot d = 4 * ∑ T ∈ F, K T := by
    rw [hfaces, Finset.mul_sum]
    exact Finset.sum_congr rfl harea
  linarith [hlow, hupp, htop.le, htop.ge]

end Conjecture41
