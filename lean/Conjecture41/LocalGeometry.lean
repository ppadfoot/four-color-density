import Conjecture41.Definitions

set_option autoImplicit false

namespace Conjecture41

/-- The four possible color patterns of a triangle. -/
inductive MarkPattern
  | allSame
  | twoSameAdjacent
  | twoSameOpposite
  | allDistinct
  deriving DecidableEq, Repr

/--
Squared exclusion weights `(wₐ,w_b,w_c)` opposite the three angles.

Ordering convention:
* in `twoSameAdjacent` and `twoSameOpposite`, the first edge joins the
  repeated color;
* in `allDistinct`, the third edge joins the opposite pair of colors.
-/
noncomputable def markWeights : MarkPattern → ℝ × ℝ × ℝ
  | .allSame => (2, 2, 2)
  | .twoSameAdjacent => (2, 5 / 4, 5 / 4)
  | .twoSameOpposite => (2, 1, 1)
  | .allDistinct => (5 / 4, 5 / 4, 1)

/-- Sixteen times the squared area in Heron's polynomial form. -/
def heron16 (x y z : ℝ) : ℝ :=
  2 * x * y + 2 * y * z + 2 * z * x - x ^ 2 - y ^ 2 - z ^ 2

/--
The numerator of the marked cotangent sum.  If `x,y,z` are squared side
lengths and `K` is the area, then this numerator divided by `4*K` is
`wₐ*cot A + w_b*cot B + w_c*cot C`.
-/
def markedNumerator
    (wa wb wc x y z : ℝ) : ℝ :=
  wa * (y + z - x) + wb * (z + x - y) + wc * (x + y - z)

/-- SOS identity for an all-same-color triangle. -/
lemma sos_allSame (x y z : ℝ) :
    markedNumerator 2 2 2 x y z ^ 2 - 4 * heron16 x y z =
      8 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  unfold markedNumerator heron16; ring

/-- SOS identity when two equal colors and the third color are adjacent. -/
lemma sos_twoSameAdjacent (x y z : ℝ) :
    markedNumerator 2 (5 / 4) (5 / 4) x y z ^ 2 - 4 * heron16 x y z =
      4 * (y + z - 3 * x / 4) ^ 2 + 2 * x ^ 2 + 4 * (y - z) ^ 2 := by
  unfold markedNumerator heron16; ring

/-- SOS identity when two equal colors and the third color are opposite. -/
lemma sos_twoSameOpposite (x y z : ℝ) :
    markedNumerator 2 1 1 x y z ^ 2 - 4 * heron16 x y z =
      4 * (x - y - z) ^ 2 + 4 * (y - z) ^ 2 := by
  unfold markedNumerator heron16; ring

/-- SOS identity for three distinct colors. -/
lemma sos_allDistinct (x y z : ℝ) :
    markedNumerator (5 / 4) (5 / 4) 1 x y z ^ 2 - 4 * heron16 x y z =
      (x + y - 5 * z / 2) ^ 2 + 4 * (x - y) ^ 2 := by
  unfold markedNumerator heron16; ring

/--
The sign lemma.  Rewriting
`markedNumerator wa wb wc x y z = x*(-wa+wb+wc) + y*(wa-wb+wc) + z*(wa+wb-wc)`,
nonnegativity follows from the three "triangle-like" inequalities on the
weights, with no hypothesis on the shape of the triangle.  This is the step
that upgrades the absolute-value consequence of the SOS identities to the
one-sided marked cotangent inequality.
-/
lemma markedNumerator_nonneg (wa wb wc x y z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h1 : 0 ≤ -wa + wb + wc) (h2 : 0 ≤ wa - wb + wc) (h3 : 0 ≤ wa + wb - wc) :
    0 ≤ markedNumerator wa wb wc x y z := by
  have : markedNumerator wa wb wc x y z =
      x * (-wa + wb + wc) + y * (wa - wb + wc) + z * (wa + wb - wc) := by
    unfold markedNumerator; ring
  rw [this]
  have := mul_nonneg hx h1
  have := mul_nonneg hy h2
  have := mul_nonneg hz h3
  linarith

/-- Each of the four weight triples satisfies the three triangle-like
inequalities used by `markedNumerator_nonneg`. -/
lemma markWeights_triangle_like (p : MarkPattern) :
    let w := markWeights p
    0 ≤ -w.1 + w.2.1 + w.2.2 ∧ 0 ≤ w.1 - w.2.1 + w.2.2 ∧
      0 ≤ w.1 + w.2.1 - w.2.2 := by
  cases p <;> simp [markWeights] <;> norm_num

/-- The marked numerator is nonnegative for every allowable color pattern. -/
lemma markedNumerator_nonneg_of_pattern (p : MarkPattern) (x y z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    let w := markWeights p
    0 ≤ markedNumerator w.1 w.2.1 w.2.2 x y z := by
  obtain ⟨h1, h2, h3⟩ := markWeights_triangle_like p
  exact markedNumerator_nonneg _ _ _ x y z hx hy hz h1 h2 h3

/-- The SOS identities, uniformly: for each pattern the difference
`N^2 - 4*heron16` is nonnegative. -/
lemma sq_markedNumerator_sub_heron_nonneg (p : MarkPattern) (x y z : ℝ) :
    let w := markWeights p
    0 ≤ markedNumerator w.1 w.2.1 w.2.2 x y z ^ 2 - 4 * heron16 x y z := by
  cases p
  · simp only [markWeights]
    rw [sos_allSame x y z]; positivity
  · simp only [markWeights]
    rw [sos_twoSameAdjacent x y z]; positivity
  · simp only [markWeights]
    rw [sos_twoSameOpposite x y z]; positivity
  · simp only [markWeights]
    rw [sos_allDistinct x y z]; positivity

/--
Algebraic form of the marked-triangle budget.

For a nondegenerate Euclidean triangle of area `K`, positive squared side
lengths `x,y,z`, and any allowable color pattern, the marked cotangent sum is
at least two.  Multiplying that conclusion by `4*K` gives this declaration.
-/
theorem markedTriangleBudget
    (p : MarkPattern) (x y z K : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hK : 0 < K)
    (hHeron : heron16 x y z = (4 * K) ^ 2) :
    let w := markWeights p
    8 * K ≤ markedNumerator w.1 w.2.1 w.2.2 x y z := by
  intro w
  have hsos : 0 ≤ markedNumerator w.1 w.2.1 w.2.2 x y z ^ 2 - 4 * heron16 x y z :=
    sq_markedNumerator_sub_heron_nonneg p x y z
  have hnn : 0 ≤ markedNumerator w.1 w.2.1 w.2.2 x y z :=
    markedNumerator_nonneg_of_pattern p x y z hx.le hy.le hz.le
  rw [hHeron] at hsos
  nlinarith [hsos, hnn, hK]

end Conjecture41
