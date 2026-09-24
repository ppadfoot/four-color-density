import Conjecture41.Cotangent

set_option autoImplicit false

/-!
# The marked budget for an arbitrary colored triangle (gate G3)

`LocalGeometry.lean` proves the marked triangle budget for the four *ordered*
weight patterns.  Here we remove the ordering convention: for **any** three
colors `i, j, k` the weight triple

```
(exclusionSq j k, exclusionSq i k, exclusionSq i j)
```

(the weight of the edge opposite each vertex) is a permutation of one of the
four patterns, and the marked budget holds.  The final statement,
`cot_marked_budget`, is the per-face inequality used by the global sum:

```
2 ≤ w_a cot A + w_b cot B + w_c cot C
```

for every nondegenerate triangle whose vertices carry any colors whatsoever.
-/

namespace Conjecture41

/-! ### The ten possible weight triples -/

/-- The possible triples of exclusion weights of a colored triangle: the four
patterns of `markWeights`, in all their distinct orderings. -/
def WeightTriple (wa wb wc : ℝ) : Prop :=
  (wa = 2 ∧ wb = 2 ∧ wc = 2) ∨
  (wa = 2 ∧ wb = 5 / 4 ∧ wc = 5 / 4) ∨
  (wa = 5 / 4 ∧ wb = 2 ∧ wc = 5 / 4) ∨
  (wa = 5 / 4 ∧ wb = 5 / 4 ∧ wc = 2) ∨
  (wa = 2 ∧ wb = 1 ∧ wc = 1) ∨
  (wa = 1 ∧ wb = 2 ∧ wc = 1) ∨
  (wa = 1 ∧ wb = 1 ∧ wc = 2) ∨
  (wa = 5 / 4 ∧ wb = 5 / 4 ∧ wc = 1) ∨
  (wa = 5 / 4 ∧ wb = 1 ∧ wc = 5 / 4) ∨
  (wa = 1 ∧ wb = 5 / 4 ∧ wc = 5 / 4)

lemma exclusionSq_self (i : Color) : exclusionSq i i = 2 := by
  simp [exclusionSq]

lemma exclusionSq_opp {i j : Color} (h : j = i + 2) : exclusionSq i j = 1 := by
  have hne : i ≠ j := by
    subst h
    revert i
    decide
  rw [exclusionSq, if_neg hne, if_pos h]

lemma exclusionSq_adj {i j : Color} (h1 : i ≠ j) (h2 : j ≠ i + 2) : exclusionSq i j = 5 / 4 := by
  rw [exclusionSq, if_neg h1, if_neg h2]

/-- Among three distinct colors exactly one pair is opposite. -/
lemma color_distinct_cases (i j k : Color) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (j = i + 2 ∧ k ≠ i + 2 ∧ k ≠ j + 2) ∨
    (k = i + 2 ∧ j ≠ i + 2 ∧ k ≠ j + 2) ∨
    (k = j + 2 ∧ j ≠ i + 2 ∧ k ≠ i + 2) := by
  revert hij hik hjk
  revert i j k
  decide

/-- The exclusion weight triple of any colored triangle is one of the ten
listed triples. -/
theorem weightTriple_exclusionSq (i j k : Color) :
    WeightTriple (exclusionSq j k) (exclusionSq i k) (exclusionSq i j) := by
  by_cases hij : i = j
  · subst hij
    by_cases hik : i = k
    · subst hik
      simp only [WeightTriple, exclusionSq_self]
      norm_num
    · by_cases hopp : k = i + 2
      · simp only [WeightTriple, exclusionSq_self, exclusionSq_opp hopp]
        norm_num
      · simp only [WeightTriple, exclusionSq_self, exclusionSq_adj hik hopp]
        norm_num
  · by_cases hik : i = k
    · subst hik
      by_cases hopp : j = i + 2
      · have hji : exclusionSq j i = 1 := by
          rw [exclusionSq_comm]; exact exclusionSq_opp hopp
        simp only [WeightTriple, exclusionSq_self, exclusionSq_opp hopp, hji]
        norm_num
      · have hji : exclusionSq j i = 5 / 4 := by
          rw [exclusionSq_comm]; exact exclusionSq_adj hij hopp
        simp only [WeightTriple, exclusionSq_self, exclusionSq_adj hij hopp, hji]
        norm_num
    · by_cases hjk : j = k
      · subst hjk
        by_cases hopp : j = i + 2
        · simp only [WeightTriple, exclusionSq_self, exclusionSq_opp hopp]
          norm_num
        · simp only [WeightTriple, exclusionSq_self, exclusionSq_adj hij hopp]
          norm_num
      · rcases color_distinct_cases i j k hij hik hjk with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · simp only [WeightTriple, exclusionSq_adj hjk h3, exclusionSq_adj hik h2,
            exclusionSq_opp h1]
          norm_num
        · simp only [WeightTriple, exclusionSq_adj hjk h3, exclusionSq_opp h1,
            exclusionSq_adj hij h2]
          norm_num
        · simp only [WeightTriple, exclusionSq_opp h1, exclusionSq_adj hik h3,
            exclusionSq_adj hij h2]
          norm_num

/-! ### The sum-of-squares bound for all ten triples -/

/-- The SOS bound `4 · heron16 ≤ N²` for every admissible weight triple. -/
theorem four_heron_le_sq_markedNumerator {wa wb wc : ℝ} (h : WeightTriple wa wb wc) (x y z : ℝ) :
    4 * heron16 x y z ≤ markedNumerator wa wb wc x y z ^ 2 := by
  have key : ∀ e : ℝ, 0 ≤ e → 4 * heron16 x y z + e ≤ markedNumerator wa wb wc x y z ^ 2 →
      4 * heron16 x y z ≤ markedNumerator wa wb wc x y z ^ 2 := by
    intro e he h'; linarith
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  · have e : markedNumerator 2 2 2 x y z ^ 2 - 4 * heron16 x y z
        = 8 * (x ^ 2 + y ^ 2 + z ^ 2) := by unfold markedNumerator heron16; ring
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  · have e : markedNumerator 2 (5 / 4) (5 / 4) x y z ^ 2 - 4 * heron16 x y z
        = 4 * (y + z - 3 * x / 4) ^ 2 + 2 * x ^ 2 + 4 * (y - z) ^ 2 := by
      unfold markedNumerator heron16; ring
    nlinarith [sq_nonneg (y + z - 3 * x / 4), sq_nonneg x, sq_nonneg (y - z)]
  · have e : markedNumerator (5 / 4) 2 (5 / 4) x y z ^ 2 - 4 * heron16 x y z
        = 4 * (x + z - 3 * y / 4) ^ 2 + 2 * y ^ 2 + 4 * (x - z) ^ 2 := by
      unfold markedNumerator heron16; ring
    nlinarith [sq_nonneg (x + z - 3 * y / 4), sq_nonneg y, sq_nonneg (x - z)]
  · have e : markedNumerator (5 / 4) (5 / 4) 2 x y z ^ 2 - 4 * heron16 x y z
        = 4 * (x + y - 3 * z / 4) ^ 2 + 2 * z ^ 2 + 4 * (x - y) ^ 2 := by
      unfold markedNumerator heron16; ring
    nlinarith [sq_nonneg (x + y - 3 * z / 4), sq_nonneg z, sq_nonneg (x - y)]
  · have e : markedNumerator 2 1 1 x y z ^ 2 - 4 * heron16 x y z
        = 4 * (x - y - z) ^ 2 + 4 * (y - z) ^ 2 := by unfold markedNumerator heron16; ring
    nlinarith [sq_nonneg (x - y - z), sq_nonneg (y - z)]
  · have e : markedNumerator 1 2 1 x y z ^ 2 - 4 * heron16 x y z
        = 4 * (y - x - z) ^ 2 + 4 * (x - z) ^ 2 := by unfold markedNumerator heron16; ring
    nlinarith [sq_nonneg (y - x - z), sq_nonneg (x - z)]
  · have e : markedNumerator 1 1 2 x y z ^ 2 - 4 * heron16 x y z
        = 4 * (z - x - y) ^ 2 + 4 * (x - y) ^ 2 := by unfold markedNumerator heron16; ring
    nlinarith [sq_nonneg (z - x - y), sq_nonneg (x - y)]
  · have e : markedNumerator (5 / 4) (5 / 4) 1 x y z ^ 2 - 4 * heron16 x y z
        = (x + y - 5 * z / 2) ^ 2 + 4 * (x - y) ^ 2 := by unfold markedNumerator heron16; ring
    nlinarith [sq_nonneg (x + y - 5 * z / 2), sq_nonneg (x - y)]
  · have e : markedNumerator (5 / 4) 1 (5 / 4) x y z ^ 2 - 4 * heron16 x y z
        = (x + z - 5 * y / 2) ^ 2 + 4 * (x - z) ^ 2 := by unfold markedNumerator heron16; ring
    nlinarith [sq_nonneg (x + z - 5 * y / 2), sq_nonneg (x - z)]
  · have e : markedNumerator 1 (5 / 4) (5 / 4) x y z ^ 2 - 4 * heron16 x y z
        = (y + z - 5 * x / 2) ^ 2 + 4 * (y - z) ^ 2 := by unfold markedNumerator heron16; ring
    nlinarith [sq_nonneg (y + z - 5 * x / 2), sq_nonneg (y - z)]

/-! ### The marked budget for an arbitrary colored triangle -/

/--
The marked triangle budget for arbitrary colors: no ordering convention on the
color pattern is needed.
-/
theorem colored_triangle_budget (i j k : Color) (x y z K : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hK : 0 < K)
    (hHeron : heron16 x y z = (4 * K) ^ 2) :
    8 * K ≤ markedNumerator (exclusionSq j k) (exclusionSq i k) (exclusionSq i j) x y z := by
  have hsos := four_heron_le_sq_markedNumerator (weightTriple_exclusionSq i j k) x y z
  have hnn : 0 ≤ markedNumerator (exclusionSq j k) (exclusionSq i k) (exclusionSq i j) x y z := by
    refine markedNumerator_nonneg _ _ _ x y z hx.le hy.le hz.le ?_ ?_ ?_ <;>
      [skip; skip; skip] <;>
      · have h1 := one_le_exclusionSq j k
        have h2 := one_le_exclusionSq i k
        have h3 := one_le_exclusionSq i j
        have h4 := exclusionSq_le_two j k
        have h5 := exclusionSq_le_two i k
        have h6 := exclusionSq_le_two i j
        linarith
  rw [hHeron] at hsos
  nlinarith [hsos, hnn, hK]

/-! ### Per-face form used in the global sum -/

/-- A degenerate triangle has vanishing signed area. -/
lemma cross_eq_zero_of_eq_left (a c : Plane) : cross a a c = 0 := by unfold cross; ring

lemma cross_eq_zero_of_eq_right (a b : Plane) : cross a b a = 0 := by unfold cross; ring

lemma cross_eq_zero_of_eq_last (a b : Plane) : cross a b b = 0 := by unfold cross; ring

/--
The per-face marked budget in cotangent form.  For any nondegenerate,
positively oriented triangle `a b c` with arbitrary colors,

```
2 ≤ w_bc · cot A + w_ac · cot B + w_ab · cot C .
```

This is the inequality that the global sum applies face by face.
-/
theorem cot_marked_budget (col : Plane → Color) {a b c : Plane} (h : 0 < cross a b c) :
    2 ≤ exclusionSq (col b) (col c) * cotOpp a b c
      + exclusionSq (col a) (col c) * cotOpp b c a
      + exclusionSq (col a) (col b) * cotOpp c a b := by
  -- nondegeneracy gives positive squared side lengths
  have hab : a ≠ b := by rintro rfl; rw [cross_eq_zero_of_eq_left] at h; exact lt_irrefl 0 h
  have hac : a ≠ c := by rintro rfl; rw [cross_eq_zero_of_eq_right] at h; exact lt_irrefl 0 h
  have hbc : b ≠ c := by rintro rfl; rw [cross_eq_zero_of_eq_last] at h; exact lt_irrefl 0 h
  have hxpos : (0 : ℝ) < dist b c ^ 2 := pow_pos (dist_pos.mpr hbc) 2
  have hypos : (0 : ℝ) < dist a c ^ 2 := pow_pos (dist_pos.mpr hac) 2
  have hzpos : (0 : ℝ) < dist a b ^ 2 := pow_pos (dist_pos.mpr hab) 2
  have hheron : heron16 (dist b c ^ 2) (dist a c ^ 2) (dist a b ^ 2)
      = (4 * (cross a b c / 2)) ^ 2 := by
    rw [heron16_eq_cross_sq a b c]; ring
  have hbud := colored_triangle_budget (col a) (col b) (col c)
    (dist b c ^ 2) (dist a c ^ 2) (dist a b ^ 2) (cross a b c / 2)
    hxpos hypos hzpos (by linarith) hheron
  rw [markedNumerator] at hbud
  -- rewrite the three cotangents over the common denominator `2 S`
  have hcyc1 : cross b c a = cross a b c := (cross_cyclic a b c).symm
  have hcyc2 : cross c a b = cross a b c := by
    rw [cross_cyclic c a b, cross_cyclic a b c]
  have e1 : cotOpp a b c
      = (dist a c ^ 2 + dist a b ^ 2 - dist b c ^ 2) / (2 * cross a b c) := rfl
  have e2 : cotOpp b c a
      = (dist a b ^ 2 + dist b c ^ 2 - dist a c ^ 2) / (2 * cross a b c) := by
    simp only [cotOpp, hcyc1]
    rw [dist_comm b a, dist_comm c a]
  have e3 : cotOpp c a b
      = (dist b c ^ 2 + dist a c ^ 2 - dist a b ^ 2) / (2 * cross a b c) := by
    simp only [cotOpp, hcyc2]
    rw [dist_comm c a, dist_comm c b]
  rw [e1, e2, e3]
  have expand : exclusionSq (col b) (col c)
        * ((dist a c ^ 2 + dist a b ^ 2 - dist b c ^ 2) / (2 * cross a b c))
      + exclusionSq (col a) (col c)
        * ((dist a b ^ 2 + dist b c ^ 2 - dist a c ^ 2) / (2 * cross a b c))
      + exclusionSq (col a) (col b)
        * ((dist b c ^ 2 + dist a c ^ 2 - dist a b ^ 2) / (2 * cross a b c))
      = (exclusionSq (col b) (col c) * (dist a c ^ 2 + dist a b ^ 2 - dist b c ^ 2)
          + exclusionSq (col a) (col c) * (dist a b ^ 2 + dist b c ^ 2 - dist a c ^ 2)
          + exclusionSq (col a) (col b) * (dist b c ^ 2 + dist a c ^ 2 - dist a b ^ 2))
        / (2 * cross a b c) := by
    field_simp
  rw [expand, le_div_iff₀ (by linarith)]
  linarith [hbud]

end Conjecture41
