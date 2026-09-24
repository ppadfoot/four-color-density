import Conjecture41.LocalGeometry
import Conjecture41.PlaneUtil

set_option autoImplicit false

/-!
# Gates G2 and G4: cotangent area and the paired Delaunay weight

This file develops, in purely algebraic (coordinate) form, the two facts about
planar triangles that the periodic weak-Delaunay argument needs.

* `four_area_eq_cot_weighted_sum`:
  `4K = x·cot A + y·cot B + z·cot C` for a nondegenerate triangle with squared
  side lengths `x, y, z` opposite the angles `A, B, C` and area `K`.
* `cotOpp_add_cotOpp_nonneg`:
  for an interior edge of a *weak Delaunay* triangulation, that is, for two
  triangles `abc` and `dcb` sharing the edge `bc` with `d` not strictly inside
  the circumcircle of `abc`, the *paired* cotangent `cot α + cot β` is
  nonnegative.  Individual cotangents may well be negative; only the pair is
  controlled.  The link with the circumcircle is `inCircleDet_eq_cross_mul`,
  and `inCircleDet_eq_half` is the algebraic identity that turns the empty
  circumcircle condition into the sign of `N₁ S₂ + N₂ S₁`.

Everything here is stated with the signed area `cross` (twice the signed area),
so that no case distinction on the shape of the triangle is required; the
cotangent of the angle at `a` in the triangle `a b c` is
`cotOpp a b c = (|ac|² + |ab|² - |bc|²) / (2 · cross a b c)`, which is the
classical `cos/sin` because `2 K = cross` and `|ac| |ab| cos A = (|ac|² + |ab|²
- |bc|²)/2`.
-/

namespace Conjecture41

open Metric

/-- Twice the signed area of the triangle `a b c`. -/
def cross (a b c : Plane) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

/-- The squared distance in coordinates. -/
lemma dist_sq_coords (a b : Plane) : dist a b ^ 2 = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

lemma cross_cyclic (a b c : Plane) : cross a b c = cross b c a := by
  unfold cross; ring

lemma cross_swap (a b c : Plane) : cross a b c = -cross a c b := by
  unfold cross; ring

/-- Heron's identity: sixteen times the squared area equals `heron16` of the
squared side lengths. -/
lemma heron16_eq_cross_sq (a b c : Plane) :
    heron16 (dist b c ^ 2) (dist a c ^ 2) (dist a b ^ 2) = 4 * cross a b c ^ 2 := by
  simp only [heron16, dist_sq_coords, cross]
  ring

/--
The cotangent of the angle of the triangle `a b c` at the vertex `a`, written
with the signed area.  For a positively oriented triangle this is
`cos A / sin A`.
-/
noncomputable def cotOpp (a b c : Plane) : ℝ :=
  (dist a c ^ 2 + dist a b ^ 2 - dist b c ^ 2) / (2 * cross a b c)

/--
The cotangent area identity `4 K = x cot A + y cot B + z cot C`, in the signed
form `2 · cross = x cot A + y cot B + z cot C` (note `cross = 2 K`).
-/
theorem four_area_eq_cot_weighted_sum {a b c : Plane} (h : cross a b c ≠ 0) :
    dist b c ^ 2 * cotOpp a b c + dist a c ^ 2 * cotOpp b c a
      + dist a b ^ 2 * cotOpp c a b = 2 * cross a b c := by
  have hbc : cross b c a = cross a b c := (cross_cyclic a b c).symm
  have hca : cross c a b = cross a b c := by rw [cross_cyclic a b c, cross_cyclic b c a]
  unfold cotOpp
  rw [hbc, hca]
  field_simp
  simp only [dist_comm]
  simp only [dist_sq_coords, cross]
  ring

/--
The in-circle determinant of the four points `a b c d`.  For a positively
oriented triangle `a b c` it is nonnegative exactly when `d` lies outside or on
the circumcircle of `a b c`; see `inCircleDet_eq_cross_mul`.
-/
def inCircleDet (a b c d : Plane) : ℝ :=
  (b 0 - a 0) *
      ((c 1 - a 1) * ((d 0 - a 0) ^ 2 + (d 1 - a 1) ^ 2)
        - ((c 0 - a 0) ^ 2 + (c 1 - a 1) ^ 2) * (d 1 - a 1))
    - (b 1 - a 1) *
      ((c 0 - a 0) * ((d 0 - a 0) ^ 2 + (d 1 - a 1) ^ 2)
        - ((c 0 - a 0) ^ 2 + (c 1 - a 1) ^ 2) * (d 0 - a 0))
    + ((b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2) *
      ((c 0 - a 0) * (d 1 - a 1) - (c 1 - a 1) * (d 0 - a 0))

/--
Geometric meaning of the in-circle determinant: if `o` is the circumcenter of
`a b c`, then `inCircleDet a b c d = cross a b c * (|d - o|² - R²)`.  So for a
positively oriented triangle, the determinant is nonnegative exactly when `d`
is outside or on the circumcircle.
-/
theorem inCircleDet_eq_cross_mul (a b c d o : Plane)
    (hb : dist a o = dist b o) (hc : dist a o = dist c o) :
    inCircleDet a b c d = cross a b c * (dist d o ^ 2 - dist a o ^ 2) := by
  have hb' : dist a o ^ 2 = dist b o ^ 2 := by rw [hb]
  have hc' : dist a o ^ 2 = dist c o ^ 2 := by rw [hc]
  rw [dist_sq_coords, dist_sq_coords] at hb' hc'
  simp only [inCircleDet, cross, dist_sq_coords]
  linear_combination
    (-((c 0 - a 0) * (d 1 - a 1) - (c 1 - a 1) * (d 0 - a 0))) * hb'
      + ((b 0 - a 0) * (d 1 - a 1) - (b 1 - a 1) * (d 0 - a 0)) * hc'

/--
The key algebraic identity of gate G4: the in-circle determinant equals
`(N₁ S₂ + N₂ S₁)/2`, where `N₁, N₂` are the cotangent numerators at the two
apexes `a` and `d` of the triangles sharing the edge `b c`, and `S₁, S₂` are
the corresponding doubled signed areas.
-/
theorem inCircleDet_eq_half (a b c d : Plane) :
    inCircleDet a b c d =
      (1 / 2) * ((dist a c ^ 2 + dist a b ^ 2 - dist b c ^ 2) * cross d c b
        + (dist d b ^ 2 + dist d c ^ 2 - dist b c ^ 2) * cross a b c) := by
  simp only [inCircleDet, cross, dist_sq_coords]
  ring

/--
Nonnegativity of the *paired* cotangent weight of a weak Delaunay edge.  If the
triangles `a b c` and `d c b` are positively oriented (so they lie on opposite
sides of the shared edge `b c`) and `d` is not strictly inside the circumcircle
of `a b c`, then `cot α + cot β ≥ 0`, where `α` is the angle at `a` and `β` the
angle at `d`.

No claim is made about the individual cotangents: either one may be negative.
-/
theorem cotOpp_add_cotOpp_nonneg {a b c d : Plane}
    (h1 : 0 < cross a b c) (h2 : 0 < cross d c b)
    (hDel : 0 ≤ inCircleDet a b c d) :
    0 ≤ cotOpp a b c + cotOpp d c b := by
  have hid := inCircleDet_eq_half a b c d
  unfold cotOpp
  rw [div_add_div _ _ (by positivity) (by positivity)]
  apply div_nonneg _ (by positivity)
  rw [dist_comm c b]
  nlinarith [hid, hDel]

/--
The consequence used in the global sum: for a weak Delaunay interior edge with
squared length `ℓ² ≥ w` and paired cotangent weight `cot α + cot β ≥ 0`, the
edge contribution decreases when the squared length is replaced by the
exclusion weight.
-/
theorem edge_weight_le {a b c d : Plane} {w : ℝ}
    (h1 : 0 < cross a b c) (h2 : 0 < cross d c b)
    (hDel : 0 ≤ inCircleDet a b c d)
    (hw : w ≤ dist b c ^ 2) :
    w * (cotOpp a b c + cotOpp d c b)
      ≤ dist b c ^ 2 * (cotOpp a b c + cotOpp d c b) :=
  mul_le_mul_of_nonneg_right hw (cotOpp_add_cotOpp_nonneg h1 h2 hDel)

end Conjecture41
