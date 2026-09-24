import Conjecture41.QuotientEuler
import Conjecture41.TorusCertificate

set_option autoImplicit false

/-!
# The torus triangulation of a periodic configuration (gate G5f)

All the fields of `TorusTriangulation` are now available for the quotient of
the canonical fan triangulation of the periodization of a nonempty periodic
configuration:

* the faces are the `nF` representative fan triangles, positively oriented,
  with vertices in the periodization (`TorusQuotient.lean`);
* the dart pairing `pfQ` is a fixed-point-free involution matching the two
  copies of every edge along genuine period-lattice translations
  (`TorusQuotient.lean`);
* the weak Delaunay in-circle inequality and the invariance of the exclusion
  weight hold for every dart (`TorusQuotient.lean`);
* the Euler identity `nF = 2 · #points` (`QuotientEuler.lean`);
* the area identity `Σ area = L²` (`QuotientArea.lean`).

Assembling them closes the geometric realization stage of the project.
-/

namespace Conjecture41

namespace PeriodicConfig

variable (P : PeriodicConfig) (hne : P.points.Nonempty)

/-- **The torus triangulation of a nonempty periodic configuration.** -/
noncomputable def torusTriangulation : TorusTriangulation P.lift (P.side ^ 2) where
  nF := P.nF hne
  nV := P.points.card
  vert := P.vertQ hne
  vert_mem := P.vertQ_mem hne
  pos := P.cross_vertQ_pos hne
  pf := P.pfQ hne
  pf_invol := P.pfQ_pfQ hne
  pf_ne := P.pfQ_ne hne
  tr := P.trQ hne
  match_left := P.match_leftQ hne
  match_right := P.match_rightQ hne
  delaunay := P.delaunayQ hne
  weight_eq := P.weight_eqQ hne
  euler := P.euler_identity hne
  area := P.area_identity hne

@[simp] lemma torusTriangulation_nV : (P.torusTriangulation hne).nV = P.points.card := rfl

end PeriodicConfig

end Conjecture41
