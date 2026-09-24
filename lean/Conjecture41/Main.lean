import Conjecture41.Definitions
import Conjecture41.LocalGeometry
import Conjecture41.Voronoi
import Conjecture41.Delone
import Conjecture41.VoronoiPolygon
import Conjecture41.DelaunayCell
import Conjecture41.DelaunayTiling
import Conjecture41.VoronoiVertex
import Conjecture41.PeriodicDelaunay
import Conjecture41.TriangleArea
import Conjecture41.AreaAdditivity
import Conjecture41.InscribedOrientation
import Conjecture41.Barycentric
import Conjecture41.Fan
import Conjecture41.CocircularFan
import Conjecture41.DelaunayFan
import Conjecture41.DelaunayGrow
import Conjecture41.CanonicalFan
import Conjecture41.TriangleInterior
import Conjecture41.GlobalTriangulation
import Conjecture41.LocalFiniteness
import Conjecture41.EdgeGrowth
import Conjecture41.EdgeNeighbour
import Conjecture41.EdgeToEdge
import Conjecture41.Fundamental
import Conjecture41.Darts
import Conjecture41.TorusQuotient
import Conjecture41.QuotientArea
import Conjecture41.Rotation
import Conjecture41.Sector
import Conjecture41.Angle
import Conjecture41.TriangleCorner
import Conjecture41.VertexAngle
import Conjecture41.VertexSum
import Conjecture41.QuotientEuler
import Conjecture41.PeriodicCertificate
import Conjecture41.Limsup
import Conjecture41.AuthoritativeProof
import Conjecture41.PlaneUtil
import Conjecture41.Cotangent
import Conjecture41.ColoredTriangle
import Conjecture41.GlobalSum
import Conjecture41.Periodic
import Conjecture41.PeriodicLift
import Conjecture41.TorusCertificate
import Conjecture41.Periodization
import Conjecture41.PeriodicProof

set_option autoImplicit false

namespace Conjecture41

/--
Cohn--Rajagopal Conjecture 4.1 for every valid four-colored configuration.

This is the exact unrestricted epsilon/eventual statement: no periodicity,
saturation, triangulation, local finiteness, or geometric certificate is
assumed.  It is derived from the periodic density theorem by the buffered
periodization argument (`conjecture_4_1_of_periodic`).
-/
theorem conjecture_4_1 (C : FourColorConfig) :
    UpperRadialDensityAtMostOne C :=
  conjecture_4_1_of_periodic periodic_density C

/-- The literal limsup version of Conjecture 4.1. -/
theorem conjecture_4_1_limsup (C : FourColorConfig) :
    LimsupDensityAtMostOne C :=
  (upperRadialDensity_iff_limsup C).mp (conjecture_4_1 C)

#print axioms conjecture_4_1
#print axioms conjecture_4_1_limsup

end Conjecture41
