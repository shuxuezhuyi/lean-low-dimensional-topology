/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Polygon.DiscPolygonJordan
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedLocalConvexity
/-! # Local and global convexity of finite-or-ideal polygon closures

The polygon interior is regular open in Klein coordinates. Its compactified
closure is convex exactly when the open polygon is convex. Local closed-model
convexity suffices globally because the polygon closure is closed and preconnected.
-/
set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Set
open scoped Complex.UnitDisc Topology
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- Finite Klein coordinates agree with the ambient Klein homeomorphism on the polygon interior. -/
theorem DiscPolygon.klein_image_interior {n : ℕ} (P : DiscPolygon n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior = _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' P.complexInterior := by
  rw [← P.interior_complex_image,Set.image_image]
  congr 1
  funext z
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph_closed
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)).symm

/-- The closed Klein polygon is the closure of its interior image. -/
theorem DiscPolygon.closedKlein_image_closedCarrier {n : ℕ} (P : DiscPolygon n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' P.closedCarrier = closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior) := by
  rw [DiscPolygon.closedCarrier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,
    ← _root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.closure_image_eq,image_image]
  rfl

/-- The finite Klein interior is the ambient interior of the compactified polygon image. -/
theorem DiscPolygon.interior_closedKlein_image {n : ℕ} (P : DiscPolygon n) :
    _root_.interior (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' P.closedCarrier) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior := by
  rw [P.closedKlein_image_closedCarrier,P.klein_image_interior,←
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.image_closure,
    ← _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.image_interior,P.interior_closure_complexInterior]

/-- The open polygon is convex exactly when its finite-or-ideal closure is convex. -/
theorem DiscPolygon.closedCarrier_hConvex_iff {n : ℕ} (P : DiscPolygon n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscHConvex P.closedCarrier ↔ P.IsConvex := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvex_iff_klein_convex,DiscPolygon.IsConvex,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex]
  constructor
  · intro hc
    rw [← P.interior_closedKlein_image]
    exact hc.interior
  · intro hc
    rw [P.closedKlein_image_closedCarrier]
    exact hc.closure

/-- Local convexity of the compactified polygon implies global convexity, including at ideal vertices. -/
theorem DiscPolygon.isConvex_iff_closedCarrier_locallyConvex {n : ℕ} (P : DiscPolygon n) :
    P.IsConvex ↔ _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsLocallyClosedDiscHConvex P.closedCarrier := by
  constructor
  · intro hc
    exact (P.closedCarrier_hConvex_iff.mpr hc).isLocallyClosedDiscHConvex
  · intro hl
    exact P.closedCarrier_hConvex_iff.mp
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvex_of_isClosed_isPreconnected_isLocallyConvex
        P.closedCarrier_isClosed
        P.closedCarrier_isPreconnected hl)

end
end LowDimensionalTopology.Geometry.Polygon
