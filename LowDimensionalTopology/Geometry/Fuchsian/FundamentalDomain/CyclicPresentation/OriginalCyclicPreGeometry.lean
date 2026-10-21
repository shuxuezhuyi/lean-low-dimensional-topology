/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicOccurrenceGeometry
/-!
# Geometry of the stored polygon face

The stored face is homeomorphic to the original compact Klein polygon and
closed disc-model closure. These maps preserve occurrence parameters, so each
word-gluing generator is the actual original side transformation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- Unpacking the actual stored original face preserves the exact circular side marking at every parameter. -/
theorem originalCyclicPreFaceHomeomorph_side
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD)
    (o:(originalCyclicPresentation J e).presentation.BoundaryOccurrence) (t:unitInterval) :
    originalCyclicPreFaceHomeomorph J e
      (((originalCyclicPresentation J e).presentation.occurrenceSide o).point t)=
      PolygonCell.side (originalCyclicOccurrenceIndex J e o) t := by
  apply PolygonCell.ext
  change (Circle.exp (PolygonCell.sideAngle o.2 t):ℂ)=
    (Circle.exp (PolygonCell.sideAngle (originalCyclicOccurrenceIndex J e o) t):ℂ)
  simp only [PolygonCell.sideAngle,originalCyclicOccurrenceIndex_val,originalCyclicFaceBoundary_length]

/-- The literal stored original face, not a substitute cell with a new pairing predicate, maps homeomorphically onto the unchanged actual compact Klein polygon. -/
def originalCyclicPreKleinHomeomorph
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier) :
    (originalCyclicPresentation J e).presentation.PolygonalPreRealization≃ₜ
      ↥(fuchsianPolygonCompactKlein P D) :=
  (originalCyclicPreFaceHomeomorph J e).trans (originalCyclicFaceHomeomorph hD ha J hc hv e hs)

/-- Each genuine stored occurrence has exactly its corresponding actual Mobius-compatible geometric parameter. -/
theorem originalCyclicPreKleinHomeomorph_side
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (o:(originalCyclicPresentation J e).presentation.BoundaryOccurrence) (t:unitInterval) :
    (originalCyclicPreKleinHomeomorph hD ha J hc hv e hs
      (((originalCyclicPresentation J e).presentation.occurrenceSide o).point t):ℂ)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (originalCyclicSideParam hD J hv e (originalCyclicOccurrenceIndex J e o) t) := by
  change (originalCyclicFaceHomeomorph hD ha J hc hv e hs
    (originalCyclicPreFaceHomeomorph J e
      (((originalCyclicPresentation J e).presentation.occurrenceSide o).point t)):ℂ)=_
  rw [originalCyclicPreFaceHomeomorph_side,originalCyclicFaceHomeomorph_side]
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- The unchanged actual compact model closure has precisely the original compact Klein coordinates and subspace topology. -/
def originalPolygonClosedModelKleinHomeomorph
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H) (D:Set
      P.domain.carrier) :
    ↥(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))≃ₜ↥(fuchsianPolygonCompactKlein P D) := by
  have hi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D)=
      fuchsianPolygonCompactKlein P D := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_discClosedModelClosure,image_image]
    rfl
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.isEmbedding.homeomorphImage _).trans
    (Homeomorph.setCongr hi)

theorem originalPolygonClosedModelKleinHomeomorph_symm_coe
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H) (D:Set
      P.domain.carrier)
    (x:↥(fuchsianPolygonCompactKlein P D)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ((originalPolygonClosedModelKleinHomeomorph P D).symm x).val=x.val := by
  change ((originalPolygonClosedModelKleinHomeomorph P D)
    ((originalPolygonClosedModelKleinHomeomorph P D).symm x)).val=x.val
  exact congrArg Subtype.val ((originalPolygonClosedModelKleinHomeomorph P D).apply_symm_apply x)

/-- The actual stored word face maps homeomorphically to the actual compactified original model closure. -/
def originalCyclicPreClosedModelHomeomorph
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier) :
    (originalCyclicPresentation J e).presentation.PolygonalPreRealization≃ₜ
      ↥(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D)) :=
  (originalCyclicPreKleinHomeomorph hD ha J hc hv e hs).trans
    (originalPolygonClosedModelKleinHomeomorph P D).symm

theorem originalCyclicPreClosedModelHomeomorph_side
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (o:(originalCyclicPresentation J e).presentation.BoundaryOccurrence) (t:unitInterval) :
    (originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs
      (((originalCyclicPresentation J e).presentation.occurrenceSide o).point t)).val=
      originalCyclicSideParam hD J hv e (originalCyclicOccurrenceIndex J e o) t := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ((originalPolygonClosedModelKleinHomeomorph P D).symm
    (originalCyclicPreKleinHomeomorph hD ha J hc hv e hs
      (((originalCyclicPresentation J e).presentation.occurrenceSide o).point t))).val=_
  rw [originalPolygonClosedModelKleinHomeomorph_symm_coe,originalCyclicPreKleinHomeomorph_side]

/-- Every generator of the actual stored word gluing relation is exactly a genuine original side transformation on the entire finite-or-ideal closed side. -/
theorem originalCyclicBoundaryPairing_geometric
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (pairing:(originalCyclicPresentation J e).presentation.BoundaryPairing) (t:unitInterval) :
    originalCyclicEdgeAction J e (originalCyclicOccurrenceIndex J e pairing.source)
      (originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs
        (pairing.identification.source.point t)).val=
      (originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs
        (pairing.identification.target.point (pairing.identification.parameter t))).val := by
  change originalCyclicEdgeAction J e (originalCyclicOccurrenceIndex J e pairing.source)
    (originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs
      (((originalCyclicPresentation J e).presentation.occurrenceSide pairing.source).point t)).val=
    (originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs
      (((originalCyclicPresentation J e).presentation.occurrenceSide pairing.target).point
        (pairing.identification.parameter t))).val
  rw [originalCyclicPreClosedModelHomeomorph_side,originalCyclicPreClosedModelHomeomorph_side]
  have hp : pairing.identification.parameter t=unitInterval.symm t := by
    change pairing.direction.homeomorph t=_
    rw [originalCyclicBoundaryPairing_direction J e pairing]
    rfl
  rw [hp,originalCyclicBoundaryPairing_target_index]
  exact originalCyclicSideParam_pair hD J hv e _ t
end LowDimensionalTopology.Geometry.Fuchsian
