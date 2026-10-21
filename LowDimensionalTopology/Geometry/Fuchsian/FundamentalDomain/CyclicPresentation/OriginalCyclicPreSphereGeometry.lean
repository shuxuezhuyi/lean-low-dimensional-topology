/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicPreGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FiniteAreaCuspCompactness
/-!
# The stored face in sphere coordinates

The normalized closed disc-model polygon and its original sphere hull have
the same subspace topology. Composing this identification with the face map
preserves the original boundary subdivision.
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
open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- The literal compact model closure and its original normalized sphere image have exactly the same subspace topology. -/
def originalPolygonClosedModelSphereHomeomorph
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H) (D:Set
      P.domain.carrier)
    (q₀:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) {n:ℕ} (S:_root_.LowDimensionalTopology.Geometry.Polygon.CyclicDiscPolygonSupportData n)
    (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P D) :
    ↥(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))≃ₜ↥(originalFiniteClosedHull q₀ S.vertices) := by
  let E:= (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
    q₀⁻¹).isEmbedding.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_closedDiscToExtended
  have hi : (fun p:𝕔𝔻=>q₀⁻¹.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p)) ''
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D)=originalFiniteClosedHull q₀ S.vertices := by
    rw [originalFiniteClosedHull,finite_cyclic_hull_eq_polygon_closedModel P D S hr]
  exact (E.homeomorphImage _).trans (Homeomorph.setCongr hi)

theorem originalPolygonClosedModelSphereHomeomorph_coe
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H) (D:Set
      P.domain.carrier)
    (q₀:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) {n:ℕ} (S:_root_.LowDimensionalTopology.Geometry.Polygon.CyclicDiscPolygonSupportData n)
    (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P D)
    (x:↥(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))) :
    (originalPolygonClosedModelSphereHomeomorph P D q₀ S hr x).val=
      q₀⁻¹.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended x.val) := rfl

/-- The actual stored original word face maps homeomorphically onto its literal original sphere hull, retaining every unchanged boundary subdivision. -/
def originalCyclicPreSphereHomeomorph
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (q₀:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) {n:ℕ} (S:_root_.LowDimensionalTopology.Geometry.Polygon.CyclicDiscPolygonSupportData n)
    (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P D) :
    (originalCyclicPresentation J e).presentation.PolygonalPreRealization≃ₜ
      ↥(originalFiniteClosedHull q₀ S.vertices) :=
  (originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs).trans
    (originalPolygonClosedModelSphereHomeomorph P D q₀ S hr)
end LowDimensionalTopology.Geometry.Fuchsian
