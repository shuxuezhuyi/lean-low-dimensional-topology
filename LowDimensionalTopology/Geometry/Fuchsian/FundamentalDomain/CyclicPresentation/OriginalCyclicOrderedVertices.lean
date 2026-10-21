/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicEdges
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Refinement.OriginalSideOrientation
/-!
# Ordered vertices and the original side involution

The cyclic vertices enumerate exactly the refined endpoints. Consecutive
vertices bound the corresponding whole side, and the transported side
involution reverses their endpoints under the actual group action.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Topology
open scoped Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- The unique actual closed-disc point at a real cyclic boundary vertex. -/
def originalCyclicVertex {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hvertices:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (i:ZMod J.n) : 𝕔𝔻:=Classical.choose ((hvertices (J.vertex i)).mp ⟨i,rfl⟩)

theorem originalCyclicVertex_mem_endpointSet {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hvertices:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (i:ZMod J.n) : originalCyclicVertex hD J hvertices i∈originalRefinedEndpointSet hD:=
  (Classical.choose_spec ((hvertices (J.vertex i)).mp ⟨i,rfl⟩)).1

/-- The actual selected point has exactly the original planar vertex as its coordinate. -/
theorem originalCyclicVertex_plane {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hvertices:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (i:ZMod J.n) : _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane (originalCyclicVertex hD J
      hvertices i)=J.vertex i:=
  (Classical.choose_spec ((hvertices (J.vertex i)).mp ⟨i,rfl⟩)).2

theorem originalCyclicVertex_injective {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hvertices:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD) :
    Function.Injective (originalCyclicVertex hD J hvertices) := by
  intro i j hij
  apply J.vertex_injective
  rw [←originalCyclicVertex_plane hD J hvertices i,←originalCyclicVertex_plane hD J hvertices j]
  exact congrArg _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane hij

/-- Actual cyclic vertices enumerate exactly the genuine original refined endpoint set. -/
theorem range_originalCyclicVertex {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hvertices:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD) :
    range (originalCyclicVertex hD J hvertices)=originalRefinedEndpointSet hD := by
  apply subset_antisymm
  · rintro x ⟨i,rfl⟩
    exact originalCyclicVertex_mem_endpointSet hD J hvertices i
  · intro x hx
    obtain ⟨i,hi⟩:=(hvertices (_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane x)).mpr ⟨x,hx,rfl⟩
    exact ⟨i,_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane_injective ((originalCyclicVertex_plane
      hD J hvertices i).trans hi)⟩

/-- The real Klein-plane image of any genuine finite-or-ideal geodesic segment. -/
theorem original_discPolygonKleinPlane_image_segment (a b:𝕔𝔻) :
    _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a b=
      segment ℝ (_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane a) (_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane b) := by
  let e:=PolygonalCircle.planeComplexEquiv.symm
  calc
    _=e '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a b):=by rw [image_image];rfl
    _=e '' segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate b):=by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    _=_:=image_segment ℝ e.toLinearEquiv.toAffineEquiv.toAffineMap _ _

/-- Consecutive actual ordered vertices bound precisely the corresponding entire original refined side. -/
theorem originalCyclicVertex_side_segment {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hvertices:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hspec:∀i,J.edgeSegment i=(e i).planeCarrier) (i:ZMod J.n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (originalCyclicVertex hD J hvertices i)
      (originalCyclicVertex hD J hvertices (i+1))=(e i).carrier := by
  apply _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane_injective.image_injective
  rw [original_discPolygonKleinPlane_image_segment,originalCyclicVertex_plane,originalCyclicVertex_plane]
  exact hspec i

/-- Literal original refined pairing transported to the actual cyclic edge indices. -/
def originalCyclicPairIndex {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) (i:ZMod J.n) : ZMod J.n:=e.symm (e i).pair

theorem originalCyclicPairIndex_apply {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) (i:ZMod J.n) :
    e (originalCyclicPairIndex J e i)=(e i).pair:=e.apply_symm_apply _

theorem originalCyclicPairIndex_involutive {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) : Function.Involutive (originalCyclicPairIndex J e) := by
  intro i
  apply e.injective
  rw [originalCyclicPairIndex_apply,originalCyclicPairIndex_apply]
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.pair_involutive hD (e i)

theorem originalCyclicPairIndex_ne_self {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) (i:ZMod J.n) : originalCyclicPairIndex J e i≠i := by
  intro he
  have hi:=congrArg e he
  rw [originalCyclicPairIndex_apply] at hi
  exact (e i).pair_ne_self hi

/-- The actual original group transformation maps the whole ordered side exactly to its actual cyclic partner. -/
theorem originalCyclicPairIndex_side_image {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hvertices:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hspec:∀i,J.edgeSegment i=(e i).planeCarrier) (i:ZMod J.n) :
    (P.compactifiedAction (fuchsianSideElement hD (e i).val.1)⁻¹).closedMap ''
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (originalCyclicVertex hD J hvertices i)
        (originalCyclicVertex hD J hvertices (i+1))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (originalCyclicVertex hD J hvertices
        (originalCyclicPairIndex J e i))
        (originalCyclicVertex hD J hvertices (originalCyclicPairIndex J e i+1)) := by
  rw [originalCyclicVertex_side_segment hD J hvertices e hspec,
    originalCyclicVertex_side_segment hD J hvertices e hspec,originalCyclicPairIndex_apply]
  exact (e i).pair_carrier

/-- Genuine actual pairing maps each true endpoint pair to the true cyclic partner endpoint pair; no ordered endpoint claim is assumed. -/
theorem originalCyclicPairIndex_endpoint_pair {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hvertices:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hspec:∀i,J.edgeSegment i=(e i).planeCarrier) (i:ZMod J.n) :
    ({(P.compactifiedAction (fuchsianSideElement hD (e i).val.1)⁻¹).closedMap
        (originalCyclicVertex hD J hvertices i),
      (P.compactifiedAction (fuchsianSideElement hD (e i).val.1)⁻¹).closedMap
        (originalCyclicVertex hD J hvertices (i+1))}:Set 𝕔𝔻)=
      {originalCyclicVertex hD J hvertices (originalCyclicPairIndex J e i),
       originalCyclicVertex hD J hvertices (originalCyclicPairIndex J e i+1)} := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.closed_segment_image_endpoints
  exact originalCyclicPairIndex_side_image hD J hvertices e hspec i

/-- The actual original Mobius side element reverses the genuine consecutive boundary endpoints; this is derived from convexity and its true action, without a supplied traversal-orientation hypothesis. -/
theorem originalCyclicPairIndex_endpoint_reverse {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ha:P.area D≠⊤) (J:PolygonalCircle)
    (hcarrier:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hvertices:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hspec:∀i,J.edgeSegment i=(e i).planeCarrier)
    (i:ZMod J.n) :
    let j:=originalCyclicPairIndex J e i
    (P.compactifiedAction (fuchsianSideElement hD (e i).val.1)⁻¹).closedMap
        (originalCyclicVertex hD J hvertices i)=originalCyclicVertex hD J hvertices (j+1) ∧
    (P.compactifiedAction (fuchsianSideElement hD (e i).val.1)⁻¹).closedMap
        (originalCyclicVertex hD J hvertices (i+1))=originalCyclicVertex hD J hvertices j :=
  _root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalOrientation.original_cyclic_pairing_reverse hD ha J e
    (originalCyclicVertex hD J hvertices) hcarrier
    (originalCyclicVertex_plane hD J hvertices)
    (originalCyclicVertex_side_segment hD J hvertices e hspec) i
end LowDimensionalTopology.Geometry.Fuchsian
