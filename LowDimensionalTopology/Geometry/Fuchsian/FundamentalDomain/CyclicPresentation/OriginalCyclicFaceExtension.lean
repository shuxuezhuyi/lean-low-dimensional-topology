/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicBoundaryParameters
public import Mathlib.Analysis.Convex.GaugeRescale
public import LowDimensionalTopology.External.LeanPool.ClassificationOfSurfaces.PolygonCellRadial
public import LowDimensionalTopology.External.LeanPool.ClassificationOfSurfaces.RepresentativeCarrier
/-!
# Extending the marked boundary across a face

An ambient convex-body gauge identifies the polygon with a closed disc.
Radial extension of its marked boundary map fills the face while preserving
every side parameter, including finite and ideal endpoints.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped Complex.UnitDisc
set_option maxHeartbeats 600000
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LeanEval.Topology.ClassificationOfSurfaces
open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- A genuine ambient homeomorphism straightening the actual compact convex Klein body, with its actual interior and entire boundary. -/
def originalPolygonGaugeData {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) :
    {f:ℂ≃ₜℂ // f '' interior (fuchsianPolygonCompactKlein P D)=Metric.ball 0 1 ∧
      f '' fuchsianPolygonCompactKlein P D=Metric.closedBall 0 1 ∧
      f '' frontier (fuchsianPolygonCompactKlein P D)=Metric.sphere 0 1} := by
  have hex : ∃f:ℂ≃ₜℂ,
      f '' interior (fuchsianPolygonCompactKlein P D)=Metric.ball 0 1 ∧
      f '' fuchsianPolygonCompactKlein P D=Metric.closedBall 0 1 ∧
      f '' frontier (fuchsianPolygonCompactKlein P D)=Metric.sphere 0 1 := by
    obtain ⟨f,hi,hc,hf⟩:=exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      hD.klein_convex.closure (compactKlein_interior_nonempty hD)
      (fuchsianPolygonCompactKlein_compact P D).isBounded
    refine ⟨f,hi,?_,hf⟩
    change f '' closure (P.kleinCoordinate '' D)=_
    simpa only [closure_closure] using hc
  exact ⟨Classical.choose hex,Classical.choose_spec hex⟩

/-- The genuine whole raw boundary and the actual Klein frontier are the same subspace in their real coordinates. -/
def originalRefinedBoundaryKleinHomeomorph {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤) :
    ↥(⋃v:OriginalRefinedSide hD,v.carrier)≃ₜ↥(frontier (fuchsianPolygonCompactKlein P D)) :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.isEmbedding.homeomorphImage
    (⋃v:OriginalRefinedSide hD,v.carrier)).trans
      (Homeomorph.setCongr (finite_area_refined_boundary_klein hD ha))

/-- The chosen ambient gauge restricted to the true compact original polygon. -/
def originalPolygonGaugeCellHomeomorph {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (n:ℕ) :
    PolygonCell n≃ₜ↥(fuchsianPolygonCompactKlein P D) :=
  (PolygonCell.closedUnitDiscHomeomorph n).trans
    ((((originalPolygonGaugeData hD).val.image (fuchsianPolygonCompactKlein P D)).trans
      (Homeomorph.setCongr (originalPolygonGaugeData hD).property.2.1)).symm)

theorem originalPolygonGaugeCellHomeomorph_coe
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (n:ℕ) (x:PolygonCell n) :
    (originalPolygonGaugeCellHomeomorph hD n x:ℂ)=(originalPolygonGaugeData hD).val.symm (x:ℂ) := rfl

/-- The actual marked boundary homeomorphism transferred into the ambient gauge circle. -/
def originalCyclicGaugeBoundaryHomeomorph
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier) :
    Circle≃ₜCircle :=
  ((originalCyclicBoundaryHomeomorph hD ha J hc hv e hs).trans
    (originalRefinedBoundaryKleinHomeomorph hD ha)).trans
      (((originalPolygonGaugeData hD).val.image (frontier (fuchsianPolygonCompactKlein P D))).trans
        (Homeomorph.setCongr (originalPolygonGaugeData hD).property.2.2))

/-- Radially extend the actual marked-boundary homeomorphism, then undo the ambient convex-body gauge. Every original side parameter is preserved. -/
def originalCyclicFaceHomeomorph
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier) :
    PolygonCell J.n≃ₜ↥(fuchsianPolygonCompactKlein P D) :=
  (PolygonCell.radialHomeomorph (n:=J.n) (m:=J.n)
    (originalCyclicGaugeBoundaryHomeomorph hD ha J hc hv e hs)).trans
      (originalPolygonGaugeCellHomeomorph hD J.n)

theorem originalCyclicFaceHomeomorph_ofCircle
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier) (z:Circle) :
    (originalCyclicFaceHomeomorph hD ha J hc hv e hs (PolygonCell.ofCircle J.n z):ℂ)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (originalCyclicBoundaryHomeomorph hD ha J hc hv e hs z).val := by
  change (originalPolygonGaugeCellHomeomorph hD J.n
    (PolygonCell.radialHomeomorph (n:=J.n) (m:=J.n)
      (originalCyclicGaugeBoundaryHomeomorph hD ha J hc hv e hs) (PolygonCell.ofCircle J.n z)):ℂ)=_
  rw [PolygonCell.radialHomeomorph_ofCircle,originalPolygonGaugeCellHomeomorph_coe]
  change (originalPolygonGaugeData hD).val.symm
    ((originalPolygonGaugeData hD).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      (originalCyclicBoundaryHomeomorph hD ha J hc hv e hs z).val))=_
  exact (originalPolygonGaugeData hD).val.symm_apply_apply _

/-- The filled actual original polygon matches every original paired side parameter exactly, including finite and ideal endpoints. -/
theorem originalCyclicFaceHomeomorph_side
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (i:Fin J.n) (t:unitInterval) :
    (originalCyclicFaceHomeomorph hD ha J hc hv e hs (PolygonCell.side i t):ℂ)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (originalCyclicSideParam hD J hv e i t) := by
  change (originalCyclicFaceHomeomorph hD ha J hc hv e hs
    (PolygonCell.ofCircle J.n (_root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover J.n ⟨i,t⟩)):ℂ)=_
  rw [originalCyclicFaceHomeomorph_ofCircle,originalCyclicBoundaryHomeomorph_cover]
  rfl
end LowDimensionalTopology.Geometry.Fuchsian
