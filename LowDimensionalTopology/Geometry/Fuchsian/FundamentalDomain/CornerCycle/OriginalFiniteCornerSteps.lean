/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Refinement.OriginalRawCornerGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalRawCorners
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.IncidentTileChains
/-!
# Finite side steps at marked corners

The paired side reverses each side-point step. A step starting at a finite
marked endpoint lifts to one raw corner step with the same endpoint action.
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
open scoped Pointwise

/-- The genuine original side step is symmetric using its actual paired side and inverse element. -/
theorem originalFiniteSidePointStep_symm
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    {x y:P.domain.carrier} (hxy:fuchsianSidePointStep hD x y) :
    fuchsianSidePointStep hD y x := by
  obtain ⟨s,hx,rfl⟩:=hxy
  refine ⟨fuchsianPairedSide hD s,?_,?_⟩
  · rw [fuchsianPairedSide_val]
    exact mem_smul_set.mpr ⟨x,hx,rfl⟩
  · rw [fuchsianSideElement_paired,inv_inv,smul_inv_smul]

/-- A genuine finite original side step starting at an actual marked endpoint lands at an actual marked endpoint and is exactly one literal raw corner step. -/
theorem originalFiniteSidePointStep_rawCorner
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    {x y:P.domain.carrier} (hxy:fuchsianSidePointStep hD x y)
    (i:ZMod J.n) (hi:originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (P.finiteCoordinate x)) :
    ∃j:ZMod J.n,originalRawCornerStep J e i j∧
      originalCyclicVertex hD J hv j=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate y) := by
  obtain ⟨s,hx,rfl⟩:=hxy
  obtain ⟨v,hvs,hxv⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.exists_over_side hD s
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate
      x)) ((mem_fuchsianSideClosedModel_finite s x).mpr hx)
  let k:=e.symm v
  have hkv:e k=v:=e.apply_symm_apply v
  have hzi:originalCyclicVertex hD J hv i∈(e k).carrier:=by
    rw [hkv,hi]
    exact hxv
  have hact:(P.compactifiedAction (fuchsianSideElement hD (e k).val.1)⁻¹).closedMap
      (originalCyclicVertex hD J hv i)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate ((fuchsianSideElement hD s)⁻¹•x)) := by
    rw [hkv,hvs,hi,P.compactifiedAction_finite]
  rcases (originalCyclicVertex_mem_side_iff hD J hv e hs i k).mp hzi with hik|hik
  · refine ⟨originalCyclicPairIndex J e k+1,⟨k,Or.inl ⟨hik,rfl⟩⟩,?_⟩
    rw [hik] at hact
    exact (originalCyclicPairIndex_endpoint_reverse hD ha J hc hv e hs k).1.symm.trans hact
  · refine ⟨originalCyclicPairIndex J e k,⟨k,Or.inr ⟨hik,rfl⟩⟩,?_⟩
    rw [hik] at hact
    exact (originalCyclicPairIndex_endpoint_reverse hD ha J hc hv e hs k).2.symm.trans hact
end LowDimensionalTopology.Geometry.Fuchsian
