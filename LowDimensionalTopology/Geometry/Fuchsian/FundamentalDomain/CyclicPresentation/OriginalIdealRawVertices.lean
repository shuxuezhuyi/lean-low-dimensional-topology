/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalWordIdealPoints
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicRawArea
/-!
# Ideal polygon points are marked corners

Every ideal point of the compactified polygon closure is a refined endpoint.
The ideal preface points are therefore precisely stored marked corners,
with their original ideal coordinates.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Filter Topology
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
section IdealCorners
variable {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)

include ha e hs in
/-- Every actual ideal point of the unchanged polygon closure is one of the original marked corners; no ideal-corner completeness hypothesis is supplied. -/
theorem originalIdealClosedModel_is_rawVertex (p:𝕔𝔻)
    (hp:p∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate ''
      D)) (hn:‖(p:ℂ)‖=1) :
    ∃i:ZMod J.n,originalCyclicVertex hD J hv i=p := by
  let Q:=originalCyclicDiscPolygon hD ha J hv e hs
  have hI:Q.complexInterior=(fun x=>(P.finiteCoordinate x:ℂ)) '' D:=by
    rw [←Q.interior_complex_image,originalCyclicDiscPolygon_interior,image_image]
  have hcl:(p:ℂ)∈closure Q.complexInterior:=by
    rw [hI]
    have hm:=mem_closure_image (Complex.UnitClosedDisc.continuous_coe.continuousAt) hp
    simpa only [image_image,Function.comp_def,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel,Complex.UnitClosedDisc.coe_mk] using hm
  rw [Q.closure_complexInterior] at hcl
  have hnot:(p:ℂ)∉Q.complexInterior:=by
    intro hi
    have hnorm:‖(p:ℂ)‖<1:=by simpa only [Metric.mem_ball,dist_zero_right] using Q.complexInterior_subset_disc hi
    rw [hn] at hnorm
    exact (lt_irrefl 1) hnorm
  obtain ⟨z,hz,hzp⟩:=hcl.resolve_left hnot
  have hzp':z=p:=Subtype.ext hzp
  subst z
  obtain ⟨i,hi⟩:=mem_iUnion.mp hz
  have hne:Q.vertices i≠Q.vertices (finRotate J.n i):=Q.vertices_injective.ne (Q.next_ne_self i).symm
  rcases original_segment_ideal_eq_endpoint _ _ p hne hi hn with he|he
  · exact ⟨originalCyclicFinIndex J i,he.symm⟩
  · exact ⟨originalCyclicFinIndex J (finRotate J.n i),he.symm⟩

/-- Each actual stored corner maps to its exact original marked vertex. -/
theorem originalCyclicPreClosedModelHomeomorph_corner (i:ZMod J.n) :
    (originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs
      (((originalCyclicPresentation J e).presentation.occurrenceSide
        ((originalCyclicCornerIndex J e).symm i)).point 0)).val=
      originalCyclicVertex hD J hv i := by
  rw [originalCyclicPreClosedModelHomeomorph_side,originalCyclicSideParam_zero hD ha J hc hv e hs]
  exact congrArg (originalCyclicVertex hD J hv) ((originalCyclicCornerIndex J e).apply_symm_apply i)

/-- All genuine ideal preface points are actual stored marked corners, with their unchanged ideal coordinates. -/
theorem originalCyclicPreIdealPoint_is_rawCorner
    (a:(originalCyclicPresentation J e).presentation.PolygonalPreRealization)
    (ha':a∈originalCyclicPreIdealPoints hD ha J hc hv e hs) :
    ∃i:ZMod J.n,a=(((originalCyclicPresentation J e).presentation.occurrenceSide
      ((originalCyclicCornerIndex J e).symm i)).point 0)∧‖(originalCyclicVertex hD J hv i:ℂ)‖=1 := by
  let B:=originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs
  obtain ⟨i,hi⟩:=originalIdealClosedModel_is_rawVertex hD ha J hv e hs (B a).val (B a).property ha'
  refine ⟨i,B.injective (Subtype.ext ?_),?_⟩
  · exact hi.symm.trans (originalCyclicPreClosedModelHomeomorph_corner hD ha J hc hv e hs i).symm
  · rw [hi]
    exact ha'
end IdealCorners
end LowDimensionalTopology.Geometry.Fuchsian
