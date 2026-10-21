/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicFaceExtension
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

/-- Every genuine original side point belongs to a refined piece over that same original side, including the two real halves of a self-paired side. -/
theorem OriginalRefinedSide.exists_over_side
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (s:FuchsianPolygonSides P D) (x:𝕔𝔻) (hx:x∈fuchsianSideClosedModel s) :
    ∃v:OriginalRefinedSide hD,v.val.1=s∧x∈v.carrier := by
  classical
  let v:OriginalRefinedSide hD:=⟨(s,false),by simp only [Bool.false_eq_true,false_implies]⟩
  by_cases hself:fuchsianPairedSide hD s=s
  · let w:OriginalRefinedSide hD:=⟨(s,true),fun _=>hself⟩
    let A:=originalSelfSideSplit hD s hself
    have hv:v.carrier=A.first:=by
      simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,v,hself,dite_true,Bool.false_eq_true,ite_false]
      rfl
    have hw:w.carrier=A.second:=by
      simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,w,hself,dite_true,ite_true]
      rfl
    rw [←A.union_inter.1] at hx
    rcases hx with hx|hx
    · exact ⟨v,rfl,hv.symm ▸ hx⟩
    · exact ⟨w,rfl,hw.symm ▸ hx⟩
  · refine ⟨v,rfl,?_⟩
    simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,v,hself,dite_false] using hx

/-- A marked original vertex on a refined side is exactly one of that side's two genuine consecutive cyclic endpoints. -/
theorem originalCyclicVertex_mem_side_iff
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (i k:ZMod J.n) :
    originalCyclicVertex hD J hv i∈(e k).carrier↔i=k∨i=k+1 := by
  constructor
  · intro hx
    have hp:_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane (originalCyclicVertex hD J hv i)∈(e
      k).planeCarrier:=
      mem_image_of_mem _ hx
    rw [←hs k,originalCyclicVertex_plane] at hp
    have hmarked:J.IsVertexPoint (J.vertex i):=⟨i,rfl⟩
    rcases (hmarked.mem_edgeSegment_iff k).mp hp with he|he
    · exact Or.inl (J.vertex_injective he)
    · exact Or.inr (J.vertex_injective he)
  · intro h
    rcases h with h|h
    · subst i
      rw [←originalCyclicVertex_side_segment hD J hv e hs k]
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_closedModelSegmentParam]
      exact ⟨0,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelSegmentParam_zero _ _⟩
    · subst i
      rw [←originalCyclicVertex_side_segment hD J hv e hs k]
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_closedModelSegmentParam]
      exact ⟨1,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelSegmentParam_one _ _⟩
end LowDimensionalTopology.Geometry.Fuchsian
