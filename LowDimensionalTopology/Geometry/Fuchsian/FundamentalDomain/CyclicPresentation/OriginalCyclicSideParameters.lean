/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.ClosedSegmentParameters
/-!
# Parameters compatible with the original side pairings

Choose one interval parameter in each side pair and define its partner using
the actual side transformation and interval reversal. The parameters are
homeomorphisms onto the whole sides and retain the ordered endpoints.
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
open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- The genuine inverse original side element on the occurrence with its literal finite boundary index. -/
def originalCyclicEdgeAction {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) (i:Fin J.n) : 𝕔𝔻≃ₜ𝕔𝔻:=
  (P.compactifiedAction (fuchsianSideElement hD (e (originalCyclicFinIndex J i)).val.1)⁻¹).closedMap

/-- Both sides of a genuine original pair act by mutually inverse homeomorphisms, including at the actual ideal endpoints. -/
theorem originalCyclicEdgeAction_pair_apply {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) (i:Fin J.n) (x:𝕔𝔻) :
    originalCyclicEdgeAction J e (originalCyclicFinPair J e i) (originalCyclicEdgeAction J e i x)=x := by
  unfold originalCyclicEdgeAction
  rw [originalCyclicFinPair_apply,originalCyclicPairIndex_apply,
    _root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.pair_element,inv_inv]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_closedDiscToExtended.injective
  rw [P.compactifiedAction_sphere,P.compactifiedAction_sphere]
  let g:=fuchsianSideElement hD (e (originalCyclicFinIndex J i)).val.1
  change g.val.val (g.val.val.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended
    x))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended x
  exact g.val.val.apply_symm_apply _
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- An occurrence's actual reference parameter along its true finite-or-ideal segment. -/
def originalCyclicSideBaseParam {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (i:Fin J.n) (t:unitInterval) : 𝕔𝔻 :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelSegmentParam (originalCyclicVertex hD J hv
    (originalCyclicFinIndex J i))
    (originalCyclicVertex hD J hv (originalCyclicFinIndex J i+1)) t

/-- Choose each positive side parameter once and define the paired negative parameter by its actual original Mobius side map. -/
def originalCyclicSideParam {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (i:Fin J.n) (t:unitInterval) : 𝕔𝔻:=
  if i<originalCyclicFinPair J e i then originalCyclicSideBaseParam hD J hv i t
  else originalCyclicEdgeAction J e (originalCyclicFinPair J e i)
    (originalCyclicSideBaseParam hD J hv (originalCyclicFinPair J e i) (unitInterval.symm t))

/-- The genuine pair action identifies exactly the reverse parameters of the true paired boundary occurrences. -/
theorem originalCyclicSideParam_pair {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (i:Fin J.n) (t:unitInterval) :
    originalCyclicEdgeAction J e i (originalCyclicSideParam hD J hv e i t)=
      originalCyclicSideParam hD J hv e (originalCyclicFinPair J e i) (unitInterval.symm t) := by
  have hpp:=originalCyclicFinPair_involutive J e i
  by_cases hi : i < originalCyclicFinPair J e i
  · have hp : ¬originalCyclicFinPair J e i < i := not_lt_of_ge hi.le
    simp only [originalCyclicSideParam,hpp,ite_eq_left hi,ite_eq_right hp,unitInterval.symm_symm]
  · have hp : originalCyclicFinPair J e i < i :=
      lt_of_le_of_ne (le_of_not_gt hi) (originalCyclicFinPair_ne_self J e i)
    simp only [originalCyclicSideParam,hpp,ite_eq_right hi,ite_eq_left hp]
    simpa only [hpp] using originalCyclicEdgeAction_pair_apply J e (originalCyclicFinPair J e i)
      (originalCyclicSideBaseParam hD J hv (originalCyclicFinPair J e i) (unitInterval.symm t))

/-- The real reference segment parameter is continuous. -/
theorem continuous_originalCyclicSideBaseParam {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (i:Fin J.n) : Continuous (originalCyclicSideBaseParam hD J hv i) :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_closedModelSegmentParam _ _

/-- Distinct genuine consecutive original vertices give an injective reference interval parameter. -/
theorem originalCyclicSideBaseParam_injective {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (i:Fin J.n) : Function.Injective (originalCyclicSideBaseParam hD J hv i) := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelSegmentParam_injective
  intro he
  apply J.adjacent_ne (originalCyclicFinIndex J i)
  rw [←originalCyclicVertex_plane hD J hv (originalCyclicFinIndex J i),
    ←originalCyclicVertex_plane hD J hv (originalCyclicFinIndex J i+1)]
  exact congrArg _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane he

/-- The truly paired original boundary parameter remains continuous. -/
theorem continuous_originalCyclicSideParam {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (i:Fin J.n) : Continuous (originalCyclicSideParam hD J hv e i) := by
  unfold originalCyclicSideParam
  split_ifs
  · exact continuous_originalCyclicSideBaseParam hD J hv i
  · exact (originalCyclicEdgeAction J e (originalCyclicFinPair J e i)).continuous.comp
      ((continuous_originalCyclicSideBaseParam hD J hv _).comp unitInterval.continuous_symm)

/-- Its actual paired parameter is also injective, including at ideal endpoints. -/
theorem originalCyclicSideParam_injective {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (i:Fin J.n) : Function.Injective (originalCyclicSideParam hD J hv e i) := by
  unfold originalCyclicSideParam
  split_ifs
  · exact originalCyclicSideBaseParam_injective hD J hv i
  · exact (originalCyclicEdgeAction J e (originalCyclicFinPair J e i)).injective.comp
      ((originalCyclicSideBaseParam_injective hD J hv _).comp unitInterval.symm_bijective.injective)

/-- Pairing the paired finite occurrence returns its true original cyclic index. -/
theorem originalCyclicPairIndex_fin_pair {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) (i:Fin J.n) :
    originalCyclicPairIndex J e (originalCyclicFinIndex J (originalCyclicFinPair J e i))=
      originalCyclicFinIndex J i :=
  (originalCyclicFinPair_apply J e (originalCyclicFinPair J e i)).symm.trans
    (congrArg (originalCyclicFinIndex J) (originalCyclicFinPair_involutive J e i))

/-- The actual paired parameter starts at the real original occurrence vertex. -/
theorem originalCyclicSideParam_zero {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier) (i:Fin J.n) :
    originalCyclicSideParam hD J hv e i 0=originalCyclicVertex hD J hv (originalCyclicFinIndex J i) := by
  by_cases hi : i < originalCyclicFinPair J e i
  · simp only [originalCyclicSideParam,ite_eq_left
    hi,originalCyclicSideBaseParam,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelSegmentParam_zero]
  · simp only [originalCyclicSideParam,ite_eq_right hi,originalCyclicSideBaseParam,
      unitInterval.symm_zero,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelSegmentParam_one,originalCyclicEdgeAction]
    have hr:=(originalCyclicPairIndex_endpoint_reverse hD ha J hc hv e hs
      (originalCyclicFinIndex J (originalCyclicFinPair J e i))).2
    rw [originalCyclicPairIndex_fin_pair] at hr
    exact hr

/-- It ends at the next true original vertex in the unchanged cyclic order. -/
theorem originalCyclicSideParam_one {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier) (i:Fin J.n) :
    originalCyclicSideParam hD J hv e i 1=originalCyclicVertex hD J hv (originalCyclicFinIndex J i+1) := by
  by_cases hi : i < originalCyclicFinPair J e i
  · simp only [originalCyclicSideParam,ite_eq_left
    hi,originalCyclicSideBaseParam,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelSegmentParam_one]
  · simp only [originalCyclicSideParam,ite_eq_right hi,originalCyclicSideBaseParam,
      unitInterval.symm_one,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelSegmentParam_zero,originalCyclicEdgeAction]
    have hr:=(originalCyclicPairIndex_endpoint_reverse hD ha J hc hv e hs
      (originalCyclicFinIndex J (originalCyclicFinPair J e i))).1
    rw [originalCyclicPairIndex_fin_pair] at hr
    exact hr

/-- The reference interval covers precisely its genuine original refined side. -/
theorem range_originalCyclicSideBaseParam {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier) (i:Fin J.n) :
    range (originalCyclicSideBaseParam hD J hv i)=(e (originalCyclicFinIndex J i)).carrier :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_closedModelSegmentParam _ _).trans
    (originalCyclicVertex_side_segment hD J hv e hs (originalCyclicFinIndex J i))

/-- The Mobius-compatible parameter covers the entire actual original side, without extra or missing points. -/
theorem range_originalCyclicSideParam {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier) (i:Fin J.n) :
    range (originalCyclicSideParam hD J hv e i)=(e (originalCyclicFinIndex J i)).carrier := by
  unfold originalCyclicSideParam
  split_ifs
  · exact range_originalCyclicSideBaseParam hD J hv e hs i
  · change range (originalCyclicEdgeAction J e (originalCyclicFinPair J e i) ∘
      originalCyclicSideBaseParam hD J hv (originalCyclicFinPair J e i) ∘ unitInterval.symm)=_
    rw [Set.range_comp,Set.range_comp,unitInterval.symm_bijective.surjective.range_eq,image_univ,
      range_originalCyclicSideBaseParam hD J hv e hs]
    change (P.compactifiedAction (fuchsianSideElement hD
      (e (originalCyclicFinIndex J (originalCyclicFinPair J e i))).val.1)⁻¹).closedMap ''
        (e (originalCyclicFinIndex J (originalCyclicFinPair J e i))).carrier=_
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.pair_carrier]
    congr 1
    rw [←originalCyclicPairIndex_apply,originalCyclicPairIndex_fin_pair]

/-- A genuine original side parameter compatible with literal reverse word gluing is a true unit-interval homeomorphism onto that entire actual side. -/
def originalCyclicSideHomeomorph {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier) (i:Fin J.n) :
    unitInterval≃ₜ↥(e (originalCyclicFinIndex J i)).carrier := by
  let :T2Space 𝕔𝔻:=Complex.UnitClosedDisc.isEmbedding_coe.t2Space
  let f:unitInterval→↥(e (originalCyclicFinIndex J i)).carrier:=fun t=>
    ⟨originalCyclicSideParam hD J hv e i t,
      (range_originalCyclicSideParam hD J hv e hs i) ▸ mem_range_self t⟩
  have hf:Function.Bijective f:=by
    constructor
    · intro t u he
      exact originalCyclicSideParam_injective hD J hv e i (congrArg Subtype.val he)
    · rintro ⟨x,hx⟩
      obtain ⟨t,ht⟩:=(range_originalCyclicSideParam hD J hv e hs i).symm ▸ hx
      exact ⟨t,Subtype.ext ht⟩
  let E:=Equiv.ofBijective f hf
  have hc:Continuous f:=(continuous_originalCyclicSideParam hD J hv e i).subtype_mk _
  exact E.toHomeomorphOfContinuousClosed hc hc.isClosedMap
end LowDimensionalTopology.Geometry.Fuchsian
