/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicCompletionMap
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalFinitePointWordGluing
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalCuspOldPoints
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicSeparation
public import Mathlib.Topology.LocalAtTarget
/-!
# The original quotient inside the word completion

Finite preface points map to the old quotient exactly as the original group
orbits prescribe. The word completion map is injective over this old part,
and compactness gives the corresponding subspace homeomorphism.
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
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LeanEval.Topology.ClassificationOfSurfaces.Moise
section OldWordKernel
variable {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D₀:FuchsianDisc H)
    {L:Set (geometricDiscData D₀).domain.carrier}
    (hL:IsConvexFuchsianPolygon (geometricDiscData D₀) L) (ha:(geometricDiscData D₀).area L≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hL,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hL)
    (e:ZMod J.n≃OriginalRefinedSide hL) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    {n:ℕ} (S:_root_.LowDimensionalTopology.Geometry.Polygon.CyclicDiscPolygonSupportData n)
    (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein (geometricDiscData D₀) L)
    (hpar:∀u:Circle,(u:ℂ)∈fuchsianPolygonIdealBoundary (geometricDiscData D₀) L→
      ∃f:geometricDiscGroup D₀,f≠1∧_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val∧
        f.val.val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))

/-- Equality of the completion images of two genuine finite original representatives is already forced by the unchanged original side-word relation. -/
theorem originalFinitePreCompletionMap_wordGluing (x y:closure L)
    (he:originalCyclicPreCompletionMap D₀ hL ha J hc hv e hs S hr hpar
        (originalFinitePrePoint hL ha J hc hv e hs x)=
      originalCyclicPreCompletionMap D₀ hL ha J hc hv e hs S hr hpar
        (originalFinitePrePoint hL ha J hc hv e hs y)) :
    (originalCyclicPresentation J e).presentation.PolygonalGluingRel
      (originalCyclicPresentation J e).valid
      (originalFinitePrePoint hL ha J hc hv e hs x)
      (originalFinitePrePoint hL ha J hc hv e hs y) := by
  let q:=geometricDiscNormalizer D₀
  let K:=originalFiniteClosedHull q S.vertices
  let HK:=finite_cyclic_hull_original_cusp_admissible D₀ L S hr hpar
  let E:=originalCyclicPreSphereHomeomorph hL ha J hc hv e hs q S hr
  obtain ⟨g,hg⟩:=(fuchsianCuspSubsetProjection_eq_iff D₀ K HK
    (E (originalFinitePrePoint hL ha J hc hv e hs x))
    (E (originalFinitePrePoint hL ha J hc hv e hs y))).mp he
  have hg':g.val.val (q.val.symm y.val.val)=q.val.symm x.val.val:=by
    change g.val.val (q.val.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended
      (originalCyclicPreClosedModelHomeomorph hL ha J hc hv e hs
        (originalFinitePrePoint hL ha J hc hv e hs y)).val))=
      q.val.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended
      (originalCyclicPreClosedModelHomeomorph hL ha J hc hv e hs
        (originalFinitePrePoint hL ha J hc hv e hs x)).val) at hg
    simpa only [originalFinitePrePoint_coe,originalFinitePoint_closedModel_sphere] using hg
  let gn:geometricDiscGroup D₀:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H g
  have hgn:gn•y.val=x.val:=by
    apply Subtype.ext
    change q.val (g.val.val (q.val.symm y.val.val))=x.val.val
    rw [hg',q.val.apply_symm_apply]
  exact Relation.EqvGen.symm _ _
    (originalFiniteOrbit_wordGluing hL ha J hc hv e hs y x gn hgn)
/-- The old part of the actual projection is exactly the genuine finite polygon closure, rather than a supplied subset of representatives. -/
theorem originalCyclicPreCompletionMap_mem_old_iff
    (a:(originalCyclicPresentation J e).presentation.PolygonalPreRealization) :
    originalCyclicPreCompletionMap D₀ hL ha J hc hv e hs S hr hpar a∈
        range (fuchsianCuspCompletionOld D₀)↔
      ∃x:closure L,a=originalFinitePrePoint hL ha J hc hv e hs x := by
  let q:=geometricDiscNormalizer D₀
  let K:=originalFiniteClosedHull q S.vertices
  let HK:=finite_cyclic_hull_original_cusp_admissible D₀ L S hr hpar
  let B:=originalCyclicPreClosedModelHomeomorph hL ha J hc hv e hs
  let E:=originalCyclicPreSphereHomeomorph hL ha J hc hv e hs q S hr
  change fuchsianCuspSubsetProjection D₀ K HK (E a)∈range (fuchsianCuspCompletionOld D₀)↔_
  rw [originalCuspSubsetProjection_mem_old_iff]
  constructor
  · intro hz
    have hfin:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (B a).val∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=by
      rw [←geometricDiscNormalizer_image D₀]
      refine ⟨(E a).val,hz,?_⟩
      change q.val (q.val.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (B a).val))=_
      exact q.val.apply_symm_apply _
    let x:(geometricDiscData D₀).domain.carrier:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended
      (B a).val,hfin⟩
    have hB:(B a).val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ((geometricDiscData D₀).finiteCoordinate x):=by
      apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_closedDiscToExtended.injective
      exact (originalFinitePoint_closedModel_sphere (geometricDiscData D₀) x).symm
    have hx:x∈closure L:=(originalFiniteClosedModel_mem_iff x).mp (hB ▸ (B a).property)
    refine ⟨⟨x,hx⟩,B.injective (Subtype.ext ?_)⟩
    exact hB.trans (originalFinitePrePoint_coe hL ha J hc hv e hs ⟨x,hx⟩).symm
  · rintro ⟨x,rfl⟩
    change q.val.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended
      (B (originalFinitePrePoint hL ha J hc hv e hs x)).val)∈D₀.carrier
    rw [originalFinitePrePoint_coe,originalFinitePoint_closedModel_sphere]
    have hx:x.val.val∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=x.val.property
    rw [←geometricDiscNormalizer_image D₀] at hx
    obtain ⟨z,hz,he⟩:=hx
    change q.val z=x.val.val at he
    rw [←he,q.val.symm_apply_apply]
    exact hz

/-- No extra identification remains above an actual old quotient point. All genuine finite word fibers are exactly the original group orbits. -/
theorem originalCyclicCompletionMap_old_injective
    {a b:(originalCyclicPresentation J e).presentation.PolygonalRealization
      (originalCyclicPresentation J e).valid}
    (ha':originalCyclicCompletionMap D₀ hL ha J hc hv e hs S hr hpar a∈
      range (fuchsianCuspCompletionOld D₀))
    (hb':originalCyclicCompletionMap D₀ hL ha J hc hv e hs S hr hpar b∈
      range (fuchsianCuspCompletionOld D₀))
    (he:originalCyclicCompletionMap D₀ hL ha J hc hv e hs S hr hpar a=
      originalCyclicCompletionMap D₀ hL ha J hc hv e hs S hr hpar b) : a=b := by
  induction a using Quotient.inductionOn with
  | h a=>
      induction b using Quotient.inductionOn with
      | h b=>
          obtain ⟨x,rfl⟩:=(originalCyclicPreCompletionMap_mem_old_iff D₀ hL ha J hc hv e hs S hr hpar a).mp ha'
          obtain ⟨y,rfl⟩:=(originalCyclicPreCompletionMap_mem_old_iff D₀ hL ha J hc hv e hs S hr hpar b).mp hb'
          exact Quotient.sound (originalFinitePreCompletionMap_wordGluing D₀ hL ha J hc hv e hs S hr hpar x y he)

/-- The actual old subspace of the original faithful word quotient is homeomorphic to the unchanged old subspace of the unique cusp completion. Closedness comes from the genuine compact word realization, not from a supplied quotient-topology assertion. -/
def originalCyclicCompletionOldHomeomorph :
    ↥((originalCyclicCompletionMap D₀ hL ha J hc hv e hs S hr hpar) ⁻¹'
      range (fuchsianCuspCompletionOld D₀))≃ₜ↥(range (fuchsianCuspCompletionOld D₀)) := by
  let F:=originalCyclicCompletionMap D₀ hL ha J hc hv e hs S hr hpar
  let O:=range (fuchsianCuspCompletionOld D₀)
  letI:=originalCyclicPresentation_compactSpace J e
  letI:=fuchsianCuspCompletion_t2Space D₀
  have hF:Continuous F:=continuous_originalCyclicCompletionMap D₀ hL ha J hc hv e hs S hr hpar
  have hsur:Function.Surjective F:=originalCyclicCompletionMap_surjective D₀ hL ha J hc hv e hs S hr hpar
  have hinj:Function.Injective (O.restrictPreimage F):=by
    intro x y hxy
    apply Subtype.ext
    exact originalCyclicCompletionMap_old_injective D₀ hL ha J hc hv e hs S hr hpar
      x.property y.property (congrArg Subtype.val hxy)
  exact (Equiv.ofBijective (O.restrictPreimage F) ⟨hinj,hsur.restrictPreimage O⟩).toHomeomorphOfContinuousClosed
    hF.restrictPreimage (hF.isClosedMap.restrictPreimage O)

end OldWordKernel
end LowDimensionalTopology.Geometry.Fuchsian
