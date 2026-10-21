/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicPreSphereGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FiniteAreaCuspQuotients
/-!
# The polygon face map into the cusp completion

The stored face maps through its original sphere hull to the cusp completion.
Finite-hull cusp bounds give continuity, and every stored side pairing has
equal images at the corresponding reversed parameters.
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

/-- The actual stored face projects into the original group's unique cusp completion, with actual geometric cusp admissibility proved from the actual ideal fixers. -/
def originalCyclicPreCompletionMap {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D₀:FuchsianDisc H)
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
        f.val.val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    (originalCyclicPresentation J e).presentation.PolygonalPreRealization→FuchsianCuspCompletion D₀ :=
  fuchsianCuspSubsetProjection D₀ (originalFiniteClosedHull (geometricDiscNormalizer D₀) S.vertices)
    (finite_cyclic_hull_original_cusp_admissible D₀ L S hr hpar) ∘
    originalCyclicPreSphereHomeomorph hL ha J hc hv e hs (geometricDiscNormalizer D₀) S hr

/-- The actual face projection is genuinely continuous for the cusp topology; all uniform cusp-coordinate bounds come from the true finite hull, without supplied bounds. -/
theorem continuous_originalCyclicPreCompletionMap {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D₀:FuchsianDisc H)
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
        f.val.val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    Continuous (originalCyclicPreCompletionMap D₀ hL ha J hc hv e hs S hr hpar) :=
  (fuchsianCuspSubsetProjection_continuous D₀ _
    (finite_cyclic_hull_original_cusp_admissible D₀ L S hr hpar)
    (originalFiniteClosedHull_cusp_bounds D₀ _ (geometricDiscNormalizer_image D₀) S.vertices)).comp
    (originalCyclicPreSphereHomeomorph hL ha J hc hv e hs (geometricDiscNormalizer D₀) S hr).continuous

/-- Every literal word gluing generator has identical images in the unchanged original cusp completion; no desired gluing-orbit correspondence is an input. -/
theorem originalCyclicPreCompletionMap_pairing {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D₀:FuchsianDisc H)
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
    (pairing:(originalCyclicPresentation J e).presentation.BoundaryPairing) (t:unitInterval) :
    originalCyclicPreCompletionMap D₀ hL ha J hc hv e hs S hr hpar (pairing.identification.source.point t)=
      originalCyclicPreCompletionMap D₀ hL ha J hc hv e hs S hr hpar
        (pairing.identification.target.point (pairing.identification.parameter t)) := by
  let P:=geometricDiscData D₀
  let q:=geometricDiscNormalizer D₀
  let K:=originalFiniteClosedHull q S.vertices
  let Hk:=finite_cyclic_hull_original_cusp_admissible D₀ L S hr hpar
  let B:=originalCyclicPreClosedModelHomeomorph hL ha J hc hv e hs
  let E:=originalCyclicPreSphereHomeomorph hL ha J hc hv e hs q S hr
  let a:=pairing.identification.source.point t
  let b:=pairing.identification.target.point (pairing.identification.parameter t)
  let gn:geometricDiscGroup D₀:=
    (fuchsianSideElement hL (e (originalCyclicFinIndex J (originalCyclicOccurrenceIndex J e pairing.source))).val.1)⁻¹
  let g:H:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
    H).symm gn
  have hg:q*g.val*q⁻¹=gn.val:=
    congrArg Subtype.val ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H).apply_symm_apply gn)
  have hgeom:(P.compactifiedAction gn).closedMap (B a).val=(B b).val:=
    originalCyclicBoundaryPairing_geometric hL ha J hc hv e hs pairing t
  have hgs:gn.val.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (B
    a).val)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (B b).val:=
    (P.compactifiedAction_sphere gn (B a).val).symm.trans (congrArg
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended hgeom)
  change fuchsianCuspSubsetProjection D₀ K Hk (E a)=fuchsianCuspSubsetProjection D₀ K Hk (E b)
  apply Eq.symm
  apply (fuchsianCuspSubsetProjection_eq_iff D₀ K Hk (E b) (E a)).mpr
  refine ⟨g,?_⟩
  change g.val.val (q.val.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (B a).val))=
    q.val.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (B b).val)
  apply q.val.injective
  rw [q.val.apply_symm_apply]
  change (q*g.val*q⁻¹).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (B
    a).val)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (B b).val
  rw [hg]
  exact hgs
end LowDimensionalTopology.Geometry.Fuchsian
