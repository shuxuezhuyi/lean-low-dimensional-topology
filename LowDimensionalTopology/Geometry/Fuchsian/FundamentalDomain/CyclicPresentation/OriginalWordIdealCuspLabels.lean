/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalWordCompletionHomeomorph
/-!
# Cusp labels on ideal word points

Restricting the word-completion homeomorphism identifies ideal word points
with the added cusp part. Its labels are exactly the maximal parabolic
cyclic conjugacy classes of the original group.
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
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LeanEval.Topology.ClassificationOfSurfaces.Moise
section IdealCuspLabels
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

/-- The actual ideal point classes of the unchanged original word correspond bijectively to all actual maximal parabolic conjugacy classes of the original group. The labels come from the genuine original completion. -/
def originalWordIdealCuspEquiv :
    ↥(originalCyclicWordIdealPoints hL ha J hc hv e hs)≃
      FuchsianCyclicConjugacyClasses D₀ .parabolic := by
  let E:=originalCyclicCompletionHomeomorph D₀ hL ha J hc hv e hs S hr hpar
  have hAB (x:(originalCyclicPresentation J e).presentation.PolygonalRealization
      (originalCyclicPresentation J e).valid) :
      x∈originalCyclicWordIdealPoints hL ha J hc hv e hs↔E x∉range (fuchsianCuspCompletionOld D₀):=by
    exact (Set.ext_iff.mp (originalCyclicCompletionMap_preimage_new D₀ hL ha J hc hv e hs S hr hpar) x).symm
  let T:↥(originalCyclicWordIdealPoints hL ha J hc hv e hs)≃
      {x:FuchsianCuspCompletion D₀//x∉range (fuchsianCuspCompletionOld D₀)}:=
    { toFun:=fun x=>⟨E x,(hAB x).mp x.property⟩
      invFun:=fun y=>⟨E.symm y,(hAB (E.symm y)).mpr (by rw [E.apply_symm_apply];exact y.property)⟩
      left_inv:=fun x=>Subtype.ext (E.symm_apply_apply x)
      right_inv:=fun y=>Subtype.ext (E.apply_symm_apply y) }
  exact T.trans (fuchsianCuspCompletionComplementEquiv D₀).symm

include S hr hpar in
/-- The number of actual ideal word points equals the original group's complete actual cusp-class count. -/
theorem originalWordIdealPoints_card_cusps :
    Nat.card ↥(originalCyclicWordIdealPoints hL ha J hc hv e hs)=
      Nat.card (FuchsianCyclicConjugacyClasses D₀ .parabolic) :=
  Nat.card_congr (originalWordIdealCuspEquiv D₀ hL ha J hc hv e hs S hr hpar)
end IdealCuspLabels
end LowDimensionalTopology.Geometry.Fuchsian
