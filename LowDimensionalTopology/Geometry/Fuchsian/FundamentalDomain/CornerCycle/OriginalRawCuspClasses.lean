/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalRawIdealWordPoints
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalWordIdealCuspLabels
/-!
# Ideal raw corner classes and cusps

For the specified polygon support and parabolic fixed-point data, zero-weight
raw corner classes correspond to cusp classes. Their cardinality is the
original group's cusp count.
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
section RawCuspClasses
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

/-- The zero-weight literal raw corner classes correspond to all actual cusp classes of the unchanged original group, through its genuine completion. -/
def originalRawIdealCuspEquiv :
    {q:Quotient (originalRawCornerSetoid J e)//originalRawCornerClassWeight hL ha J hc hv e hs q=0}≃
      FuchsianCyclicConjugacyClasses D₀ .parabolic :=
  (originalRawIdealWordEquiv hL ha J hc hv e hs).trans
    (originalWordIdealCuspEquiv D₀ hL ha J hc hv e hs S hr hpar)

include S hr hpar in
/-- The actual original cusp count is exactly the number of genuine ideal classes of the unchanged original side word. -/
theorem originalRawZeroClassCount_eq_cusps :
    originalRawZeroClassCount hL ha J hc hv e hs=
      Nat.card (FuchsianCyclicConjugacyClasses D₀ .parabolic) := by
  classical
  calc
    _=Nat.card {q:Quotient (originalRawCornerSetoid J e)//originalRawCornerClassWeight hL ha J hc hv e hs q=0}:=by
      simp only [originalRawZeroClassCount,Nat.card_eq_fintype_card,Fintype.card_subtype]
    _=Nat.card (FuchsianCyclicConjugacyClasses D₀ .parabolic):=
      Nat.card_congr (originalRawIdealCuspEquiv D₀ hL ha J hc hv e hs S hr hpar)
end RawCuspClasses
end LowDimensionalTopology.Geometry.Fuchsian
