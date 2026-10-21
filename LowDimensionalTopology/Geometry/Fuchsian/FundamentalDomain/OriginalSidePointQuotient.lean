/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.IncidentTileChains
public import Mathlib.Topology.Homeomorph.Quotient
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Literal finite chains of the actual original side pairings, restricted to the original finite polygon closure. -/
def fuchsianOriginalSidePointSetoid {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) :
    Setoid (closure D):=(Relation.EqvGen.setoid (fuchsianSidePointStep hD)).comap Subtype.val

/-- The actual original finite-point side gluing quotient with its genuine quotient topology. -/
abbrev FuchsianOriginalSidePointQuotient {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D):=
  Quotient (fuchsianOriginalSidePointSetoid hD)

/-- No extra orbit identifications are hidden in the literal original side-point gluing. -/
theorem IsConvexFuchsianPolygon.originalSidePointSetoid_iff_orbit {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (p q:closure D) :
    fuchsianOriginalSidePointSetoid hD p q↔_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.restrictedOrbitRel H P.domain.carrier (closure D) p q := by
  change Relation.EqvGen (fuchsianSidePointStep hD) p.val q.val↔∃g:H,g•q.val=p.val
  rw [hD.side_point_chain_iff_orbit p.val q.val p.property q.property]
  constructor
  · rintro ⟨g,hg⟩
    exact ⟨g⁻¹,by rw [←hg,inv_smul_smul]⟩
  · rintro ⟨g,hg⟩
    exact ⟨g⁻¹,by rw [←hg,inv_smul_smul]⟩

/-- The unchanged original closure side-word quotient and its genuine restricted orbit quotient are homeomorphic by the identity on representatives. -/
def IsConvexFuchsianPolygon.originalSidePointRestrictedHomeomorph {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) :
    FuchsianOriginalSidePointQuotient hD≃ₜFuchsianClosedDomainQuotient P D :=
  Homeomorph.Quotient.congrRight hD.originalSidePointSetoid_iff_orbit

/-- Literal original finite-point side gluing yields precisely the actual old original Fuchsian quotient topology. No supplied developing-map injectivity is required. -/
def IsConvexFuchsianPolygon.originalSidePointOrbitHomeomorph {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) :
    FuchsianOriginalSidePointQuotient hD≃ₜ_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient P.domain :=
  hD.originalSidePointRestrictedHomeomorph.trans hD.locallyFinite.comparisonHomeomorph

/-- The homeomorphism retains the literal old quotient class of every original finite polygon point. -/
theorem IsConvexFuchsianPolygon.originalSidePointOrbitHomeomorph_projection
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (p:closure D) :
    hD.originalSidePointOrbitHomeomorph (Quotient.mk (fuchsianOriginalSidePointSetoid hD) p)=
      _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection P.domain p.val := rfl

end LowDimensionalTopology.Geometry.Fuchsian
