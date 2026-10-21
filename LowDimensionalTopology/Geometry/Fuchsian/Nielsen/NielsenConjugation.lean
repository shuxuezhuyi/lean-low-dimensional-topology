/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenIdealHull
public import LowDimensionalTopology.Geometry.Surfaces.Cusp.GeneralParabolicCusps
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaGeometry
@[expose] public section
open Set
open scoped Topology OnePoint UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean
noncomputable section

theorem nielsen_loxodromicFixedPointSet_conjugation
    (H : Subgroup Mobius.complexMobiusGroup)
    (q : Mobius.complexMobiusGroup) : q.val '' DiscreteGroups.mobiusLoxodromicFixedPointSet H=
      DiscreteGroups.mobiusLoxodromicFixedPointSet (DiscreteGroups.Action.Actions.subgroupConjugate q H) := by
  apply Set.Subset.antisymm
  · rintro z ⟨w,⟨g,hg,hfix⟩,rfl⟩
    let k : DiscreteGroups.Action.Actions.subgroupConjugate q H:=⟨q*g.val*q⁻¹,
      (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨g.val,g.property,rfl⟩⟩
    refine ⟨k,Mobius.mobiusLoxodromic_conjugation_forward g.val q hg,?_⟩
    change (q*g.val*q⁻¹) • (q • w)=q • w
    rw [mul_smul,mul_smul,inv_smul_smul]
    change q • (g • w)=q • w
    rw [hfix]
  · rintro z ⟨g,hg,hfix⟩
    obtain ⟨f,hf,hfg⟩:=(DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H g.val).mp g.property
    have hfL : Mobius.MobiusLoxodromic f:=by
      rw [←hfg] at hg
      exact (Mobius.mobiusLoxodromic_conjugation f q).mp hg
    refine ⟨q⁻¹ • z,⟨⟨f,hf⟩,hfL,?_⟩,smul_inv_smul q z⟩
    change f • (q⁻¹ • z)=q⁻¹ • z
    change g.val • z=z at hfix
    rw [←hfg] at hfix
    have hh:=congrArg (fun w=>q⁻¹ • w) hfix
    simpa only [mul_smul,inv_smul_smul] using hh

theorem nielsen_mobiusLimitSet_conjugation
    (H : Subgroup Mobius.complexMobiusGroup)
    (q : Mobius.complexMobiusGroup) : q.val '' DiscreteGroups.mobiusLimitSet H=
      DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q H) := by
  change (Mobius.mobiusBoundaryHomeomorph q) '' closure (DiscreteGroups.mobiusLoxodromicFixedPointSet H)=_
  rw [Homeomorph.image_closure]
  exact congrArg closure (nielsen_loxodromicFixedPointSet_conjugation H q)

/-- Actual whole-domain and whole-group conjugation, with the original discontinuity data retained. -/
def FuchsianDisc.nielsenConjugate
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup) : FuchsianDisc (DiscreteGroups.Action.Actions.subgroupConjugate q H) := by
  let Ω : Surfaces.MobiusInvariantDomain H:=⟨D.carrier,D.isDisc.isOpen,D.isDisc.isConnected,D.invariant⟩
  exact ⟨q.val '' D.carrier,D.isDisc.image q,(Ω.conjugate q).invariant,
    Ω.conjugate_discontinuous q D.discontinuous⟩

theorem FuchsianDisc.nielsenConjugate_carrier
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (q : Mobius.complexMobiusGroup) :
    (D.nielsenConjugate q).carrier=q.val '' D.carrier := rfl

/-- Every original non-elementary Fuchsian domain admits a genuine half-plane chart
whose omitted ideal point lies in the actual conjugate limit set. -/
theorem FuchsianDisc.nielsenNormalizer_exists
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hH : DiscreteGroups.IsNonElementary H) :
    ∃q : Mobius.complexMobiusGroup,q.val '' D.carrier=Hyperbolic.openHalfPlaneSet ∧
      (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q H) := by
  let u:=D.halfPlaneNormalizer
  let K:=DiscreteGroups.Action.Actions.subgroupConjugate u H
  let E:=D.nielsenConjugate u
  have hE : E.carrier=Hyperbolic.openHalfPlaneSet:=D.halfPlaneNormalizer_image
  have hK : DiscreteGroups.IsNonElementary K:=hH.conjugation u
  obtain ⟨p,hp⟩:=DiscreteGroups.mobiusLimitSet_nonempty K hK
  have hpB:=E.loxodromic_limit_subset_frontier hp
  rw [hE,nielsen_openHalfPlane_frontier] at hpB
  obtain ⟨s,hs⟩:=Hyperbolic.halfPlaneIdealBoundary_exists_sl2_to_infty p hpB
  let q:=Hyperbolic.realSLMobius s*u
  refine ⟨q,?_,?_⟩
  · change ((Hyperbolic.realSLMobius s*u).val) '' D.carrier=_
    rw [show (Hyperbolic.realSLMobius s*u).val= (Hyperbolic.realSLMobius s).val*u.val by rfl,
      Equiv.Perm.coe_mul,Function.comp_def,←Set.image_image,D.halfPlaneNormalizer_image,
      realSLMobius_image_openHalfPlane]
  · rw [←nielsen_mobiusLimitSet_conjugation H q]
    obtain ⟨w,hw,he⟩:= (show p∈u.val '' DiscreteGroups.mobiusLimitSet H by rw [nielsen_mobiusLimitSet_conjugation H u];exact hp)
    refine ⟨w,hw,?_⟩
    change (Hyperbolic.realSLMobius s).val (u.val w)=∞
    rw [he]
    exact hs

end
end LowDimensionalTopology.Geometry.Fuchsian
