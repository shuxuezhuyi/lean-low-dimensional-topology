/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.FuchsianSignatureOrders
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenConjugation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem fuchsianCyclicFixedPoints_conjugation_iff {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (kind:FuchsianCyclicKind) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (p:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    q.val p∈fuchsianCyclicFixedPoints (D.nielsenConjugate q) kind ↔p∈fuchsianCyclicFixedPoints D kind := by
  constructor
  · rintro ⟨hp, f,hfH,hft,hfix⟩
    obtain ⟨g,hg,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q
      H f).mp hfH
    have htype:=hft.conjugate q⁻¹
    rw [show q⁻¹*(q*g*q⁻¹)*(q⁻¹)⁻¹=g by group] at htype
    refine ⟨?_,g,hg,htype,?_⟩
    · intro hk
      obtain ⟨z,hz,he⟩:=hp hk
      exact q.val.injective he ▸ hz
    · change q • (g • (q⁻¹ • (q • p)))=q • p at hfix
      simp only [inv_smul_smul] at hfix
      exact q.val.injective hfix
  · rintro ⟨hp,f,hf,hft,hfix⟩
    refine ⟨fun hk=>⟨p,hp hk,rfl⟩,q*f*q⁻¹,⟨f,hf,rfl⟩,hft.conjugate q,?_⟩
    change q • (f • (q⁻¹ • (q • p)))=q • p
    simp only [inv_smul_smul]
    change q.val (f.val p)=q.val p
    rw [hfix]

def fuchsianCyclicPointConjugacyEquiv {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (kind:FuchsianCyclicKind) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    fuchsianCyclicFixedPoints D kind≃fuchsianCyclicFixedPoints (D.nielsenConjugate q) kind where
  toFun p:=⟨q.val p.val,(fuchsianCyclicFixedPoints_conjugation_iff D kind q p.val).mpr p.property⟩
  invFun p:=⟨q.val.symm p.val,(fuchsianCyclicFixedPoints_conjugation_iff D kind q _).mp
    ((q.val.apply_symm_apply p.val).symm ▸ p.property)⟩
  left_inv p:=Subtype.ext (q.val.symm_apply_apply p.val)
  right_inv p:=Subtype.ext (q.val.apply_symm_apply p.val)

theorem fuchsianCyclicPointConjugacyEquiv_equivariant {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (kind:FuchsianCyclicKind) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (g:H)
    (p:fuchsianCyclicFixedPoints D kind) :
    fuchsianCyclicPointConjugacyEquiv D kind q (g • p)=
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H g • fuchsianCyclicPointConjugacyEquiv D kind q p := by
  apply Subtype.ext
  change q • (g.val • p.val)=(q*g.val*q⁻¹) • (q • p.val)
  simp only [mul_smul,inv_smul_smul]

theorem fuchsianCyclicPointConjugacyEquiv_orbit_iff {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (kind:FuchsianCyclicKind) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (p r:fuchsianCyclicFixedPoints D kind) :
    MulAction.orbitRel H (fuchsianCyclicFixedPoints D kind) p r ↔
      MulAction.orbitRel (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H)
        (fuchsianCyclicFixedPoints (D.nielsenConjugate q) kind)
        (fuchsianCyclicPointConjugacyEquiv D kind q p) (fuchsianCyclicPointConjugacyEquiv D kind q r) := by
  constructor
  · rintro ⟨g,hg⟩
    exact ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H g,
      (fuchsianCyclicPointConjugacyEquiv_equivariant D kind q g r).symm.trans
        (congrArg (fuchsianCyclicPointConjugacyEquiv D kind q) hg)⟩
  · rintro ⟨g,hg⟩
    let k:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
      H).symm g
    refine ⟨k,(fuchsianCyclicPointConjugacyEquiv D kind q).injective ?_⟩
    rw [fuchsianCyclicPointConjugacyEquiv_equivariant,
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
        H).apply_symm_apply]
    exact hg

/-- Actual maximal elliptic and parabolic subgroup classes are transported by the genuine whole-group conjugacy. -/
def fuchsianCyclicClassConjugacyEquiv {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (kind:FuchsianCyclicKind) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    FuchsianCyclicConjugacyClasses D kind≃FuchsianCyclicConjugacyClasses (D.nielsenConjugate q) kind :=
  (fuchsianCyclicConjugacyClassesEquiv D kind).trans
    ((Quotient.congr (fuchsianCyclicPointConjugacyEquiv D kind q)
      (fuchsianCyclicPointConjugacyEquiv_orbit_iff D kind q)).trans
        (fuchsianCyclicConjugacyClassesEquiv (D.nielsenConjugate q) kind).symm)

theorem mobiusBoundaryStabilizer_global_conjugation (H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (p:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) (q.val p)=
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p) := by
  ext f
  constructor
  · intro hf
    obtain ⟨hfH,hfix⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer _ _ f).mp hf
    obtain ⟨g,hg,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q
      H f).mp hfH
    refine ⟨g,(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p g).mpr
      ⟨hg,?_⟩,rfl⟩
    change q • (g • (q⁻¹ • (q • p)))=q • p at hfix
    simp only [inv_smul_smul] at hfix
    exact q.val.injective hfix
  · rintro ⟨g,hg,rfl⟩
    obtain ⟨hgH,hfix⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p g).mp hg
    apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer _ _ _).mpr
    refine ⟨⟨g,hgH,rfl⟩,?_⟩
    change q • (g • (q⁻¹ • (q • p)))=q • p
    simp only [inv_smul_smul]
    change q.val (g.val p)=q.val p
    rw [hfix]

theorem fuchsianCyclicClassConjugacyEquiv_point (H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D:FuchsianDisc H) (kind:FuchsianCyclicKind) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (p:fuchsianCyclicFixedPoints D kind) :
    fuchsianCyclicClassConjugacyEquiv D kind q (Quotient.mk _ (fuchsianCyclicPointStabilizer D kind p))=
      Quotient.mk _ (fuchsianCyclicPointStabilizer (D.nielsenConjugate q) kind
        (fuchsianCyclicPointConjugacyEquiv D kind q p)) := by
  change Quotient.mk _ (fuchsianCyclicPointStabilizer (D.nielsenConjugate q) kind
    (fuchsianCyclicPointConjugacyEquiv D kind q
      ((fuchsianCyclicPointStabilizerEquiv D kind).symm ((fuchsianCyclicPointStabilizerEquiv D kind) p))))=_
  rw [Equiv.symm_apply_apply]

/-- The exact order of every actual maximal elliptic class is unchanged by original Mobius conjugacy. -/
theorem fuchsianEllipticClassOrder_global_conjugation {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (c:FuchsianCyclicConjugacyClasses D .elliptic) :
    fuchsianEllipticClassOrder (D.nielsenConjugate q) (fuchsianCyclicClassConjugacyEquiv D .elliptic q c)=
      fuchsianEllipticClassOrder D c := by
  induction c using Quotient.inductionOn with
  | _ K=>
    let p:=(fuchsianCyclicPointStabilizerEquiv D .elliptic).symm K
    have hp:fuchsianCyclicPointStabilizer D .elliptic p=K:=
      (fuchsianCyclicPointStabilizerEquiv D .elliptic).apply_symm_apply K
    rw [←hp,fuchsianCyclicClassConjugacyEquiv_point,fuchsianEllipticClassOrder_mk,fuchsianEllipticClassOrder_mk]
    change Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) (q.val p.val))=
      Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val)
    rw [mobiusBoundaryStabilizer_global_conjugation,subgroupConjugate_natCard]



theorem fuchsianCyclicClassConjugacyEquiv_natCard {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (kind:FuchsianCyclicKind) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    Nat.card (FuchsianCyclicConjugacyClasses (D.nielsenConjugate q) kind)=
      Nat.card (FuchsianCyclicConjugacyClasses D kind) :=
  Nat.card_congr (fuchsianCyclicClassConjugacyEquiv D kind q).symm

theorem fuchsianCyclicClassConjugacyEquiv_finite {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (kind:FuchsianCyclicKind) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    [Finite (FuchsianCyclicConjugacyClasses D kind)] :
    Finite (FuchsianCyclicConjugacyClasses (D.nielsenConjugate q) kind) :=
  Finite.of_equiv _ (fuchsianCyclicClassConjugacyEquiv D kind q)

/-- Actual entire elliptic order multisets, including multiplicities, are invariant under original whole-group conjugacy. -/
theorem fuchsianEllipticOrderList_global_conjugation {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    [Finite (FuchsianCyclicConjugacyClasses D .elliptic)]
    [Finite (FuchsianCyclicConjugacyClasses (D.nielsenConjugate q) .elliptic)] :
    (fuchsianEllipticOrderList D).Perm (fuchsianEllipticOrderList (D.nielsenConjugate q)) := by
  classical
  let :=Fintype.ofFinite (FuchsianCyclicConjugacyClasses D .elliptic)
  let :=Fintype.ofFinite (FuchsianCyclicConjugacyClasses (D.nielsenConjugate q) .elliptic)
  let e:=(Fintype.equivFin (FuchsianCyclicConjugacyClasses D .elliptic)).symm |>.trans
    ((fuchsianCyclicClassConjugacyEquiv D .elliptic q).trans
      (Fintype.equivFin (FuchsianCyclicConjugacyClasses (D.nielsenConjugate q) .elliptic)))
  apply signature_orderList_perm_of_equiv e
  intro i
  simp only [e,Equiv.trans_apply,Equiv.symm_apply_apply]
  exact fuchsianEllipticClassOrder_global_conjugation D q _

end LowDimensionalTopology.Geometry.Fuchsian
