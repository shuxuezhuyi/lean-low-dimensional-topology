module
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Data.Set.UnionLift
public import Mathlib.Topology.Homeomorph.Defs
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LowDimensionalTopology.Geometry.Auxiliary.Topology
open Set

/-- Compatible homeomorphisms of finite closed covers glue to an actual
homeomorphism. Compatibility is required for the local maps and their inverses,
so both glued maps agree on every overlap. -/
theorem finite_closed_cover_homeomorph
    {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite I]
    (S : I→Set X) (T : I→Set Y)
    (hS : ⋃i,S i=univ) (hT : ⋃i,T i=univ)
    (hSc : ∀i,IsClosed (S i)) (hTc : ∀i,IsClosed (T i))
    (e : ∀i,S i≃ₜT i)
    (hf : ∀i j (x:X) (hi:x∈S i) (hj:x∈S j),
      (e i ⟨x,hi⟩).val=(e j ⟨x,hj⟩).val)
    (hb : ∀i j (y:Y) (hi:y∈T i) (hj:y∈T j),
      ((e i).symm ⟨y,hi⟩).val=((e j).symm ⟨y,hj⟩).val) :
    ∃E:X≃ₜY,
      (∀i (x:S i),E x=(e i x).val) ∧
      (∀i (y:T i),E.symm y=((e i).symm y).val) := by
  let F : X→Y:=Set.liftCover S (fun i x=>(e i x).val) hf hS
  let G : Y→X:=Set.liftCover T (fun i y=>((e i).symm y).val) hb hT
  have hF (i:I) (x:S i) : F x=(e i x).val:=Set.liftCover_coe x
  have hG (i:I) (y:T i) : G y=((e i).symm y).val:=Set.liftCover_coe y
  have hFc : Continuous F:=by
    apply (locallyFinite_of_finite S).continuous hS hSc
    intro i
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (fun x:S i=>F x)=(fun x:S i=>(e i x).val):=funext (hF i)
    change Continuous (fun x:S i=>F x)
    rw [he]
    exact continuous_subtype_val.comp (e i).continuous
  have hGc : Continuous G:=by
    apply (locallyFinite_of_finite T).continuous hT hTc
    intro i
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (fun y:T i=>G y)=(fun y:T i=>((e i).symm y).val):=funext (hG i)
    change Continuous (fun y:T i=>G y)
    rw [he]
    exact continuous_subtype_val.comp (e i).symm.continuous
  have hleft : Function.LeftInverse G F:=by
    intro x
    obtain ⟨i,hi⟩:=mem_iUnion.mp (hS.symm ▸ mem_univ x)
    change G (F (⟨x,hi⟩:S i))=x
    rw [hF i ⟨x,hi⟩,hG i (e i ⟨x,hi⟩)]
    exact congrArg Subtype.val ((e i).symm_apply_apply ⟨x,hi⟩)
  have hright : Function.RightInverse G F:=by
    intro y
    obtain ⟨i,hi⟩:=mem_iUnion.mp (hT.symm ▸ mem_univ y)
    change F (G (⟨y,hi⟩:T i))=y
    rw [hG i ⟨y,hi⟩,hF i ((e i).symm ⟨y,hi⟩)]
    exact congrArg Subtype.val ((e i).apply_symm_apply ⟨y,hi⟩)
  let E : X≃ₜY :=
    { toFun:=F
      invFun:=G
      left_inv:=hleft
      right_inv:=hright
      continuous_toFun:=hFc
      continuous_invFun:=hGc }
  exact ⟨E,hF,hG⟩

end LowDimensionalTopology.Geometry.Auxiliary.Topology
