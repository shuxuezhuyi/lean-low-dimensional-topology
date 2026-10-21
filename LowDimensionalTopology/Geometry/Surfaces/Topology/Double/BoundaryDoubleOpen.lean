/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Double.DoubleClosedDisc
public import Mathlib.Topology.Constructions.SumProd
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Surfaces
open Set Topology
variable {X : Type*} [TopologicalSpace X] {B : Set X}

/-- Forgetting the sheet retains the actual physical base point. -/
def boundaryDoubleBase : BoundaryDouble X B→X:=Quotient.lift Prod.snd (fun _ _ h=>h.1)

theorem boundaryDoubleBase_continuous : Continuous (boundaryDoubleBase (B:=B)) :=
  continuous_quot_lift _ continuous_snd

/-- The literal double of a subset maps to the original double by the actual inclusion. -/
def boundaryDoubleInclusion (U : Set X) : BoundaryDouble U {x|x.val∈B}→BoundaryDouble X B:=
  Quotient.map (fun p:Bool×U=>(p.1,p.2.val)) (by
    intro a b h
    exact ⟨congrArg Subtype.val h.1,h.2⟩)

theorem boundaryDoubleInclusion_continuous (U : Set X) : Continuous (boundaryDoubleInclusion (B:=B) U) :=
by
  unfold boundaryDoubleInclusion
  exact continuous_quot_map _ (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

omit [TopologicalSpace X] in
theorem boundaryDoubleInclusion_injective (U : Set X) : Function.Injective (boundaryDoubleInclusion (B:=B) U) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      apply Quotient.sound
      have h:boundaryDoubleSetoid X B (a.1,a.2.val) (b.1,b.2.val):=Quotient.exact hab
      exact ⟨Subtype.ext h.1,h.2⟩

omit [TopologicalSpace X] in
theorem boundaryDoubleInclusion_range (U : Set X) :
    range (boundaryDoubleInclusion (B:=B) U)=boundaryDoubleBase ⁻¹' U := by
  ext q
  induction q using Quotient.inductionOn with
  | h a =>
    constructor
    · rintro ⟨p,hp⟩
      induction p using Quotient.inductionOn with
      | h b =>
        have h:boundaryDoubleSetoid X B (b.1,b.2.val) a:=Quotient.exact hp
        change a.2∈U
        exact h.1 ▸ b.2.property
    · intro hu
      exact ⟨Quotient.mk (boundaryDoubleSetoid U {x|x.val∈B}) (a.1,⟨a.2,hu⟩),rfl⟩

theorem boundaryDoubleInclusion_isOpenMap {U : Set X} (hU:IsOpen U) :
    IsOpenMap (boundaryDoubleInclusion (B:=B) U) := by
  intro V hV
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  let f:Bool×U→Bool×X:=fun a=>(a.1,a.2.val)
  have hf:IsOpenMap f:=IsOpenMap.id.prodMap hU.isOpenMap_subtype_val
  have hEq:(Quotient.mk (boundaryDoubleSetoid X B)) ⁻¹' (boundaryDoubleInclusion U '' V)=
      f '' ((Quotient.mk (boundaryDoubleSetoid U {x|x.val∈B})) ⁻¹' V) := by
    ext a
    constructor
    · rintro ⟨q,hq,he⟩
      induction q using Quotient.inductionOn with
      | h b =>
        have h:boundaryDoubleSetoid X B (b.1,b.2.val) a:=Quotient.exact he
        let b':Bool×U:=(a.1,⟨a.2,h.1 ▸ b.2.property⟩)
        have heq:(Quotient.mk (boundaryDoubleSetoid U {x|x.val∈B}) b':BoundaryDouble U {x|x.val∈B})=Quotient.mk (boundaryDoubleSetoid U {x|x.val∈B}) b:=by
          apply Quotient.sound
          refine ⟨Subtype.ext h.1.symm,?_⟩
          rcases h.2 with hb|hB
          · exact Or.inl hb.symm
          · right
            change a.2∈B
            exact h.1 ▸ hB
        refine ⟨b',?_,rfl⟩
        change (Quotient.mk (boundaryDoubleSetoid U {x|x.val∈B}) b')∈V
        rw [heq]
        exact hq
    · rintro ⟨b,hb,rfl⟩
      exact ⟨Quotient.mk (boundaryDoubleSetoid U {x|x.val∈B}) b,hb,rfl⟩
  change IsOpen ((Quotient.mk (boundaryDoubleSetoid X B)) ⁻¹' (boundaryDoubleInclusion U '' V))
  rw [hEq]
  exact hf _ (continuous_quotient_mk'.isOpen_preimage _ hV)

theorem boundaryDoubleInclusion_isOpenEmbedding {U : Set X} (hU:IsOpen U) :
    IsOpenEmbedding (boundaryDoubleInclusion (B:=B) U) :=
  .of_continuous_injective_isOpenMap (boundaryDoubleInclusion_continuous U)
    (boundaryDoubleInclusion_injective U) (boundaryDoubleInclusion_isOpenMap hU)

/-- The actual open part of the original double is precisely the double of the actual open part. -/
def boundaryDoubleOpenHomeomorph {U : Set X} (hU:IsOpen U) :
    BoundaryDouble U {x|x.val∈B}≃ₜ(boundaryDoubleBase (B:=B) ⁻¹' U) :=
  (boundaryDoubleInclusion_isOpenEmbedding (B:=B) hU).isEmbedding.toHomeomorph |>.trans
    (Homeomorph.setCongr (boundaryDoubleInclusion_range U))

end LowDimensionalTopology.Geometry.Surfaces
