module
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Constructions
@[expose] public section
open Set Topology
namespace LowDimensionalTopology.Geometry.Auxiliary.Topology
universe u
/-- An open set on which a genuine quotient relation has singleton classes
embeds openly in the original quotient topology. -/
theorem quotient_openEmbedding_of_open_rigid
    {X : Type u} [TopologicalSpace X] (R : Setoid X) (U : Set X) (hU : IsOpen U)
    (hRigid : ∀x∈U,∀y : X,R x y →x=y) :
    IsOpenEmbedding (fun x : U=>Quotient.mk R x.val) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_quot_mk.comp continuous_subtype_val
  · intro x y h
    exact Subtype.ext (hRigid x.val x.property y.val (Quotient.exact h))
  · intro A hA
    have ho : IsOpen (Subtype.val '' A):=hU.isOpenEmbedding_subtypeVal.isOpenMap _ hA
    apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
    have he : (Quotient.mk R) ⁻¹' ((fun x : U=>Quotient.mk R x.val) '' A)=Subtype.val '' A := by
      ext x
      constructor
      · rintro ⟨y,hy,hye⟩
        exact ⟨y,hy,hRigid y.val y.property x (Quotient.exact hye)⟩
      · rintro ⟨y,hy,rfl⟩
        exact mem_image_of_mem _ hy
    change IsOpen ((Quotient.mk R) ⁻¹' ((fun x : U=>Quotient.mk R x.val) '' A))
    rw [he]
    exact ho

/-- If a composition is a local homeomorphism and its first factor is
continuous and open, that first factor is itself locally a homeomorphism. -/
theorem localHomeomorphOn_first_of_comp_open
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X→Y} {g : Y→Z} {A : Set X}
    (hgf : IsLocalHomeomorphOn (g ∘ f) A) (hf : Continuous f) (hfo : IsOpenMap f) :
    IsLocalHomeomorphOn f A := by
  apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict A).mpr
  intro x hx
  obtain ⟨U,hU,hEmb⟩:=(isLocalHomeomorphOn_iff_isOpenEmbedding_restrict A).mp hgf x hx
  refine ⟨interior U,IsOpen.mem_nhds isOpen_interior (mem_interior_iff_mem_nhds.mpr hU),?_⟩
  have hc : IsOpenEmbedding ((interior U).domRestrict (g ∘ f)):=
    hEmb.comp ⟨.inclusion interior_subset,by rw [Set.range_inclusion];exact isOpen_induced isOpen_interior⟩
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact hf.comp continuous_subtype_val
  · intro a b hab
    exact hc.injective (congrArg g hab)
  · exact hfo.comp isOpen_interior.isOpenEmbedding_subtypeVal.isOpenMap
end LowDimensionalTopology.Geometry.Auxiliary.Topology
