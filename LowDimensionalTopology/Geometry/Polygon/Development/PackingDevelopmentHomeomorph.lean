/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareCompactDevelopment
public import Mathlib.Topology.Separation.Hausdorff
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.Polygon
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [T2Space A]
theorem continuousOpen_injective_of_openDense {f : A→B} (hc : Continuous f) (ho : IsOpenMap f)
    {D : Set A} (hD : IsOpen D) (hd : Dense D) (hi : Set.InjOn f D) : Function.Injective f := by
  intro x y hxy
  by_contra hne
  obtain ⟨U,V,hU,hV,hx,hy,hUV⟩:=t2_separation hne
  have hAU : IsOpen (U∩f ⁻¹' (f '' V)):=hU.inter ((ho V hV).preimage hc)
  have hxA : x∈U∩f ⁻¹' (f '' V):=⟨hx,⟨y,hy,hxy.symm⟩⟩
  obtain ⟨p,hpD,hpU,hpV⟩:=hd.exists_mem_open hAU ⟨x,hxA⟩
  obtain ⟨q,hqV,hqp⟩:=hpV
  have hAW : IsOpen (V∩f ⁻¹' (f '' (U∩D))):=
    hV.inter ((ho (U∩D) (hU.inter hD)).preimage hc)
  have hqW : q∈V∩f ⁻¹' (f '' (U∩D)):=⟨hqV,⟨p,⟨hpU,hpD⟩,hqp.symm⟩⟩
  obtain ⟨t,htD,htV,htI⟩:=hd.exists_mem_open hAW ⟨q,hqW⟩
  obtain ⟨s,hs,he⟩:=htI
  have hst : s=t:=hi hs.2 htD he
  exact Set.disjoint_left.mp hUV hs.1 (hst.symm ▸ htV)
end LowDimensionalTopology.Geometry.Polygon
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
universe u v
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)
variable [TopologicalSpace X]
local instance packingDevelopmentGeneratedTopology : TopologicalSpace S.Generated:=⊥
local instance packingDevelopmentGeneratedDiscrete : DiscreteTopology S.Generated:=⟨rfl⟩

def developmentInterior : Set S.Development:=S.project '' {a:S.Copy|a.2.val∈P.interior}

omit [TopologicalSpace X] in
theorem developmentInterior_preimage : S.project ⁻¹' S.developmentInterior={a:S.Copy|a.2.val∈P.interior} := by
  ext a
  constructor
  · rintro ⟨b,hb,hba⟩
    have he:=S.gluing_interior_rigid ((S.project_eq_iff b a).mp hba) (Or.inl hb)
    exact he ▸ hb
  · intro ha
    exact ⟨a,ha,rfl⟩

theorem developmentInterior_isOpen (ho : IsOpen P.interior) : IsOpen S.developmentInterior := by
  rw [S.isOpen_iff_project_preimage,S.developmentInterior_preimage]
  exact ho.preimage (continuous_subtype_val.comp continuous_snd)

theorem developmentInterior_dense (hcl : P.carrier⊆closure P.interior) : Dense S.developmentInterior := by
  intro q
  induction q using Quotient.inductionOn with
  | h a =>
    have hImage : Subtype.val '' {p:P.Point|p.val∈P.interior}=P.interior:=by
      ext x
      constructor
      · rintro ⟨p,hp,rfl⟩
        exact hp
      · intro hx
        exact ⟨⟨x,P.interior_subset_carrier hx⟩,hx,rfl⟩
    have hp : a.2∈closure {p:P.Point|p.val∈P.interior}:=by
      rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,hImage]
      exact hcl a.2.property
    have hc : Continuous (fun p:P.Point=>S.project (a.1,p)):=
      S.continuous_project.comp (continuous_const.prodMk continuous_id)
    exact map_mem_closure (f:=fun p:P.Point=>S.project (a.1,p)) hc hp (by intro p hp;exact ⟨(a.1,p),hp,rfl⟩)

omit [TopologicalSpace X] in
theorem evaluation_injOn_developmentInterior
    (hPack : ∀g h:S.Generated,g≠h→Disjoint (g • P.interior) (h • P.interior)) :
    Set.InjOn S.evaluation S.developmentInterior := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ he
  have hi : a.1=b.1:=by
    by_contra hne
    exact disjoint_left.mp (hPack a.1 b.1 hne) ⟨a.2.val,ha,rfl⟩
      ⟨b.2.val,hb,(S.evaluation_project a).symm.trans (he.trans (S.evaluation_project b))|>.symm⟩
  have hp : a.2=b.2:=by
    apply Subtype.ext
    apply (MulAction.injective a.1)
    change a.1 • a.2.val=a.1 • b.2.val
    have hh:=he
    change a.1 • a.2.val=b.1 • b.2.val at hh
    rwa [←hi] at hh
  exact congrArg S.project (Prod.ext hi hp)

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing

namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
universe u v
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)
variable [MetricSpace X]
local instance packingMetricGeneratedTopology : TopologicalSpace S.Generated:=⊥
local instance packingMetricGeneratedDiscrete : DiscreteTopology S.Generated:=⟨rfl⟩
variable [IsIsometricSMul S.Generated X]
/--
Actual local tessellation plus independently proved original packing imply global injectivity;
no compactness, uniform radius or covering premise occurs. Hausdorffness is genuinely derived from local tessellation.
-/
theorem FiniteFiberLocalTessellationCondition.evaluation_injective_of_packing
    (h : S.FiniteFiberLocalTessellationCondition) (ho : IsOpen P.interior)
    (hcl : P.carrier⊆closure P.interior)
    (hPack : ∀g k:S.Generated,g≠k→Disjoint (g • P.interior) (k • P.interior)) :
    Function.Injective S.evaluation := by
  let : T2Space S.Development:=h.t2Space S
  exact _root_.LowDimensionalTopology.Geometry.Polygon.continuousOpen_injective_of_openDense S.continuous_evaluation_of_generated_isometric
    (h.isOpenMap_evaluation S) (S.developmentInterior_isOpen ho) (S.developmentInterior_dense hcl)
      (S.evaluation_injOn_developmentInterior hPack)

/--
Original closed-chamber orbit covering supplies actual surjectivity, so local tessellation and independently
proved packing construct the global developing homeomorphism even for noncompact chambers.
-/
def FiniteFiberLocalTessellationCondition.homeomorph_of_packing_cover
    (h : S.FiniteFiberLocalTessellationCondition) (ho : IsOpen P.interior)
    (hcl : P.carrier⊆closure P.interior)
    (hPack : ∀g k:S.Generated,g≠k→Disjoint (g • P.interior) (k • P.interior))
    (hCover : ∀x:X,∃g:S.Generated,∃p:P.Point,g • p.val=x) : S.Development≃ₜX :=
  (Equiv.ofBijective S.evaluation ⟨h.evaluation_injective_of_packing S ho hcl hPack,
    fun x=>by obtain ⟨g,p,hgp⟩:=hCover x;exact ⟨S.project (g,p),hgp⟩⟩).toHomeomorphOfContinuousOpen
      S.continuous_evaluation_of_generated_isometric (h.isOpenMap_evaluation S)

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
