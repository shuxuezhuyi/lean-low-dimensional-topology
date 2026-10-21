/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckePingPongGeometry
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.PingPong
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativePoincarePolygons
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups ComplexConjugate Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem finite_order_mem_zpowers_power {G : Type*} [Group G]
    (f g : G) (n : ℕ) (hn : 0<n) (hf : orderOf f=n) (hg : g∈Subgroup.zpowers f) :
    ∃m : ℕ,m<n ∧ f^m=g := by
  classical
  have hfin : IsOfFinOrder f:=orderOf_pos_iff.mp (by rw [hf];exact hn)
  obtain ⟨m,hm,hmg⟩:=Finset.mem_image.mp (hfin.mem_zpowers_iff_mem_range_orderOf.mp hg)
  exact ⟨m,by simpa only [hf,Finset.mem_range] using hm,hmg⟩

theorem heckePingPongSector_disjoint_translate (n : ℕ) (hn : 3≤n)
    (g : ℍ≃ᵢℍ)
    (hg : g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL n)))
    (hne : g≠1) : Disjoint (g • heckePingPongSector n hn) (heckePingPongSector n hn) := by
  classical
  have hn0 : 0<n:=by omega
  obtain ⟨m,_hm,rfl⟩:=finite_order_mem_zpowers_power _ g n hn0
    (standardHeckeCornerSL_order n hn) hg
  obtain ⟨j,hj⟩:=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_zpow_eq_fin n hn0 (-(m:ℤ))
  have hjc : ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n:ℂ)⁻¹)^m=(_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n^j.val:Circle):=by
    have hj' : ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n)⁻¹)^m=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n^j.val:=by
      simpa only [zpow_neg,zpow_natCast,inv_pow] using hj
    exact congrArg (fun u : Circle=>(u:ℂ)) hj'
  have hj0 : j≠⟨0,hn0⟩:=by
    intro hjzero
    apply hne
    apply IsometryEquiv.ext
    intro z
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.fixed_center_coordinate_injective (standardHeckeCorner n hn)
    change heckeCornerCoordinate _ ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL n)^m) z)=
      heckeCornerCoordinate _ z
    rw [heckeCornerCoordinate_product_power,hjc,hjzero]
    simp
  have hdis :=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotation_openPlaneSector_finite_disjoint n hn0 hj0
  have hdis' : Disjoint
      ((fun w : ℂ=>(_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n^j.val:Circle)*w) '' _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n)
      (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n):=by
    simpa using hdis
  apply disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ hz
  apply disjoint_left.mp hdis'
  · refine ⟨heckeCornerCoordinate (standardHeckeCorner n hn) x,hx,?_⟩
    change (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n^j.val:Circle)*heckeCornerCoordinate (standardHeckeCorner n hn) x=
      heckeCornerCoordinate (standardHeckeCorner n hn) ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL n)^m) x)
    rw [heckeCornerCoordinate_product_power,hjc]
  · exact hz

theorem heckePingPongSector_compl_positive (n : ℕ) (hn : 3≤n) (z : ℍ)
    (hz : z∉heckePingPongSector n hn) : 0<z.re := by
  by_contra he
  exact hz (heckePingPongSector_contains_nonpositive n hn z (le_of_not_gt he))

theorem modularInversion_positive_to_negative (z : ℍ) (hz : 0<z.re) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL z).re<0 := by
  change ((modularInversionSL • z:ℍ):ℂ).re<0
  rw [modularInversionSL_action_coe]
  simp only [Complex.div_re,Complex.neg_re,Complex.one_re,Complex.neg_im,Complex.one_im,
    zero_mul,neg_zero,zero_div,add_zero,neg_mul,one_mul,UpperHalfPlane.coe_re]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hz) (Complex.normSq_pos.mpr z.ne_zero)

theorem modularInversion_zpowers_nonidentity (g : ℍ≃ᵢℍ)
    (hg : g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL))
    (hne : g≠1) :
    g=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL := by
  obtain ⟨m,hm,rfl⟩:=finite_order_mem_zpowers_power _ g 2 (by decide)
    modularInversionSL_order_two hg
  have hm' : m=0 ∨ m=1:=by omega
  rcases hm' with rfl|rfl
  · exact False.elim (hne (pow_zero _))
  · exact pow_one _


theorem discreteTopology_sup_of_two_pingPong
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {X : Type*} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    (A B : Subgroup G) (P Q U : Set X) (hU : IsOpen U) (hUn : U.Nonempty)
    (hA : ∀g∈A,g≠1→g • Q⊆P) (hB : ∀g∈B,g≠1→g • P⊆Q)
    (hAU : ∀g∈A,g≠1→g • U⊆P) (hBU : ∀g∈B,g≠1→g • U⊆Q)
    (hPU : Disjoint P U) (hQU : Disjoint Q U) : DiscreteTopology (A⊔B : Subgroup G) := by
  let H : Bool→Type _:=fun | false=>A | true=>B
  let : ∀b,Group (H b):=fun | false=>inferInstance | true=>inferInstance
  let f : ∀b,H b→*G:=fun | false=>A.subtype | true=>B.subtype
  let R : Bool→Set X:=fun b=>if b then Q else P
  have hpp : Pairwise fun i j=>∀h : H i,h≠1→f i h • R j⊆R i:=by
    intro i j hij h hh
    cases i <;> cases j
    · exact False.elim (hij rfl)
    · exact hA (h:A).val (h:A).property (fun he=>hh (Subtype.ext he))
    · exact hB (h:B).val (h:B).property (fun he=>hh (Subtype.ext he))
    · exact False.elim (hij rfl)
  have hstart : ∀i (h : H i),h≠1→f i h • U⊆R i:=by
    intro i h hh
    cases i
    · exact hAU (h:A).val (h:A).property (fun he=>hh (Subtype.ext he))
    · exact hBU (h:B).val (h:B).property (fun he=>hh (Subtype.ext he))
  have hgap : ∀i,Disjoint (R i) U:=by
    intro i
    cases i
    · exact hPU
    · exact hQU
  have hrange : (Monoid.CoprodI.lift f).range=A⊔B:=by
    rw [Monoid.CoprodI.range_eq_iSup]
    change (⨆b : Bool,(f b).range)=A⊔B
    rw [iSup_bool_eq]
    change B.subtype.range⊔A.subtype.range=A⊔B
    rw [Subgroup.range_subtype,Subgroup.range_subtype,sup_comm]
  rw [←hrange]
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteTopology_range_of_pingPong_gap f R U hU hUn hpp hstart hgap


theorem standardHeckeGroup_cyclic_sup (n : ℕ) (hn : 3≤n) :
    standardHeckeGroup n (by exact_mod_cast hn)=
      Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL)⊔
        Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL n)) := by
  let S:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL
  let T:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (Real.pi/(n:ℝ))))
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL n)
  have hF : F=T*S:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (_*_)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _
    rw [map_mul]
  rw [standardHeckeGroup_generators,triangleOrderAngle_nat]
  change Subgroup.closure ({T,S}:Set (ℍ≃ᵢℍ))=Subgroup.zpowers S⊔Subgroup.zpowers F
  apply le_antisymm
  · rw [Subgroup.closure_le,Set.insert_subset_iff,Set.singleton_subset_iff]
    have hS : S∈Subgroup.zpowers S⊔Subgroup.zpowers F:=(show Subgroup.zpowers S≤Subgroup.zpowers S⊔Subgroup.zpowers F from le_sup_left) (Subgroup.mem_zpowers S)
    have hFmem : F∈Subgroup.zpowers S⊔Subgroup.zpowers F:=(show Subgroup.zpowers F≤Subgroup.zpowers S⊔Subgroup.zpowers F from le_sup_right) (Subgroup.mem_zpowers F)
    refine ⟨?_,hS⟩
    have hT : T=F*S⁻¹:=by rw [hF];group
    rw [hT]
    exact (Subgroup.zpowers S⊔Subgroup.zpowers F).mul_mem hFmem
      ((Subgroup.zpowers S⊔Subgroup.zpowers F).inv_mem hS)
  · refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) ?_
    apply Subgroup.zpowers_le.mpr
    rw [hF]
    exact (Subgroup.closure ({T,S}:Set (ℍ≃ᵢℍ))).mul_mem
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem standardHeckeGroup_finite_discrete (n : ℕ) (hn : 3≤n) :
    DiscreteTopology (standardHeckeGroup n (by exact_mod_cast hn)) := by
  rw [standardHeckeGroup_cyclic_sup n hn]
  apply discreteTopology_sup_of_two_pingPong _ _
    {z : ℍ | z.re<0} (heckePingPongSector n hn)ᶜ (heckePingPongGap n hn)
    (heckePingPongGap_isOpen n hn) (heckePingPongGap_nonempty n hn)
  · intro g hg hne
    rw [modularInversion_zpowers_nonidentity g hg hne]
    rintro z ⟨x,hx,rfl⟩
    exact modularInversion_positive_to_negative x (heckePingPongSector_compl_positive n hn x hx)
  · intro g hg hne
    rintro z ⟨x,hx,rfl⟩
    intro hz
    exact disjoint_left.mp (heckePingPongSector_disjoint_translate n hn g hg hne)
      ⟨x,heckePingPongSector_contains_nonpositive n hn x hx.le,rfl⟩ hz
  · intro g hg hne
    rw [modularInversion_zpowers_nonidentity g hg hne]
    rintro z ⟨x,hx,rfl⟩
    exact modularInversion_positive_to_negative x hx.2
  · intro g hg hne
    rintro z ⟨x,hx,rfl⟩
    intro hz
    exact disjoint_left.mp (heckePingPongSector_disjoint_translate n hn g hg hne)
      ⟨x,hx.1,rfl⟩ hz
  · apply disjoint_left.mpr
    intro x hx hxu
    have hx' : x.re<0:=hx
    have hxp : 0<x.re:=hxu.2
    exact lt_asymm hx' hxp
  · apply disjoint_left.mpr
    intro x hx hxu
    exact hx hxu.1

end LowDimensionalTopology.Geometry.Fuchsian
