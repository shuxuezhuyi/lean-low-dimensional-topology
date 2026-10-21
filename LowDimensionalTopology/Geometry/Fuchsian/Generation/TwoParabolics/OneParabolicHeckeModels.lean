/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.UnitTranslationTraceReduction
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.SmallTraceEllipticOrders
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.FuchsianParabolicTraceBounds
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.NonTriangleParabolicGroups
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups
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

theorem one_parabolic_small_trace_Hecke_model
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)))
    (hsmall : Matrix.trace (A*B*A⁻¹*B⁻¹).val<6) :
    ∃q : Matrix.SpecialLinearGroup (Fin 2) ℝ,∃n : ℕ,∃hn : 3≤n,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))=
        unitHeckeMobiusGroup n (by exact_mod_cast hn) ∧
      Matrix.trace (A*B*A⁻¹*B⁻¹).val=4+2*Real.cos (2*Real.pi/(n:ℝ)) := by
  obtain ⟨q₀,hG,htrace,hc1,hc2,_hstab⟩:=
    one_parabolic_small_trace_primitive_unit_normal_form A B hA hd hne hsmall
  let B₀:=q₀*B*q₀⁻¹
  let K:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B₀} : Set Mobius.complexMobiusGroup)
  have hdK:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K:=by
    let : DiscreteTopology (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)):=hd
    have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q₀)
      (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))
    change _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q₀) _) at h
    rwa [hG] at h
  let P:=realSL_pair_halfPlaneData (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1) B₀ hdK
  have hcn:B₀ 1 0≠0:=by
    intro h
    change 1≤|B₀ 1 0| at hc1
    rw [h,abs_zero] at hc1
    norm_num at hc1
  obtain ⟨k,hcC,htrC,hgen⟩:=unit_translation_trace_reduction B₀ hcn
  let C:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (k:ℝ)*B₀
  have hcCn:C 1 0≠0:=by rwa [hcC]
  have hcC2:|C 1 0|<2:=by rwa [hcC]
  have hT:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈K:=by
    rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation]
    exact Subgroup.subset_closure (by simp)
  have hC:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈K:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B₀} : Set Mobius.complexMobiusGroup)
    rw [hgen]
    apply Subgroup.subset_closure
    simp only [mem_insert_iff,mem_singleton_iff]
    exact Or.inr rfl
  have ht0:Matrix.trace C.val=0:=(realSL_nearest_trace_halfTurn K hdK hT
    (fun f hf=>P.preserves ⟨f,hf⟩) C hC hcCn hcC2 (by rw [show C 1 0=B₀ 1 0 from hcC];exact htrC)).1
  have hdC:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup)):=by
    rwa [←hgen]
  obtain ⟨q₁,n,hn,hcform,hmodel⟩:=trace_zero_pair_Hecke_model C ht0 hcCn hcC2 hdC
  refine ⟨q₁*q₀,n,hn,?_,?_⟩
  · rw [map_mul,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose,hG,hgen]
    exact hmodel
  · have hcoeff:|B₀ 1 0|=2*Real.cos (Real.pi/(n:ℝ)):=by rwa [hcC] at hcform
    have he:=congrArg (fun x:ℝ=>x^2) hcoeff
    rw [sq_abs] at he
    have hdbl:=Real.cos_two_mul (Real.pi/(n:ℝ))
    rw [show 2*(Real.pi/(n:ℝ))=2*Real.pi/(n:ℝ) by ring] at hdbl
    rw [htrace]
    change 2+(B₀ 1 0)^2=_
    nlinarith only [he,hdbl]

theorem fuchsian_one_parabolic_small_trace_Hecke_model
    (f g : Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup)))
    (hsmall : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g).re<6) :
    ∃q : Mobius.complexMobiusGroup,∃n : ℕ,∃hn : 3≤n,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup))=
        unitHeckeMobiusGroup n (by exact_mod_cast hn) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=((4+2*Real.cos (2*Real.pi/(n:ℝ)):ℝ):ℂ) := by
  obtain ⟨q₀,A,B,_hA,_hB,hG,htrace,hAp,hd,hne'⟩:=
    fuchsian_one_parabolic_pair_real_lifts f g D hf hne
  have hs:Matrix.trace (A*B*A⁻¹*B⁻¹).val<6:=by
    rw [htrace,Complex.ofReal_re] at hsmall
    exact hsmall
  obtain ⟨q₁,n,hn,hmodel,htr⟩:=one_parabolic_small_trace_Hecke_model A B hAp hd hne' hs
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q₁*q₀,n,hn,?_,?_⟩
  · rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose,hG]
    exact hmodel
  · rw [htrace,htr]

theorem fuchsian_one_parabolic_nontriangle_trace_ge_six
    (f g : Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup)))
    (hnt : ¬IsMobiusTriangleGroup (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup))) :
    6≤(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g).re := by
  by_contra hn
  obtain ⟨q,n,hn,_hmodel,_htrace⟩:=
    fuchsian_one_parabolic_small_trace_Hecke_model f g D hf hne (lt_of_not_ge hn)
  apply hnt
  apply isMobiusTriangleGroup_of_conjugate _ q
  rw [_hmodel]
  exact unitHeckeMobiusGroup_isTriangle n (by exact_mod_cast hn)

end LowDimensionalTopology.Geometry.Fuchsian
