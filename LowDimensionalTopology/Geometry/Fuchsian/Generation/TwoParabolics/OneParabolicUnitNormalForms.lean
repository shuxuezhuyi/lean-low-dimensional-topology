/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.TwoParabolicFuchsianModels
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

theorem one_parabolic_unit_normal_form (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    ∃q : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))=
        Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)} : Set Mobius.complexMobiusGroup) ∧
      Matrix.trace (A*B*A⁻¹*B⁻¹).val=2+((q*B*q⁻¹) 1 0)^2 := by
  obtain ⟨q₀,t,ht,hnorm⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hA
  let B₀:=q₀*B*q₀⁻¹
  let k:ℝ:=1/|t|
  have hk:0<k:=one_div_pos.mpr (abs_pos.mpr ht)
  let D:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk
  let q:=D*q₀
  have hAB:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q₀) (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))=
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B₀} : Set Mobius.complexMobiusGroup) := by
    change (Subgroup.closure _).map _=_
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation]
    have ha:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q₀*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q₀)⁻¹=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t):=realSL_conjugate_of_signed_matrix q₀ A _ hnorm
    have hb:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q₀*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q₀)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B₀ := by
      simp only [B₀,map_mul,map_inv]
    rw [ha,hb]
  have hB : D*B₀*D⁻¹=q*B*q⁻¹ := by dsimp only [B₀,q];group
  have haD:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D)⁻¹=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (k*t)) := by
    rw [←map_inv,←map_mul,←map_mul]
    exact congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (verticalDilationSL_conjugate_translation_matrix k hk t)
  have hbD:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B₀*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹) := by
    rw [←map_inv,←map_mul,←map_mul,hB]
  refine ⟨q,?_,?_⟩
  · change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D*q₀)) _=_
    rw [map_mul,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose,hAB]
    change (Subgroup.closure _).map _=_
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,haD,hbD]
    by_cases hp:0<t
    · have he:k*t=1:=by dsimp only [k];rw [abs_of_pos hp];field_simp
      rw [he]
    · have hn:t<0:=lt_of_le_of_ne (le_of_not_gt hp) ht
      have he:k*t= -1 := by dsimp only [k];rw [abs_of_neg hn];field_simp
      rw [he,hTranslationSL_neg_one_inverse,map_inv,closure_pair_inverse_left]
  · have hc:(q*B*q⁻¹) 1 0=|t| * B₀ 1 0 := by
      rw [←hB]
      change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk*B₀*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk)⁻¹) 1 0=_
      rw [primitive_dilation_lowerLeft]
      dsimp only [k]
      simp only [div_div_eq_mul_div,div_one]
      ring
    rw [parabolic_normalization_commutator_trace A B q₀ t hnorm,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_commutator_trace, hc]
    simp only [mul_pow,sq_abs]
    rfl


theorem realSL_pair_halfPlaneData (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))) :
    HalfPlaneFuchsianGroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)) := by
  have hreal : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range := by
    apply (Subgroup.closure_le _).mpr
    rintro f (rfl|rfl)
    · exact ⟨A,rfl⟩
    · exact ⟨B,rfl⟩
  refine ⟨?_,hd⟩
  intro f
  obtain ⟨C,hC⟩:=hreal f.property
  rw [←hC]
  exact realSLMobius_image_openHalfPlane C

theorem one_parabolic_small_trace_primitive_unit_normal_form
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)))
    (hsmall : Matrix.trace (A*B*A⁻¹*B⁻¹).val < 6) :
    ∃q : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))=
        Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)} : Set Mobius.complexMobiusGroup) ∧
      Matrix.trace (A*B*A⁻¹*B⁻¹).val=2+((q*B*q⁻¹) 1 0)^2 ∧
      1 ≤ |(q*B*q⁻¹) 1 0| ∧ |(q*B*q⁻¹) 1 0| < 2 ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)} : Set Mobius.complexMobiusGroup)) ∞=
        Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) := by
  obtain ⟨q,hq,htr⟩:=one_parabolic_unit_normal_form A B hA
  have hlow:=parabolic_commutator_trace_lower_three A B hA hd hne
  have hc1 : 1 ≤ |(q*B*q⁻¹) 1 0| := by
    nlinarith [sq_abs ((q*B*q⁻¹) 1 0),abs_nonneg ((q*B*q⁻¹) 1 0)]
  have hc2 : |(q*B*q⁻¹) 1 0| < 2 := by nlinarith [sq_abs ((q*B*q⁻¹) 1 0)]
  have hc : (q*B*q⁻¹) 1 0≠0 := by
    intro he
    rw [he,abs_zero] at hc1
    norm_num at hc1
  have hdK : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)} : Set Mobius.complexMobiusGroup)) := by
    let : DiscreteTopology (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)):=hd
    have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
      (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))
    change _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
      (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))) at h
    rwa [hq] at h
  have P:=realSL_pair_halfPlaneData (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1) (q*B*q⁻¹) hdK
  refine ⟨q,hq,htr,hc1,hc2,?_⟩
  apply primitive_unit_stabilizer_of_lowerLeft _ P _ (q*B*q⁻¹) _ hc hc2
  · have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)∈Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)} : Set Mobius.complexMobiusGroup) :=
      Subgroup.subset_closure (by simp)
    simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation] using hm
  · exact Subgroup.subset_closure (by simp)

end LowDimensionalTopology.Geometry.Fuchsian
