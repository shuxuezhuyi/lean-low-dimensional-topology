/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.TwoParabolicNormalForms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem closure_pair_inverse_left {G : Type*} [Group G] (f g : G) :
    Subgroup.closure ({f⁻¹,g} : Set G)=Subgroup.closure ({f,g} : Set G) := by
  rw [←Set.singleton_union,←Set.singleton_union,Subgroup.closure_union,
    Subgroup.closure_union,Subgroup.closure_singleton_inv]

theorem closure_pair_inverse_right {G : Type*} [Group G] (f g : G) :
    Subgroup.closure ({f,g⁻¹} : Set G)=Subgroup.closure ({f,g} : Set G) := by
  rw [Set.pair_comm f g⁻¹,closure_pair_inverse_left,Set.pair_comm g f]

theorem twoParabolic_pair_abs (t c : ℝ) :
    Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL |t|),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL |c|)} : Set Mobius.complexMobiusGroup)=
    Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c)} : Set Mobius.complexMobiusGroup) := by
  have ht : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL |t|)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) ∨
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL |t|)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t))⁻¹ := by
    by_cases h : 0≤t
    · exact Or.inl (by rw [abs_of_nonneg h])
    · exact Or.inr (by rw [abs_of_neg (lt_of_not_ge h),canonical_translation_inverse,map_inv])
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL |c|)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c) ∨
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL |c|)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c))⁻¹ := by
    by_cases h : 0≤c
    · exact Or.inl (by rw [abs_of_nonneg h])
    · exact Or.inr (by rw [abs_of_neg (lt_of_not_ge h),←twoParabolicModelSL_inverse,map_inv])
  rcases ht with ht|ht <;> rcases hc with hc|hc <;>
    rw [ht,hc] <;> simp only [closure_pair_inverse_left,closure_pair_inverse_right]

theorem twoParabolic_pair_dilation (k : ℝ) (hk : 0<k) (t c : ℝ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk))
      (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c)} : Set Mobius.complexMobiusGroup))=
    Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (k*t)),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL (c/k))} : Set Mobius.complexMobiusGroup) := by
  change (Subgroup.closure _).map _=_
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation]
  have ht : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)*
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk))⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (k*t)) := by
    rw [←map_inv,←map_mul,←map_mul,verticalDilationSL_conjugate_translation_matrix]
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c)*
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk))⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL (c/k)) := by
    rw [←map_inv,←map_mul,←map_mul,verticalDilationSL_conjugate_twoParabolicModel]
  rw [ht,hc]

theorem realSL_conjugate_of_signed_matrix (q A C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : q*A*q⁻¹=C ∨ q*A*q⁻¹= -C) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C := by
  rw [←map_inv,←map_mul,←map_mul]
  rcases h with h|h
  · rw [h]
  · rw [h,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg]

theorem twoParabolic_signed_normal_form_trace (A B q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (t c : ℝ)
    (hA : q*A*q⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t ∨ q*A*q⁻¹= -_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)
    (hB : q*B*q⁻¹=twoParabolicModelSL c ∨ q*B*q⁻¹= -twoParabolicModelSL c) :
    Matrix.trace (A*B*A⁻¹*B⁻¹).val=2+(t*c)^2 := by
  rw [parabolic_normalization_commutator_trace A B q t hA,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_commutator_trace]
  rcases hB with h|h
  · simp [h,twoParabolicModelSL]
  · simp [h,twoParabolicModelSL]

/-- The original generated group has a genuine unit-translation, positive-parameter normal form. -/
theorem two_parabolic_positive_normal_form (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))) :
    ∃ q : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ c : ℝ, 0<c ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
        (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))=
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c)} : Set Mobius.complexMobiusGroup) ∧
      Matrix.trace (A*B*A⁻¹*B⁻¹).val=2+c^2 := by
  obtain ⟨q,t,c,ht,hc,ha,hb⟩ := two_parabolic_simultaneous_normal_form A B hA hB hne
  have hq : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
        (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))=
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c)} : Set Mobius.complexMobiusGroup) := by
    change (Subgroup.closure _).map _=_
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,realSL_conjugate_of_signed_matrix q A _ ha,
      realSL_conjugate_of_signed_matrix q B _ hb]
  let k : ℝ := 1/|t|
  have hk : 0<k := one_div_pos.mpr (abs_pos.mpr ht)
  have hunit : k*|t|=1 := by dsimp only [k];field_simp
  have hcoef : |c|/k=|t*c| := by simp [k,div_eq_mul_inv,abs_mul,mul_comm]
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk*q,|t*c|,abs_pos.mpr (mul_ne_zero ht hc),?_,?_⟩
  · rw [map_mul,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose,hq,←twoParabolic_pair_abs]
    have hd := twoParabolic_pair_dilation k hk |t| |c|
    rwa [hunit,hcoef] at hd
  · rw [sq_abs]
    exact twoParabolic_signed_normal_form_trace A B q t c ha hb

/-- Discreteness and non-elementarity are transported to the actual positive model;
the original Jorgensen bound gives its coefficient bound without an added premise. -/
theorem two_parabolic_discrete_positive_normal_form (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))) :
    ∃ q : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ c : ℝ, 1≤c ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
        (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))=
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c)} : Set Mobius.complexMobiusGroup) ∧
      Matrix.trace (A*B*A⁻¹*B⁻¹).val=2+c^2 ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c)} : Set Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c)} : Set Mobius.complexMobiusGroup)) := by
  obtain ⟨q,c,hc,hq,htr⟩ := two_parabolic_positive_normal_form A B hA hB hne
  have ht := parabolic_commutator_trace_lower_three A B hA hd hne
  have hc1 : 1≤c := by rw [htr] at ht;nlinarith
  refine ⟨q,c,hc1,hq,htr,?_,?_⟩
  · let H := Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)
    let : DiscreteTopology H := hd
    have h := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H
    change _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H) at h
    dsimp only [H] at h
    rwa [hq] at h
  · have h := hne.conjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
      (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))) at h
    rwa [hq] at h

/-- The exceptional range in the original theorem is exactly the genuine model range [1,4). -/
theorem twoParabolic_small_trace_parameter (c : ℝ) (hc : 1≤c) :
    2+c^2<18 ↔ c<4 := by
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

end LowDimensionalTopology.Geometry.Fuchsian
