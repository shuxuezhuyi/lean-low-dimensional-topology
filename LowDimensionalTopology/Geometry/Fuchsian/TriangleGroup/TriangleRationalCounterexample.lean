/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleTypeGeometry
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenInequality
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteElementaryGroups
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane MatrixGroups OnePoint
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

/-- Arbitrary genuine real translations have the literal real determinant-one lift. -/
theorem rationalTriangle_translation_projection (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (t:ℂ) := by
  apply mobius_ext_on_halfPlane
  intro z
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe,
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]

/-- Translation and negative reciprocal form a genuinely non-elementary actual Mobius
subgroup whenever the translation is nonzero. -/
theorem rationalTriangle_translation_reciprocal_nonElementary (t : ℝ) (ht : t≠0) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (t:ℂ),_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion} :
      Set Mobius.complexMobiusGroup)) := by
  intro he
  let H:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (t:ℂ),_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion} :Set Mobius.complexMobiusGroup)
  have hf : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (t:ℂ)∈H:=Subgroup.subset_closure (by simp)
  have hg : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion∈H:=Subgroup.subset_closure (by simp)
  have hp:= (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff (t:ℂ)).mpr (by exact_mod_cast ht)
  obtain ⟨a,ha,hall⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.elementary_parabolic_common_fixedPoint H he _ hf hp
  have hai : a=∞:=((ha ∞).mp (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty _)).symm
  have hfix:=hall ⟨_,hg⟩
  rw [hai,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion_infty] at hfix
  exact (OnePoint.coe_ne_infty (0:ℂ)) hfix

/-- The exact trace defect of the genuine translation/negative-reciprocal pair. -/
theorem rationalTriangle_translation_reciprocal_defect (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenDefect (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (t:ℂ)) _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion=t^2 := by
  let A:=Matrix.SpecialLinearGroup.map Complex.ofRealHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)
  have hA : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (t:ℂ):=
    rationalTriangle_translation_projection t
  have hs : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (t:ℂ))=4 := by
    rw [←rationalTriangle_translation_projection,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace]
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.trace_fin_two]
  have hc : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (t:ℂ)) _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion=
      2+(t:ℂ)^2 := by
    change _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (t:ℂ))
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversionLift)=_
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace_representatives _ _ A _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversionLift hA rfl]
    change Matrix.trace ((A.val*_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversionLift.val)*
      Matrix.adjugate A.val*Matrix.adjugate _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversionLift.val)=_
    norm_num [A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversionLift,Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.adjugate_fin_two,Matrix.mul_apply,
      Fin.sum_univ_two,Matrix.trace_fin_two]
    ring
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenDefect,hs,hc]
  simp only [sub_self,norm_zero,zero_add,add_sub_cancel_left,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

/-- A positive translation shorter than one gives a nondiscrete genuine subgroup;
this is a direct consequence of the proved sharp Jorgensen inequality. -/
theorem rationalTriangle_translation_reciprocal_not_discrete (t : ℝ) (ht : 0<t) (ht1 : t<1) :
    ¬_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (t:ℂ),_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion} :
      Set Mobius.complexMobiusGroup)) := by
  intro hd
  have hb:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.one_le_jorgensenDefect_of_discrete_nonElementary _ _ hd (rationalTriangle_translation_reciprocal_nonElementary t ht.ne')
  rw [rationalTriangle_translation_reciprocal_defect] at hb
  nlinarith

/-- The global Mobius image of a genuinely discrete native conformal subgroup is discrete
in the actual boundary-uniform Mobius topology. -/
theorem native_conformal_subgroup_image_discrete (H : Subgroup (ℍ≃ᵢℍ))
    (hH : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) [DiscreteTopology H] :
    _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (nativeConformalSubgroupMobiusHom H hH).range := by
  have hh:=(nativeConformalSubgroupMobiusHom_isometry H hH).isEmbedding.isInducing.isDiscrete_range
  exact isDiscrete_iff_discreteTopology.mp hh

/-- The two noncircular sides of the actual prescribed ideal triangle are literal vertical lines. -/
theorem prescribedIdealHTriangle_sideA (α β : ℝ) (hα : 0≤α) (hβ : 0≤β)
    (hsum : α+β<Real.pi) :
    (prescribedIdealHTriangle α β hα hβ hsum).sideLineA=.vertical (Real.cos β) := by
  let T:=prescribedIdealHTriangle α β hα hβ hsum
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint∈T.sideLineA.closedCarrier:=
    ((T.toDiscTriangle.sideLineA.closedCarrier_cayley_mem _).mp T.toDiscTriangle.c_mem_sideLineA)
  have hb : T.b∈T.sideLineA.closedCarrier:=
    ((T.toDiscTriangle.sideLineA.closedCarrier_cayley_mem _).mp T.toDiscTriangle.b_mem_sideLineA)
  obtain ⟨x,hx⟩:=T.sideLineA.eq_vertical_of_infty_ideal
    ((T.sideLineA.closedCarrier_mem_ideal_iff _ _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint_ideal).mp hc)
  rw [hx] at hb
  have hr:=closed_vertical_point_re x T.b (⟨Real.cos β,Real.sin β⟩:ℂ) rfl hb
  change Real.cos β=x at hr
  exact hx.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical hr.symm)

theorem prescribedIdealHTriangle_sideB (α β : ℝ) (hα : 0≤α) (hβ : 0≤β)
    (hsum : α+β<Real.pi) :
    (prescribedIdealHTriangle α β hα hβ hsum).sideLineB=.vertical (-Real.cos α) := by
  let T:=prescribedIdealHTriangle α β hα hβ hsum
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint∈T.sideLineB.closedCarrier:=
    ((T.toDiscTriangle.sideLineB.closedCarrier_cayley_mem _).mp T.toDiscTriangle.c_mem_sideLineB)
  have ha : T.a∈T.sideLineB.closedCarrier:=
    ((T.toDiscTriangle.sideLineB.closedCarrier_cayley_mem _).mp T.toDiscTriangle.a_mem_sideLineB)
  obtain ⟨x,hx⟩:=T.sideLineB.eq_vertical_of_infty_ideal
    ((T.sideLineB.closedCarrier_mem_ideal_iff _ _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint_ideal).mp hc)
  rw [hx] at ha
  have hr:=closed_vertical_point_re x T.a (⟨-Real.cos α,Real.sin α⟩:ℂ) rfl ha
  change -Real.cos α=x at hr
  exact hx.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical hr.symm)

/-- An explicit genuine ideal triangle whose three angles are rational multiples of pi. -/
def rationalNondiscreteTriangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle:=
  prescribedIdealHTriangle (Real.pi/2) (2*Real.pi/5)
    (by positivity) (by positivity) (by linarith only [Real.pi_pos])

theorem rationalNondiscreteTriangle_angles :
    rationalNondiscreteTriangle.alpha=Real.pi/2 ∧
      rationalNondiscreteTriangle.beta=2*Real.pi/5 ∧ rationalNondiscreteTriangle.gamma=0 :=
  prescribedIdealHTriangle_angles _ _ _ _ _

theorem rationalNondiscreteTriangle_parameter_bounds :
    0<2*Real.cos (2*Real.pi/5) ∧ 2*Real.cos (2*Real.pi/5)<1 := by
  have hp:=Real.pi_pos
  have hpos:=Real.cos_pos_of_mem_Ioo (show 2*Real.pi/5∈Ioo (-(Real.pi/2)) (Real.pi/2) by
    constructor <;> linarith)
  have hlt:=Real.cos_lt_cos_of_nonneg_of_le_pi (show 0≤Real.pi/3 by positivity)
    (show 2*Real.pi/5≤Real.pi by linarith) (show Real.pi/3<2*Real.pi/5 by linarith)
  rw [Real.cos_pi_div_three] at hlt
  constructor <;> linarith

/-- The first pair of actual side reflections is the short genuine real translation. -/
theorem rationalNondiscreteTriangle_first_matrix :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL rationalNondiscreteTriangle.sideLineA rationalNondiscreteTriangle.sideLineB=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (2*Real.pi/5)) := by
  rw [rationalNondiscreteTriangle,prescribedIdealHTriangle_sideA,prescribedIdealHTriangle_sideB,
    Real.cos_pi_div_two,neg_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.mul_apply,Fin.sum_univ_two]

/-- The second pair of actual side reflections is negative reciprocal, up to the harmless lift sign. -/
theorem rationalNondiscreteTriangle_second_matrix :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL rationalNondiscreteTriangle.sideLineC rationalNondiscreteTriangle.sideLineB=
      -modularInversionSL := by
  rw [rationalNondiscreteTriangle,prescribedIdealHTriangle_circle,prescribedIdealHTriangle_sideB,
    Real.cos_pi_div_two,neg_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflectionMatrix,modularInversionSL,
      Matrix.SpecialLinearGroup.coe_neg,Matrix.mul_apply,Fin.sum_univ_two]

/-- The actual conformal group of this rational-angle triangle is not discrete. -/
theorem rationalNondiscreteTriangle_conformal_not_discrete :
    ¬DiscreteTopology (triangleConformalGroup rationalNondiscreteTriangle) := by
  intro hd
  let H:=triangleConformalGroup rationalNondiscreteTriangle
  let : DiscreteTopology H:=hd
  let F:=nativeConformalSubgroupMobiusHom H inf_le_right
  have hfirst : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL rationalNondiscreteTriangle.sideLineA
      rationalNondiscreteTriangle.sideLineB)∈H := by
    change _∈triangleConformalGroup rationalNondiscreteTriangle
    rw [←reflectionProductSL_native,triangleConformalGroup_eq_pairProductGroup]
    exact Subgroup.subset_closure (Or.inl rfl)
  have hsecond : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL rationalNondiscreteTriangle.sideLineC
      rationalNondiscreteTriangle.sideLineB)∈H := by
    change _∈triangleConformalGroup rationalNondiscreteTriangle
    rw [←reflectionProductSL_native,triangleConformalGroup_eq_pairProductGroup]
    exact Subgroup.subset_closure (Or.inr (mem_singleton _))
  have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation ((2*Real.cos (2*Real.pi/5):ℝ):ℂ)∈F.range := by
    refine ⟨⟨_,hfirst⟩,?_⟩
    rw [nativeConformalSubgroupMobiusHom_matrix,rationalNondiscreteTriangle_first_matrix,
      rationalTriangle_translation_projection]
  have hJ : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion∈F.range := by
    refine ⟨⟨_,hsecond⟩,?_⟩
    rw [nativeConformalSubgroupMobiusHom_matrix,rationalNondiscreteTriangle_second_matrix,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg,modularInversionSL_projection]
  have himage : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup F.range:=native_conformal_subgroup_image_discrete H inf_le_right
  have hle : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation ((2*Real.cos (2*Real.pi/5):ℝ):ℂ),
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion}:Set Mobius.complexMobiusGroup)≤F.range :=
    (Subgroup.closure_le _).mpr (by intro f hf;rcases hf with rfl|hf;exact hT;exact mem_singleton_iff.mp hf ▸ hJ)
  have hpair:=discreteMobius_subgroup_of_le F.range _ himage hle
  exact rationalTriangle_translation_reciprocal_not_discrete _
    rationalNondiscreteTriangle_parameter_bounds.1 rationalNondiscreteTriangle_parameter_bounds.2 hpair

/-- Both the full genuine reflection group and its genuine conformal subgroup fail to be discrete. -/
theorem rationalNondiscreteTriangle_reflection_not_discrete :
    ¬DiscreteTopology (triangleReflectionGroup rationalNondiscreteTriangle) :=
  fun hd=>rationalNondiscreteTriangle_conformal_not_discrete
    ((triangle_discrete_full_iff_conformal _).mp hd)

/-- Rationality of all three genuine angles does not suffice for discreteness. -/
theorem rational_triangle_angles_not_sufficient : ∃T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle,
    (∃a : ℚ,T.alpha=(a:ℝ)*Real.pi) ∧ (∃b : ℚ,T.beta=(b:ℝ)*Real.pi) ∧
      (∃c : ℚ,T.gamma=(c:ℝ)*Real.pi) ∧
      ¬DiscreteTopology (triangleReflectionGroup T) ∧ ¬DiscreteTopology (triangleConformalGroup T) := by
  refine ⟨rationalNondiscreteTriangle,?_,?_,?_,rationalNondiscreteTriangle_reflection_not_discrete,
    rationalNondiscreteTriangle_conformal_not_discrete⟩
  · exact ⟨1/2,by rw [rationalNondiscreteTriangle_angles.1];push_cast;ring⟩
  · exact ⟨2/5,by rw [rationalNondiscreteTriangle_angles.2.1];push_cast;ring⟩
  · exact ⟨0,by rw [rationalNondiscreteTriangle_angles.2.2];norm_num⟩

end LowDimensionalTopology.Geometry.Fuchsian
