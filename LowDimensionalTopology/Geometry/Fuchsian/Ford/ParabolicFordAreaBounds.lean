/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.OneParabolicUnitNormalForms
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.ParabolicFiniteArea
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.NativeTriangleTransport
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped UpperHalfPlane OnePoint MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

def fordCircleAngle (c : ℝ) : ℝ := Real.arccos (c/2)

theorem fordCircleAngle_bounds (c : ℝ) (hc : 0<c) (h2 : c<2) :
    0<fordCircleAngle c ∧ fordCircleAngle c<Real.pi/2 := by
  exact ⟨Real.arccos_pos.mpr (by linarith),Real.arccos_lt_pi_div_two.mpr (by linarith)⟩

def fordCircleChart (c : ℝ) (hc : 0<c) : ℍ≃ᵢℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (1/2)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (1/c) (one_div_pos.mpr hc))

theorem fordCircleChart_inverse_coe (c : ℝ) (hc : 0<c) (z : ℍ) :
    ((fordCircleChart c hc).symm z:ℂ)=(c:ℂ)*((z:ℂ)-1/2) := by
  change ((((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
    (1/2)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (1/c) (one_div_pos.mpr hc))⁻¹) •
    z:ℍ):ℂ)=_
  rw [mul_inv_rev,mul_smul,verticalDilationSL_inverse_coe,←canonical_translation_inverse,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
  push_cast
  rw [div_div_eq_mul_div,div_one]
  ring

theorem fordCircleChart_inverse_re (c : ℝ) (hc : 0<c) (z : ℍ) :
    ((fordCircleChart c hc).symm z).re=c*(z.re-1/2) := by
  have h:=congrArg Complex.re (fordCircleChart_inverse_coe c hc z)
  norm_num [Complex.mul_re,Complex.sub_re,Complex.div_re] at h
  exact h

def centeredCircleFordRegion (c : ℝ) : Set ℍ :=
  {z | 0<z.re ∧ z.re<1 ∧ 1<‖(c:ℂ)*((z:ℂ)-1/2)‖}

theorem centeredCircleFordRegion_eq_triangle_image (c : ℝ) (hc : 0<c) (h2 : c<2) :
    centeredCircleFordRegion c=(fordCircleChart c hc) ''
      (prescribedIdealHTriangle (fordCircleAngle c) (fordCircleAngle c)
        (fordCircleAngle_bounds c hc h2).1.le (fordCircleAngle_bounds c hc h2).1.le
        (by have h:=(fordCircleAngle_bounds c hc h2).2;linarith)).interior := by
  let θ:=fordCircleAngle c
  have hθ:=fordCircleAngle_bounds c hc h2
  have hs:θ+θ<Real.pi:=by change fordCircleAngle c+fordCircleAngle c<Real.pi;linarith [hθ.2]
  let T:=prescribedIdealHTriangle θ θ hθ.1.le hθ.1.le hs
  let E:=fordCircleChart c hc
  have hcos:Real.cos θ=c/2:=Real.cos_arccos (by linarith) (by linarith)
  change centeredCircleFordRegion c=E '' T.interior
  ext z
  constructor
  · rintro ⟨hz0,hz1,hzN⟩
    refine ⟨E.symm z,?_,E.apply_symm_apply z⟩
    rw [prescribedIdealHTriangle_mem_interior_iff,hcos]
    have hr:=fordCircleChart_inverse_re c hc z
    have he:=fordCircleChart_inverse_coe c hc z
    refine ⟨⟨by nlinarith,by nlinarith⟩,?_⟩
    have hn:1<‖(E.symm z:ℂ)‖:=by rwa [he]
    nlinarith [norm_nonneg (E.symm z:ℂ)]
  · rintro ⟨w,hw,rfl⟩
    rw [prescribedIdealHTriangle_mem_interior_iff,hcos] at hw
    have hr:=fordCircleChart_inverse_re c hc (E w)
    have he:=fordCircleChart_inverse_coe c hc (E w)
    change (E.symm (E w)).re=c*((E w).re-1/2) at hr
    rw [E.symm_apply_apply] at hr
    change ((E.symm (E w):ℍ):ℂ)=(c:ℂ)*((E w:ℂ)-1/2) at he
    rw [E.symm_apply_apply] at he
    change 0<(E w).re ∧ (E w).re<1 ∧ 1<‖(c:ℂ)*((E w:ℂ)-1/2)‖
    refine ⟨by nlinarith [hw.1.1],by nlinarith [hw.1.2],?_⟩
    rw [←he]
    nlinarith [norm_nonneg (w:ℂ)]

theorem centeredCircleFordRegion_volume (c : ℝ) (hc : 0<c) (h2 : c<2) :
    volume (centeredCircleFordRegion c)=ENNReal.ofReal (Real.pi-2*fordCircleAngle c) := by
  rw [centeredCircleFordRegion_eq_triangle_image c hc h2,native_isometry_volume_image,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.area_eq_angle_defect]
  have hs:fordCircleAngle c+fordCircleAngle c<Real.pi:=by
    have h:=(fordCircleAngle_bounds c hc h2).2
    linarith
  have ha:=prescribedIdealHTriangle_angles (fordCircleAngle c) (fordCircleAngle c)
    (fordCircleAngle_bounds c hc h2).1.le (fordCircleAngle_bounds c hc h2).1.le hs
  rw [ha.1,ha.2.1,ha.2.2]
  congr 1
  ring


theorem centeredCircleFordRegion_volume_lt_pi (c : ℝ) (hc : 0<c) (h2 : c<2) :
    volume (centeredCircleFordRegion c)<ENNReal.ofReal Real.pi := by
  rw [centeredCircleFordRegion_volume c hc h2]
  exact (ENNReal.ofReal_lt_ofReal_iff Real.pi_pos).mpr (by
    have h:=(fordCircleAngle_bounds c hc h2).1
    linarith)

theorem parabolicFordStrictStrip_subset_centeredCircle (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hc : B 1 0≠0) (hd : B 1 1= -(B 1 0)/2) :
    parabolicFordStrictStrip H⊆centeredCircleFordRegion |B 1 0| := by
  intro z hz
  have hN : 1<‖_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator B z‖:=hz.2.2 B hB hc
  have he : _root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator B z=(B 1 0:ℂ)*((z:ℂ)-1/2) := by
    change (B 1 0:ℂ)*(z:ℂ)+(B 1 1:ℂ)=_
    rw [hd]
    push_cast
    ring
  have hnorm : ‖_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator B z‖=‖((|B 1 0|:ℝ):ℂ)*((z:ℂ)-1/2)‖ := by
    rw [he,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
      Real.norm_eq_abs,abs_abs]
  exact ⟨hz.1,hz.2.1,by rwa [←hnorm]⟩

theorem centered_small_coefficient_Ford_area_lt_pi (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hc : B 1 0≠0) (h2 : |B 1 0| < 2) (hd : B 1 1= -(B 1 0)/2) :
    volume (parabolicFordDomain H)<ENNReal.ofReal Real.pi := by
  apply lt_of_le_of_lt (measure_mono ((parabolicFordDomain_subset_strictStrip H).trans
    (parabolicFordStrictStrip_subset_centeredCircle H B hB hc hd)))
  exact centeredCircleFordRegion_volume_lt_pi _ (abs_pos.mpr hc) h2


theorem hTranslationSL_conjugate_lower_row (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (s : ℝ) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
      s*B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s)⁻¹) 1 0=B 1 0 ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s*B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s)⁻¹) 1 1=B 1 1-s*B 1 0 := by
  constructor <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,Matrix.vecMul,dotProduct]
  ring

theorem small_coefficient_fundamental_area_lt_pi (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hc : B 1 0≠0) (h2 : |B 1 0| < 2) :
    ∃q : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∃Pq : HalfPlaneFuchsianGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H),
      letI:=Pq.nativeAction
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H) ℍ volume
        (parabolicFordDomain (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H)) ∧
      volume (parabolicFordDomain (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H))<ENNReal.ofReal Real.pi := by
  let s:ℝ:=B 1 1/B 1 0+1/2
  let q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s
  let C:=q*B*q⁻¹
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H
  let Pq:=parabolic_conjugate_halfPlaneData P (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    q) (realSLMobius_image_openHalfPlane q)
  have hC0 : C 1 0=B 1 0:=(hTranslationSL_conjugate_lower_row B s).1
  have hC1 : C 1 1= -(B 1 0)/2 := by
    rw [show C 1 1=B 1 1-s*B 1 0 from (hTranslationSL_conjugate_lower_row B s).2]
    dsimp only [s]
    field_simp [hc]
    ring
  have hTq : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈K := by
    apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ H _).mpr
    refine ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1,hT,?_⟩
    rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation,←map_inv,←map_mul,←map_mul]
    exact congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hTranslationSL_conjugate_translation
      s 1)
  have hCq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈K := by
    apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ H _).mpr
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,hB,by simp only [C,map_mul,map_inv]⟩
  have hcn : C 1 0≠0:=by rwa [hC0]
  have hc2 : |C 1 0| < 2:=by rwa [hC0]
  have hcenter : C 1 1= -(C 1 0)/2 := by rw [hC1,hC0]
  have hstab:=primitive_unit_stabilizer_of_lowerLeft K Pq hTq C hCq hcn hc2
  refine ⟨q,Pq,parabolicFordDomain_fundamental Pq hTq hstab,?_⟩
  exact centered_small_coefficient_Ford_area_lt_pi K C hCq hcn hc2 hcenter

theorem one_parabolic_small_trace_fundamental_area_lt_pi
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hsmall : Matrix.trace (A*B*A⁻¹*B⁻¹).val < 6) :
    ∃q : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∃Pq : HalfPlaneFuchsianGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
        (Subgroup.closure
          ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
            _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
            _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))),
      letI:=Pq.nativeAction
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
        (Subgroup.closure
          ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
            _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
            _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) ℍ volume
        (parabolicFordDomain (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
          (Subgroup.closure
            ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
              _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
              _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))) ∧
      volume (parabolicFordDomain
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
        (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))))<ENNReal.ofReal Real.pi := by
  obtain ⟨q₀,hG,_htr,hc1,hc2,_hstab⟩:=one_parabolic_small_trace_primitive_unit_normal_form A B hA hd hne hsmall
  let C:=q₀*B*q₀⁻¹
  let K:=Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hdK : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K := by
    let : DiscreteTopology (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=hd
    have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q₀)
      (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))
    change _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q₀)
      (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) at h
    rwa [hG] at h
  have P:=realSL_pair_halfPlaneData (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1) C hdK
  have hT:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈K:=by
    have h:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)∈K:=Subgroup.subset_closure (by simp)
    simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation] using h
  have hC:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈K:=Subgroup.subset_closure (by simp)
  have hcn:C 1 0≠0:=by intro h;change 1≤|C 1 0| at hc1;rw [h,abs_zero] at hc1;norm_num at hc1
  obtain ⟨q₁,Pq,hFD,harea⟩:=small_coefficient_fundamental_area_lt_pi K P hT C hC hcn hc2
  refine ⟨q₁*q₀,?_⟩
  rw [map_mul,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose,hG]
  exact ⟨Pq,hFD,harea⟩

end LowDimensionalTopology.Geometry.Fuchsian
