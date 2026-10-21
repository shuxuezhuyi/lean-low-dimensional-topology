/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicProducts
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenApplications
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual real parabolic matrix. -/
def quarterParabolicSL : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![1,0;1,1],by norm_num⟩

/-- The actual real hyperbolic matrix in the same source example. -/
def quarterHyperbolicSL : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![2,3;1,2],by norm_num [Matrix.det_fin_two]⟩

theorem quarterTranslation_projection :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessTranslation := by
  rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessTranslation_lift]
  change _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection
    (Matrix.SpecialLinearGroup.map Complex.ofRealHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
      1))=_
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem quarterParabolic_projection : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterParabolicSL=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenParabolicPartner := by
  change _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection
    (Matrix.SpecialLinearGroup.map Complex.ofRealHom quarterParabolicSL)=
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenParabolicPartnerLift
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem quarterHyperbolic_word :
    quarterHyperbolicSL=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1*quarterParabolicSL*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quarterHyperbolicSL,quarterParabolicSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]

theorem quarterParabolic_pair_group :
    Subgroup.closure ({
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterParabolicSL} :
      Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup := by
  rw [quarterTranslation_projection,quarterParabolic_projection,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenParabolicPair_group]

theorem quarterHyperbolic_pair_group :
    Subgroup.closure ({
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterHyperbolicSL} :
      Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup := by
  let T:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)
  let U:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterParabolicSL
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterHyperbolicSL
  let K:=Subgroup.closure ({T,F} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hword : F=T*U*T := by
    dsimp [F,T,U]
    rw [quarterHyperbolic_word,map_mul,map_mul]
  have hTU : Subgroup.closure ({T,U} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup :=
    quarterParabolic_pair_group
  rw [←hTU]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro f hf
    rcases Set.mem_insert_iff.mp hf with rfl | hf
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [Set.mem_singleton_iff] at hf
      rw [hf]
      change F∈Subgroup.closure ({T,U} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
      rw [hword]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
        (Subgroup.subset_closure (Set.mem_insert _ _))
  · have hTK : T∈K := Subgroup.subset_closure (Set.mem_insert _ _)
    have hFK : F∈K := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hUK : U∈K := by
      have he : U=T⁻¹*F*T⁻¹ := by rw [hword];group
      rw [he]
      exact K.mul_mem (K.mul_mem (K.inv_mem hTK) hFK) (K.inv_mem hTK)
    exact (Subgroup.closure_le _).mpr (by
      intro f hf
      rcases Set.mem_insert_iff.mp hf with rfl | hf
      · exact hTK
      · exact Set.mem_singleton_iff.mp hf ▸ hUK)

theorem quarterTranslation_parabolic : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) := by
  rw [quarterTranslation_projection]
  exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff 1).mpr one_ne_zero

theorem quarterParabolic_parabolic : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterParabolicSL) := by
  rw [quarterParabolic_projection]
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenParabolicPartner_parabolic

theorem quarterHyperbolic_hyperbolic : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterHyperbolicSL) := by
  have hid : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace 1=4 := by
    have he:=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_specialLinearProjection (1:_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2)
    norm_num [Matrix.trace_fin_two] at he
    exact he
  have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterHyperbolicSL≠1 := by
    intro he
    have ht:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace quarterHyperbolicSL
    rw [he,hid] at ht
    norm_num [quarterHyperbolicSL,Matrix.trace_fin_two] at ht
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ hn).mpr
  norm_num [quarterHyperbolicSL,Matrix.trace_fin_two]

theorem quarterParabolic_action (z : ℍ) :
    ((quarterParabolicSL•z : ℍ):ℂ)=(z:ℂ)/((z:ℂ)+1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [quarterParabolicSL]

theorem quarterHyperbolic_action (z : ℍ) :
    ((quarterHyperbolicSL•z : ℍ):ℂ)=(2*(z:ℂ)+3)/((z:ℂ)+2) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [quarterHyperbolicSL]

theorem quarterParabolic_admissible :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) ∧
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterParabolicSL) ∧
    _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterParabolicSL} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterParabolicSL} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  refine ⟨quarterTranslation_parabolic,quarterParabolic_parabolic,?_,?_⟩
  · rw [quarterParabolic_pair_group];exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup_discrete
  · rw [quarterParabolic_pair_group];exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup_nonElementary

theorem quarterHyperbolic_admissible :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) ∧
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterHyperbolicSL) ∧
    _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterHyperbolicSL} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterHyperbolicSL} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  refine ⟨quarterTranslation_parabolic,quarterHyperbolic_hyperbolic,?_,?_⟩
  · rw [quarterHyperbolic_pair_group];exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup_discrete
  · rw [quarterHyperbolic_pair_group];exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup_nonElementary

theorem quarterParabolic_half_displacement (y : ℝ) (hy : 0<y) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry quarterParabolicSL) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)=y/2 := by
  change Real.sinh (dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)
    (quarterParabolicSL•_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)/2)=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_half_displacement_polynomial]
  have hQ : (quarterParabolicSL 1 0 : ℂ)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy : ℂ)^2+
      ((quarterParabolicSL 1 1 : ℂ)-quarterParabolicSL 0
        0)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy : ℂ)-
        quarterParabolicSL 0 1=(-(y^2):ℝ) := by
    apply Complex.ext <;>
      simp [quarterParabolicSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,pow_two,Complex.mul_re,Complex.mul_im]
  rw [hQ,Complex.norm_real,Real.norm_eq_abs,abs_neg,abs_of_nonneg (sq_nonneg y)]
  change y^2/(2*y)=y/2
  field_simp

theorem quarterHyperbolic_half_displacement (y : ℝ) (hy : 0<y) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry quarterHyperbolicSL) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)=(y^2+3)/(2*y) := by
  change Real.sinh (dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)
    (quarterHyperbolicSL•_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)/2)=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_half_displacement_polynomial]
  have hQ : (quarterHyperbolicSL 1 0 : ℂ)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy : ℂ)^2+
      ((quarterHyperbolicSL 1 1 : ℂ)-quarterHyperbolicSL 0
        0)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy : ℂ)-
        quarterHyperbolicSL 0 1=(-(y^2+3):ℝ) := by
    apply Complex.ext <;>
      simp [quarterHyperbolicSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,pow_two,Complex.mul_re,Complex.mul_im] ; ring
  rw [hQ,Complex.norm_real,Real.norm_eq_abs,abs_neg,
    abs_of_nonneg (by positivity : 0≤y^2+3)]
  rfl

theorem quarterParabolic_product (y : ℝ) (hy : 0<y) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry quarterParabolicSL) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)=1/4 := by
  rw [quarterParabolic_half_displacement]
  change Real.sinh (dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
    1•_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)/2)*(y/2)=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.translation_half_displacement]
  norm_num only [abs_one]
  change 1/(2*y)*(y/2)=1/4
  field_simp
  ring

theorem quarterHyperbolic_product (y : ℝ) (hy : 0<y) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry quarterHyperbolicSL) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)=1/4+3/(4*y^2) := by
  rw [quarterHyperbolic_half_displacement]
  change Real.sinh (dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
    1•_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)/2)*((y^2+3)/(2*y))=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.translation_half_displacement]
  norm_num only [abs_one]
  change 1/(2*y)*((y^2+3)/(2*y))=1/4+3/(4*y^2)
  field_simp
  ring

/-- The parabolic/hyperbolic pair approaches the genuine quarter bound at true points. -/
theorem quarterHyperbolic_approaches (ε : ℝ) (hε : 0<ε) :
    ∃ y : ℝ, ∃ hy : 0<y,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)*
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry quarterHyperbolicSL) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)<1/4+ε := by
  let y:=Real.sqrt (3/(2*ε))
  have hy : 0<y := Real.sqrt_pos.mpr (by positivity)
  have hysq : y^2=3/(2*ε) := Real.sq_sqrt (by positivity)
  have he : 3/(4*y^2)=ε/2 := by
    rw [hysq]
    field_simp
    ring
  refine ⟨y,hy,?_⟩
  rw [quarterHyperbolic_product,he]
  linarith

theorem quarterParabolic_P_exact :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry quarterParabolicSL)=1/4 := by
  apply le_antisymm
  · have he:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_le (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry quarterParabolicSL)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 1 (by norm_num))
    rwa [quarterParabolic_product] at he
  · exact parabolic_pair_displacementP_quarter _ _ quarterTranslation_parabolic
      (Or.inl quarterParabolic_parabolic) quarterParabolic_admissible.2.2.1
      quarterParabolic_admissible.2.2.2

theorem quarterHyperbolic_P_exact :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry quarterHyperbolicSL)=1/4 := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨y,hy,he⟩:=quarterHyperbolic_approaches ε hε
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_le _ _
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)).trans he.le
  · exact parabolic_pair_displacementP_quarter _ _ quarterTranslation_parabolic
      (Or.inr quarterHyperbolic_hyperbolic) quarterHyperbolic_admissible.2.2.1
      quarterHyperbolic_admissible.2.2.2

theorem quarterTriple_group :
    Subgroup.closure ({
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterParabolicSL,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterHyperbolicSL} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro f hf
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl
    · rw [quarterTranslation_projection]
      exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup_generators.1
    · rw [←quarterParabolic_pair_group]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · rw [←quarterHyperbolic_pair_group]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · rw [←quarterParabolic_pair_group]
    apply Subgroup.closure_mono
    intro f hf
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hf ⊢
    exact hf.elim Or.inl (fun he => Or.inr (Or.inl he))

theorem quarterTriple_admissible :
    _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterParabolicSL,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterHyperbolicSL} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterParabolicSL,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius quarterHyperbolicSL} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  rw [quarterTriple_group]
  exact ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup_discrete,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup_nonElementary⟩

end LowDimensionalTopology.Geometry.Fuchsian
