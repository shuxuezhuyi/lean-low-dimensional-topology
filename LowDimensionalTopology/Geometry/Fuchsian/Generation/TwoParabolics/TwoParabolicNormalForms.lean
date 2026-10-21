/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicTraceBounds
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

def twoParabolicModelSL (c : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![1,0;c,1],by norm_num⟩

theorem twoParabolicModelSL_inverse (c : ℝ) :
    (twoParabolicModelSL c)⁻¹=twoParabolicModelSL (-c) := by
  apply inv_eq_of_mul_eq_one_left
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoParabolicModelSL,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]

theorem twoParabolicModelSL_commutator_trace (c : ℝ) :
    Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1*twoParabolicModelSL c*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)⁻¹*
      (twoParabolicModelSL c)⁻¹).val=2+c^2 := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_commutator_trace]
  simp [twoParabolicModelSL]

theorem twoParabolicModelSL_parabolic (c : ℝ) (hc : c≠0) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c)) := by
  have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c)≠1 := by
    intro he
    have h1 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius 1:=by simpa only [map_one] using he
    rcases (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_iff_sign _ _).mp h1 with h|h
    all_goals
      have h0:=congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) ℝ=>A 1 0) h
      have hz : c=0:=by
        norm_num [twoParabolicModelSL] at h0
        linarith
      exact hc hz
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff _ hn).mpr
  norm_num [twoParabolicModelSL,Matrix.trace_fin_two]

/-- A genuine horizontal translation puts a trace-two parabolic with nonzero
lower-left coefficient into the exact lower-unipotent matrix form. -/
theorem parabolic_trace_two_centering (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (htr : Matrix.trace B.val=2) (hc : B 1 0≠0) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL ((1-B 0 0)/B 1 0)*B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL ((1-B 0 0)/B 1 0))⁻¹=
      twoParabolicModelSL (B 1 0) := by
  have ht : B 0 0+B 1 1=2:=by simpa only [Matrix.trace_fin_two] using htr
  have hd : B 1 1=2-B 0 0:=by linarith
  have hdet : B 0 0*B 1 1-B 0 1*B 1 0=1:=by
    simpa only [Matrix.det_fin_two] using B.det_coe
  have hbc : B 0 1*B 1 0= -(B 0 0-1)^2:=by
    rw [hd] at hdet
    nlinarith [hdet]
  apply (mul_inv_eq_iff_eq_mul).mpr
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,twoParabolicModelSL,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply,Fin.sum_univ_two]
  all_goals field_simp [hc]
  all_goals nlinarith [hbc,hd]

/-- Both possible lifts of a parabolic admit a genuine horizontal centering. -/
theorem parabolic_lower_unipotent_normal_form (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) (hc : B 1 0≠0) :
    ∃ s c : ℝ, c≠0 ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s*B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s)⁻¹=twoParabolicModelSL c ∨
       _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s*B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s)⁻¹= -twoParabolicModelSL c) := by
  have ht := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff B hB.1).mp hB
  by_cases hp : Matrix.trace B.val=2
  · exact ⟨(1-B 0 0)/B 1 0,B 1 0,hc,Or.inl (parabolic_trace_two_centering B hp hc)⟩
  · have hm : Matrix.trace (-B).val=2 := by
      simp only [Matrix.SpecialLinearGroup.coe_neg,Matrix.trace_neg]
      have hf : (Matrix.trace B.val-2)*(Matrix.trace B.val+2)=0 := by nlinarith [ht]
      rcases mul_eq_zero.mp hf with h|h
      · exact False.elim (hp (by linarith))
      · linarith
    have hcn : (-B) 1 0≠0 := by simpa using hc
    have he := parabolic_trace_two_centering (-B) hm hcn
    refine ⟨(1-(-B) 0 0)/(-B) 1 0,(-B) 1 0,hcn,Or.inr ?_⟩
    have hn : -(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL ((1-(-B) 0 0)/(-B) 1 0)*B*
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL ((1-(-B) 0 0)/(-B) 1 0))⁻¹)=
        twoParabolicModelSL ((-B) 1 0) := by
      simpa only [mul_neg,neg_mul] using he
    exact neg_eq_iff_eq_neg.mp hn

/-- Horizontal centering preserves the original first parabolic translation. -/
theorem hTranslationSL_conjugate_translation (s t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t := by
  rw [←canonical_translation_inverse]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Two original parabolics with a non-elementary generated group have simultaneous
actual real matrix normal forms; neither normalizer nor coefficient is assumed. -/
theorem two_parabolic_simultaneous_normal_form (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))) :
    ∃ q : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ t c : ℝ, t≠0 ∧ c≠0 ∧
      (q*A*q⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t ∨ q*A*q⁻¹= -_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) ∧
      (q*B*q⁻¹=twoParabolicModelSL c ∨ q*B*q⁻¹= -twoParabolicModelSL c) := by
  obtain ⟨q,t,ht,hnorm⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hA
  have hprojA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) := by
    rw [←map_inv,←map_mul,←map_mul]
    rcases hnorm with he|he
    · rw [he]
    · rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg]
  have hprojB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹) := by simp only [map_mul,map_inv]
  have hnQ : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)} : Set Mobius.complexMobiusGroup)) := by
    have h := hne.conjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,hprojA,hprojB] at h
    exact h
  have hc := translation_hyperbolic_lowerLeft_nezero t (q*B*q⁻¹) hnQ
  have hp : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)) := by
    rw [←hprojB]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q,rfl⟩)).mp hB
  obtain ⟨s,c,hc0,hcenter⟩ := parabolic_lower_unipotent_normal_form (q*B*q⁻¹) hp hc
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s*q,t,c,ht,hc0,?_,?_⟩
  · have hassoc : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s*q)*A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s*q)⁻¹=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s*(q*A*q⁻¹)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s)⁻¹ := by group
    rw [hassoc]
    rcases hnorm with he|he
    · exact Or.inl (by rw [he,hTranslationSL_conjugate_translation])
    · exact Or.inr (by rw [he,mul_neg,neg_mul,hTranslationSL_conjugate_translation])
  · have hassoc : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s*q)*B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s*q)⁻¹=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s*(q*B*q⁻¹)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s)⁻¹ := by group
    simpa only [hassoc] using hcenter

/-- The simultaneous matrix normalizer conjugates the original generated group. -/
theorem two_parabolic_generated_signed_normal_form (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))) :
    ∃ q : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ t c : ℝ, t≠0 ∧ c≠0 ∧
      (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)).map
        (MulAut.conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)).toMonoidHom=
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c)} : Set Mobius.complexMobiusGroup) := by
  obtain ⟨q,t,c,ht,hc,hqA,hqB⟩ := two_parabolic_simultaneous_normal_form A B hA hB hne
  refine ⟨q,t,c,ht,hc,?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation]
  have ha : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) := by
    rw [←map_inv,←map_mul,←map_mul]
    rcases hqA with he|he
    · rw [he]
    · rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg]
  have hb : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c) := by
    rw [←map_inv,←map_mul,←map_mul]
    rcases hqB with he|he
    · rw [he]
    · rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg]
  rw [ha,hb]

theorem verticalDilationSL_conjugate_translation_matrix (k : ℝ) (hk : 0<k) (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk)⁻¹=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (k*t) := by
  have hs := (Real.sqrt_pos.mpr hk).ne'
  have hsq := Real.sq_sqrt hk.le
  apply (mul_inv_eq_iff_eq_mul).mpr
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply,Fin.sum_univ_two]
  all_goals field_simp [hs]
  all_goals rw [hsq]
  all_goals ring

theorem verticalDilationSL_conjugate_twoParabolicModel (k : ℝ) (hk : 0<k) (c : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk*twoParabolicModelSL c*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk)⁻¹=
      twoParabolicModelSL (c/k) := by
  have hs := (Real.sqrt_pos.mpr hk).ne'
  have hsq := Real.sq_sqrt hk.le
  apply (mul_inv_eq_iff_eq_mul).mpr
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL,twoParabolicModelSL,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply,Fin.sum_univ_two]
  all_goals field_simp [hs,hk.ne']
  all_goals rw [hsq]
  all_goals ring

end LowDimensionalTopology.Geometry.Fuchsian
