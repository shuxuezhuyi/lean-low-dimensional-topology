/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.OneParabolicUnitNormalForms
public import Mathlib.Algebra.Order.Round
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

theorem closure_pair_zpow_mul_left {G : Type*} [Group G] (f g : G) (n : ℤ) :
    Subgroup.closure ({f,g} : Set G)=Subgroup.closure ({f,f^n*g} : Set G) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with hx|hx
    · rw [hx];exact Subgroup.subset_closure (by simp)
    · rw [hx]
      have hf : f∈Subgroup.closure ({f,f^n*g} : Set G):=Subgroup.subset_closure (by simp)
      have hg : f^n*g∈Subgroup.closure ({f,f^n*g} : Set G):=Subgroup.subset_closure (by simp)
      have h:=(Subgroup.closure ({f,f^n*g} : Set G)).mul_mem
        ((Subgroup.closure ({f,f^n*g} : Set G)).zpow_mem hf (-n)) hg
      have he : f^(-n)*(f^n*g)=g:=by group
      rw [he] at h
      exact h
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with hx|hx
    · rw [hx];exact Subgroup.subset_closure (by simp)
    · rw [hx]
      exact (Subgroup.closure ({f,g} : Set G)).mul_mem
        ((Subgroup.closure ({f,g} : Set G)).zpow_mem (Subgroup.subset_closure (by simp)) n)
        (Subgroup.subset_closure (by simp))

theorem unit_translation_trace_reduction (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : B 1 0≠0) :
    ∃n : ℤ, let C:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)*B
      C 1 0=B 1 0 ∧ |Matrix.trace C.val|≤|B 1 0|/2 ∧
        Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)=
        Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup) := by
  let t:=Matrix.trace B.val
  let c:=B 1 0
  let n:ℤ:= -round (t/c)
  refine ⟨n,?_,?_,?_⟩
  · norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  · rw [canonical_translation_mul_trace]
    change |t+(n:ℝ)*c|≤|c|/2
    have he:t+(n:ℝ)*c=(t/c-(round (t/c):ℝ))*c := by
      dsimp only [n]
      push_cast
      field_simp [show c≠0 from hc]
      ring
    rw [he,abs_mul]
    have h:=mul_le_mul_of_nonneg_right (abs_sub_round (t/c)) (abs_nonneg c)
    linarith only [h]
  · have he:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)^n:=by rw [hTranslationSL_zpow];simp
    rw [he,map_mul,map_zpow]
    exact closure_pair_zpow_mul_left _ _ n

theorem realSLMobius_ne_one_of_lowerLeft (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0≠0) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1 := by
  intro he
  have h1:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius 1:=by simpa only [map_one] using he
  rcases (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_iff_sign _ _).mp h1 with h|h
  all_goals
    have h0:=congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) ℝ=>C 1 0) h
    norm_num at h0
    exact hc (by linarith only [h0])

def coefficientInversionSL (c : ℝ) (hc : c≠0) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![0,-1/c;c,0],by simp [Matrix.det_fin_two,hc]⟩

theorem trace_zero_horizontal_centering (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace B.val=0) (hc : B 1 0≠0) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-B 0 0/B 1 0)*B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-B 0 0/B 1 0))⁻¹=
      coefficientInversionSL (B 1 0) hc := by
  have hd:B 1 1= -B 0 0:=by have h:=ht;rw [Matrix.trace_fin_two] at h;linarith only [h]
  have hdet:B 0 0*B 1 1-B 0 1*B 1 0=1:=by
    simpa only [Matrix.det_fin_two] using B.det_coe
  have hbc:B 0 1*B 1 0= -(B 0 0)^2-1:=by rw [hd] at hdet;nlinarith only [hdet]
  apply (mul_inv_eq_iff_eq_mul).mpr
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,coefficientInversionSL,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply,Fin.sum_univ_two]
  all_goals field_simp [hc]
  all_goals nlinarith [hbc,hd]

theorem coefficientInversionSL_abs (c : ℝ) (hc : c≠0) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (coefficientInversionSL c hc)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (coefficientInversionSL |c| (abs_pos.mpr hc).ne') := by
  by_cases hp:0<c
  · simp only [abs_of_pos hp]
  · have hn:c<0:=lt_of_le_of_ne (le_of_not_gt hp) hc
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_iff_sign _ _).mpr
    right
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [coefficientInversionSL,abs_of_neg hn,div_eq_mul_inv]

theorem coefficientInversionSL_conjugate_translation (c : ℝ) (hc : c≠0) :
    coefficientInversionSL c hc*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)*(coefficientInversionSL c hc)⁻¹=
      twoParabolicModelSL (c^2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coefficientInversionSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,twoParabolicModelSL,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals field_simp [hc]

theorem coefficientInversionSL_cosine_parameter
    (H : Subgroup Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (c : ℝ) (hc : 0<c) (hc2 : c<2)
    (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (coefficientInversionSL c hc.ne')∈H) :
    ∃n : ℕ,3≤n ∧ c=2*Real.cos (Real.pi/(n:ℝ)) := by
  let S:=coefficientInversionSL c hc.ne'
  have hSc:S 1 0=c:=rfl
  have hc1:1≤c:=by
    have h:=primitive_translation_shimizu H hd 1 (by norm_num)
      (by simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation] using hT) S hS (by rw [hSc];exact hc.ne')
    simpa only [hSc,one_mul,abs_of_pos hc] using h
  have hLe:twoParabolicCanonicalGroup (c^2)≤H:=by
    apply (Subgroup.closure_le _).mpr
    intro f hf
    simp only [mem_insert_iff,mem_singleton_iff] at hf
    rcases hf with hf|hf
    · rw [hf,_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation]
      exact hT
    · rw [hf,←coefficientInversionSL_conjugate_translation c hc.ne',map_mul,map_mul,map_inv,
        hTranslationSL_neg_one_inverse,map_inv]
      exact H.mul_mem (H.mul_mem hS (H.inv_mem (by simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation] using hT))) (H.inv_mem hS)
  have hdL:=discreteMobius_subgroup_of_le H (twoParabolicCanonicalGroup (c^2)) hd hLe
  have hcSq:1≤c^2:=by nlinarith only [hc1]
  have hc4:c^2<4:=by nlinarith only [hc,hc2]
  obtain ⟨r,hr,_horder,hform⟩:=twoParabolic_small_parameter_classification (c^2) hcSq hc4 hdL
  rcases hform with hform|hform
  · have hrR:(2:ℝ)≤r:=by exact_mod_cast hr
    have hcos:0<Real.cos (Real.pi/(2*(r:ℝ))):=Real.cos_pos_of_mem_Ioo
      ⟨by have hp:0<Real.pi/(2*(r:ℝ)):=by positivity
          linarith [Real.pi_pos],by
        apply (div_lt_iff₀ (by linarith only [hrR]:0<2*(r:ℝ))).mpr
        nlinarith [Real.pi_pos]⟩
    have he:=Real.cos_two_mul (Real.pi/(2*(r:ℝ)))
    rw [show 2*(Real.pi/(2*(r:ℝ)))=Real.pi/(r:ℝ) by ring] at he
    refine ⟨2*r,by omega,?_⟩
    norm_num only [Nat.cast_mul,Nat.cast_ofNat]
    nlinarith only [he,hform,hcos,hc]
  · have hr3:3≤r:=by
      by_contra hn
      have hv:r=2:=by omega
      norm_num [hv,Real.cos_pi] at hform
      nlinarith only [hcSq,hform]
    have hrR:(3:ℝ)≤r:=by exact_mod_cast hr3
    have hcos:0<Real.cos (Real.pi/(r:ℝ)):=Real.cos_pos_of_mem_Ioo
      ⟨by have hp:0<Real.pi/(r:ℝ):=by positivity
          linarith [Real.pi_pos],by
        apply (div_lt_iff₀ (by linarith only [hrR]:0<(r:ℝ))).mpr
        nlinarith [Real.pi_pos]⟩
    have he:=Real.cos_two_mul (Real.pi/(r:ℝ))
    rw [show 2*(Real.pi/(r:ℝ))=2*Real.pi/(r:ℝ) by ring] at he
    exact ⟨r,hr3,by nlinarith only [he,hform,hcos,hc]⟩

theorem coefficientInversionSL_eq_unitHecke (n : ℕ) (hn : 3≤n) :
    coefficientInversionSL (2*Real.cos (Real.pi/(n:ℝ)))
      (hecke_width_pos n (by exact_mod_cast hn)).ne'=
      unitHeckeInversionSL n (by exact_mod_cast hn) := by
  let A:=unitHeckeInversionSL n (by exact_mod_cast hn)
  let c:ℝ:=2*Real.cos (Real.pi/(n:ℝ))
  have hc:c≠0:=(hecke_width_pos n (by exact_mod_cast hn)).ne'
  have ha:A 0 0=0:=unitHeckeInversionSL_upperLeft _ _
  have hd:A 1 1=0:=unitHeckeInversionSL_lowerRight _ _
  have hcl:A 1 0=c:=by
    exact unitHeckeInversionSL_lowerLeft _ _
  have hdet:A 0 0*A 1 1-A 0 1*A 1 0=1:=by
    simpa only [Matrix.det_fin_two] using A.det_coe
  have hb:A 0 1= -1/c:=by
    rw [ha,hd,hcl] at hdet
    apply (eq_div_iff hc).mpr
    nlinarith only [hdet]
  change coefficientInversionSL c hc=A
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [coefficientInversionSL,ha,hd,hcl,hb]

theorem trace_zero_pair_Hecke_model (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace B.val=0) (hc : B 1 0≠0) (h2 : |B 1 0|<2)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))) :
    ∃q : Matrix.SpecialLinearGroup (Fin 2) ℝ,∃n : ℕ,∃hn : 3≤n,
      |B 1 0|=2*Real.cos (Real.pi/(n:ℝ)) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))=
        unitHeckeMobiusGroup n (by exact_mod_cast hn) := by
  let q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-B 0 0/B 1 0)
  let c:=|B 1 0|
  have hc0:0<c:=abs_pos.mpr hc
  let C:=coefficientInversionSL c hc0.ne'
  let K:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup)
  have hG:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))=K := by
    change (Subgroup.closure _).map _=_
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation]
    have hT:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1):=by
      rw [←map_inv,←map_mul,←map_mul]
      exact congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hTranslationSL_conjugate_translation _ _)
    have hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C:=by
      rw [←map_inv,←map_mul,←map_mul]
      exact (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (trace_zero_horizontal_centering B ht hc)).trans
        (coefficientInversionSL_abs _ hc)
    rw [hT,hB]
  have hdK:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K:=by
    let : DiscreteTopology (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)):=hd
    have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))
    change _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) _) at h
    rwa [hG] at h
  have hT:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈K:=by
    rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation]
    exact Subgroup.subset_closure (by simp)
  have hC:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈K:=Subgroup.subset_closure (by simp)
  obtain ⟨n,hn,hcform⟩:=coefficientInversionSL_cosine_parameter K hdK hT c hc0 h2 hC
  refine ⟨q,n,hn,hcform,?_⟩
  rw [hG,unitHeckeMobiusGroup_generators]
  have he:C=unitHeckeInversionSL n (by exact_mod_cast hn):=by
    dsimp only [C]
    simpa only [hcform] using coefficientInversionSL_eq_unitHecke n hn
  change Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup)=_
  rw [he]

end LowDimensionalTopology.Geometry.Fuchsian
