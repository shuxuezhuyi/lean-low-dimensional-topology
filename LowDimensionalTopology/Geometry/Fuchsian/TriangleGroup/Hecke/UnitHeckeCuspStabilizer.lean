/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeSharpHeight
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordRegions
public import LowDimensionalTopology.Geometry.Surfaces.Cusp.ParabolicCusps
public import Mathlib.Algebra.Order.Round
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveCanonicalRegions
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

/-- True positive dilation conjugation rescales the actual lower-left coefficient. -/
theorem primitive_dilation_lowerLeft (k : ℝ) (hk : 0<k) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk*B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk)⁻¹) 1 0=B 1 0/k := by
  have hs : Real.sqrt k≠0:=(Real.sqrt_pos.mpr hk).ne'
  simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.mul_apply,Matrix.adjugate_fin_two,Fin.sum_univ_two,Matrix.vecMul,dotProduct]
  field_simp
  rw [Real.sq_sqrt hk.le]
  ring

/-- A genuine positive translation period gives the normalized Shimizu bound for the actual original discrete group. -/
theorem primitive_translation_shimizu
    (H : Subgroup Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (t : ℝ) (ht : 0<t) (hT : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈H)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hc : B 1 0≠0) :
    1≤t*|B 1 0| := by
  let D:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (1/t) (one_div_pos.mpr ht)
  let q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  let : DiscreteTopology H:=hd
  have hdK : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q H
  have hact (z : ℍ) : (D*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t*D⁻¹) • z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1 • z := by
    have hh:=congrArg (fun f : ℍ≃ᵢℍ=>f z)
      (dilation_conjugate_translation_native (1/t) (one_div_pos.mpr ht) t)
    change D • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t • (D⁻¹ • z))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL ((1/t)*t) • z at hh
    simpa only [mul_smul,one_div_mul_cancel ht.ne'] using hh
  have hproj : q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)*q⁻¹=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D)⁻¹=_
    rw [←map_inv,←map_mul,←map_mul]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_ext_action _ _ hact).trans _root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation
  have hT1 : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈K:=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨_,hT,hproj⟩
  let C:=D*B*D⁻¹
  have hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈K := by
    apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,hB,?_⟩
    simp only [C,q,map_mul,map_inv]
  have hcl : C 1 0=t*B 1 0 := by
    have he:=primitive_dilation_lowerLeft (1/t) (one_div_pos.mpr ht) B
    change C 1 0=B 1 0/(1/t) at he
    rw [he]
    field_simp
  have hcC : C 1 0≠0 := by rw [hcl];exact mul_ne_zero ht.ne' hc
  have hh:=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspShimizu_lowerLeft K hdK hT1 (Matrix.SpecialLinearGroup.map Complex.ofRealHom C)
    hC (by change ((C 1 0:ℝ):ℂ)≠0;exact Complex.ofReal_ne_zero.mpr hcC)
  change 1≤‖(C 1 0:ℂ)‖ at hh
  simpa only [Complex.norm_real,Real.norm_eq_abs,hcl,abs_mul,abs_of_pos ht] using hh



/-- The true projective translation lift respects subtraction. -/
theorem primitive_translation_sub (s t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (s-t))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t))⁻¹ := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hTranslationSLHom (Multiplicative.ofAdd s / Multiplicative.ofAdd t))=_
  rw [map_div,map_div,div_eq_mul_inv]
  rfl

/-- Opposite true translation periods give inverse projective transformations. -/
theorem primitive_translation_neg (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-t))=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t))⁻¹ := by
  have h0 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 0)=1 := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hTranslationSLHom 1)=1
    rw [map_one,map_one]
  simpa only [zero_sub,h0,one_mul] using primitive_translation_sub 0 t

/-- In an actual discrete group with a genuine coefficient below two, every nonzero true translation has period greater than one half. -/
theorem primitive_translation_abs_gt_half
    (H : Subgroup Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hc : B 1 0≠0)
    (hc2 : |B 1 0| < 2)
    (t : ℝ) (ht : t≠0) (hT : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈H) : (1:ℝ)/2 < |t| := by
  have hbound : 1≤|t| * |B 1 0| := by
    rcases lt_or_gt_of_ne ht with hn|hp
    · have hTneg : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-t))∈H := by
        rw [primitive_translation_neg]
        exact H.inv_mem hT
      have hh:=primitive_translation_shimizu H hd (-t) (neg_pos.mpr hn) hTneg B hB hc
      simpa only [abs_of_neg hn] using hh
    · simpa only [abs_of_pos hp] using primitive_translation_shimizu H hd t hp hT B hB hc
  by_contra hnot
  have htupper : |t| * 2≤1 := by linarith only [le_of_not_gt hnot]
  have hprod : |t| * |B 1 0| < |t| * 2:=mul_lt_mul_of_pos_left hc2 (abs_pos.mpr ht)
  linarith only [hbound,hprod,htupper]

/-- The actual unit period and the true below-two coefficient force every actual translation period to be an integer. -/
theorem primitive_translation_integer
    (H : Subgroup Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hT1 : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H) (hc : B 1 0≠0) (hc2 : |B 1 0| < 2)
    (t : ℝ) (hT : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈H) : ∃n : ℤ,t=(n:ℝ) := by
  let n:ℤ:=round t
  have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ))∈H := by
    have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)^n := by rw [hTranslationSL_zpow];simp
    rw [he,map_zpow,_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation]
    exact H.zpow_mem hT1 n
  have hr : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (t-(n:ℝ)))∈H := by
    rw [primitive_translation_sub]
    exact H.mul_mem hT (H.inv_mem hn)
  have hzero : t-(n:ℝ)=0 := by
    by_contra he
    have hh:=primitive_translation_abs_gt_half H hd B hB hc hc2 _ he hr
    have hnear : |t-(n:ℝ)|≤(1:ℝ)/2:=abs_sub_round t
    linarith only [hh,hnear]
  exact ⟨n,sub_eq_zero.mp hzero⟩



/-- The actual discrete unit-period infinity stabilizer has only genuine real translations. -/
theorem primitive_affine_translation
    (H : Subgroup Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H)
    (hfix : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞=∞) :
    ∃t : ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) := by
  have hc : A 1 0=0:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff A).mp hfix
  have hdabs:=_root_.LowDimensionalTopology.Geometry.Fuchsian.discrete_unitTranslation_affine_denominator H hd hT A hA hc
  have hdsq : (A 1 1)^2=1 := by rw [←sq_abs,hdabs];norm_num
  have hdet : A 0 0*A 1 1=1 := by simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using A.det_coe
  have hdne : A 1 1≠0 := right_ne_zero_of_mul_eq_one hdet
  have had : A 0 0=A 1 1:=mul_right_cancel₀ hdne (by nlinarith only [hdet,hdsq])
  have hdsq' : (A 1 1)^2=(1:ℝ)^2:=by simpa using hdsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hdsq' with hd1|hd1
  · have he : A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (A 0 1) := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,hc,had,hd1]
    exact ⟨A 0 1,congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius he⟩
  · have he : A= -_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-A 0 1) := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.SpecialLinearGroup.coe_neg,hc,had,hd1]
    exact ⟨-A 0 1,(congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius he).trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg _)⟩

/-- An actual below-two coefficient certifies the full primitive infinity stabilizer of the actual original group. -/
theorem primitive_unit_stabilizer_of_lowerLeft
    (H : Subgroup Mobius.complexMobiusGroup)
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hc : B 1 0≠0) (hc2 : |B 1 0| < 2) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ∞=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) := by
  apply le_antisymm
  · intro f hf
    obtain ⟨hfH,hfix⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ∞ f).mp hf
    obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL f (P.preserves ⟨f,hfH⟩)
    have hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H:=hA.symm ▸ hfH
    have hAf : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞=∞:=by rw [hA];exact hfix
    obtain ⟨t,ht⟩:=primitive_affine_translation H P.discrete hT A hAH hAf
    have hTt : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈H:=ht ▸ hAH
    obtain ⟨n,hn⟩:=primitive_translation_integer H P.discrete hT B hB hc hc2 t hTt
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨n,?_⟩
    rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation, ←map_zpow, hTranslationSL_zpow,
      mul_one, ←hn, ←ht, hA]
  · apply Subgroup.zpowers_le.mpr
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ∞ _).mpr ⟨hT,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1⟩

/-- The genuine source inversion belongs to the actual whole unit Hecke Mobius group. -/
theorem unitHeckeInversionSL_mem (q : ℕ∞) (hq : 3≤q) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeInversionSL q hq)∈unitHeckeMobiusGroup q hq := by
  apply nativeConformalSubgroupMobiusGroup_matrix_mem
  rw [unitHeckeInversionSL_native,unitHeckeGroup_generators]
  exact Subgroup.subset_closure (by simp)

/-- The source inversion's actual determinant-one coefficient is the true Hecke width. -/
theorem unitHeckeInversionSL_lowerLeft (q : ℕ∞) (hq : 3≤q) :
    unitHeckeInversionSL q hq 1 0=2*Real.cos (triangleOrderAngle q) := by
  unfold unitHeckeInversionSL unitHeckeDilationSL
  rw [primitive_dilation_lowerLeft]
  norm_num [modularInversionSL]

/-- For every finite source Hecke parameter, the actual whole infinity stabilizer is generated by the genuine unit translation. -/
theorem unitHeckeMobiusGroup_infty_stabilizer (n : ℕ) (hn : 3≤n) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer (unitHeckeMobiusGroup n (by exact_mod_cast hn)) ∞=
      Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) := by
  let hnE : (3:ℕ∞)≤n:=by exact_mod_cast hn
  let B:=unitHeckeInversionSL n hnE
  have hc : 0<B 1 0 := by rw [unitHeckeInversionSL_lowerLeft];exact hecke_width_pos n hnE
  have hangle:=hecke_order_angle_bounds n hnE
  have hpos : 0<triangleOrderAngle n := by
    rw [triangleOrderAngle_nat]
    exact div_pos Real.pi_pos (by exact_mod_cast (by omega : 0<n))
  have hcos : Real.cos (triangleOrderAngle n)<1 := by
    have hh:=Real.strictAntiOn_cos (show (0:ℝ)∈Icc 0 Real.pi by simp [Real.pi_pos.le])
      (show triangleOrderAngle n∈Icc 0 Real.pi by constructor <;> linarith [hangle.1,hangle.2,Real.pi_pos]) hpos
    simpa only [Real.cos_zero] using hh
  have hc2 : |B 1 0| < 2 := by rw [abs_of_pos hc,unitHeckeInversionSL_lowerLeft];linarith only [hcos]
  exact primitive_unit_stabilizer_of_lowerLeft _ (unitHeckeMobiusData n hnE)
    (unitHeckeMobiusGroup_translation_mem n hnE) B (unitHeckeInversionSL_mem n hnE) hc.ne' hc2

end LowDimensionalTopology.Geometry.Fuchsian
