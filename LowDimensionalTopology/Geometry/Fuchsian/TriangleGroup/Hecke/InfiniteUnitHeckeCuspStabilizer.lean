/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.UnitHeckeCuspStabilizer
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

/-- Actual real matrix membership is equivalent to membership of its whole native action. -/
theorem realSLMobius_mem_nativeConformal_range_iff (H : Subgroup (ℍ≃ᵢℍ))
    (hH : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈(nativeConformalSubgroupMobiusHom H hH).range ↔ _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A∈H := by
  constructor
  · rintro ⟨f,hf⟩
    obtain ⟨B,hB⟩:=hH f.property
    have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B∈H := by
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom B∈H
      rw [hB]
      exact f.property
    have he : f=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B,hm⟩:=Subtype.ext hB.symm
    rw [he,nativeConformalSubgroupMobiusHom_matrix] at hf
    have hnative : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A := by
      rcases (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_iff_sign B A).mp hf with rfl|rfl
      · rfl
      · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_neg B).symm
    rw [←hnative]
    exact hm
  · exact nativeConformalSubgroupMobiusGroup_matrix_mem H hH A

/-- The two-cusp standard group is the actual independently constructed infinite triangle group. -/
theorem standardHeckeGroup_top_eq :
    standardHeckeGroup ⊤ (by simp)=triangleConformalGroup infiniteHeckeTriangle := by
  have ht : standardHeckeTriangle ⊤ (by simp)=infiniteHeckeTriangle := by
    unfold standardHeckeTriangle infiniteHeckeTriangle
    simp only [triangleOrderAngle_top]
  change triangleConformalGroup _=_
  rw [ht]

/-- The literal unit translation is absent from the actual standard two-cusp group. -/
theorem standardHeckeGroup_top_unitTranslation_not_mem :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)∉standardHeckeGroup ⊤ (by simp) := by
  rw [standardHeckeGroup_top_eq]
  have he : modularNativeHom ModularGroup.T=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1) := by
    apply congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [ModularGroup.T,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.SpecialLinearGroup.map_apply_coe,
        RingHom.mapMatrix_apply,Matrix.map_apply]
  rw [←he]
  exact infiniteHeckeTriangle_translation_not_mem

/-- The true normalized two-cusp group does not contain a half-unit translation. -/
theorem unitHeckeMobiusGroup_top_halfTranslation_not_mem :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (1/2))∉unitHeckeMobiusGroup ⊤ (by simp) := by
  intro h
  have hn:=(realSLMobius_mem_nativeConformal_range_iff _ (unitHeckeGroup_le_conformal ⊤ (by simp)) _).mp h
  obtain ⟨g,hg,hge⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL ⊤ (by simp)))
    (standardHeckeGroup ⊤ (by simp)) _).mp hn
  have ht : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL ⊤ (by simp))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)*
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL ⊤ (by simp)))⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (1/2)) := by
    unfold unitHeckeDilationSL
    rw [dilation_conjugate_translation_native]
    norm_num only [triangleOrderAngle_top,Real.cos_zero,mul_one]
  have he : g=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1) := by
    have hh:=hge.trans ht.symm
    exact mul_left_cancel (mul_right_cancel hh)
  exact standardHeckeGroup_top_unitTranslation_not_mem (he ▸ hg)

/-- At the limiting Shimizu coefficient two, absence of the genuine half-period still forces integral periods. -/
theorem primitive_translation_integer_of_no_half
    (H : Subgroup Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hT1 : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hc : B 1 0≠0) (hc2 : |B 1 0| ≤ 2)
    (hhalf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (1/2))∉H)
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
    have hbound : 1≤|t-(n:ℝ)| * |B 1 0| := by
      rcases lt_or_gt_of_ne he with hn'|hp
      · have hTneg : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-(t-(n:ℝ))))∈H := by
          rw [primitive_translation_neg]
          exact H.inv_mem hr
        have hh:=primitive_translation_shimizu H hd (-(t-(n:ℝ))) (neg_pos.mpr hn') hTneg B hB hc
        simpa only [abs_of_neg hn'] using hh
      · simpa only [abs_of_pos hp] using primitive_translation_shimizu H hd _ hp hr B hB hc
    have hnear : |t-(n:ℝ)|≤(1:ℝ)/2:=abs_sub_round t
    have hprod : |t-(n:ℝ)| * |B 1 0| ≤ |t-(n:ℝ)| * 2 :=
      mul_le_mul_of_nonneg_left hc2 (abs_nonneg _)
    have ha : |t-(n:ℝ)|=(1:ℝ)/2 := by linarith only [hbound,hprod,hnear]
    rcases (abs_eq (by norm_num : (0:ℝ)≤1/2)).mp ha with hp|hn'
    · exact hhalf (hp ▸ hr)
    · have hh : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (1/2))∈H := by
        rw [hn',primitive_translation_neg] at hr
        simpa only [inv_inv] using H.inv_mem hr
      exact hhalf hh
  exact ⟨n,sub_eq_zero.mp hzero⟩

/-- The limiting coefficient and a proved half-period obstruction determine the full original infinity stabilizer. -/
theorem primitive_unit_stabilizer_of_no_half
    (H : Subgroup Mobius.complexMobiusGroup)
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hc : B 1 0≠0) (hc2 : |B 1 0| ≤ 2)
    (hhalf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (1/2))∉H) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ∞=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) := by
  apply le_antisymm
  · intro f hf
    obtain ⟨hfH,hfix⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ∞ f).mp hf
    obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL f (P.preserves ⟨f,hfH⟩)
    have hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H:=hA.symm ▸ hfH
    have hAf : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞=∞:=by rw [hA];exact hfix
    obtain ⟨t,ht⟩:=primitive_affine_translation H P.discrete hT A hAH hAf
    have hTt : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈H:=ht ▸ hAH
    obtain ⟨n,hn⟩:=primitive_translation_integer_of_no_half H P.discrete hT B hB hc hc2 hhalf t hTt
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨n,?_⟩
    rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation, ←map_zpow, hTranslationSL_zpow,
      mul_one, ←hn, ←ht, hA]
  · apply Subgroup.zpowers_le.mpr
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ∞ _).mpr ⟨hT,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1⟩

/-- The original unit-normalized two-cusp Hecke group has the full primitive unit-translation infinity stabilizer. -/
theorem unitHeckeMobiusGroup_top_infty_stabilizer :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer (unitHeckeMobiusGroup ⊤ (by simp)) ∞=
      Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) := by
  apply primitive_unit_stabilizer_of_no_half _ (unitHeckeMobiusData ⊤ (by simp))
    (unitHeckeMobiusGroup_translation_mem ⊤ (by simp))
    (unitHeckeInversionSL ⊤ (by simp)) (unitHeckeInversionSL_mem ⊤ (by simp))
  · rw [unitHeckeInversionSL_lowerLeft]
    norm_num [triangleOrderAngle_top]
  · rw [unitHeckeInversionSL_lowerLeft]
    norm_num [triangleOrderAngle_top]
  · exact unitHeckeMobiusGroup_top_halfTranslation_not_mem

/-- Every source parameter, including the two-cusp parameter, has the genuine full unit-translation stabilizer. -/
theorem unitHeckeMobiusGroup_infty_stabilizer_all (q : ℕ∞) (hq : 3≤q) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer (unitHeckeMobiusGroup q hq) ∞=
      Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) := by
  induction q using ENat.recTopCoe with
  | top => exact unitHeckeMobiusGroup_top_infty_stabilizer
  | coe n => exact unitHeckeMobiusGroup_infty_stabilizer n (by exact_mod_cast hq)

end LowDimensionalTopology.Geometry.Fuchsian
