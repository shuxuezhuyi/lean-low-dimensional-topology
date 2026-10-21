/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Gram.DirichletGramIdentity
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ParabolicEllipticNormalForms
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Euclidean

/-- Three distinct actual points determine their genuine generalized circle. -/
theorem complexGeneralizedCircle_eq_of_three {S T : Set Mobius.ExtendedComplex}
    (hS : Mobius.IsComplexGeneralizedCircle S) (hT : Mobius.IsComplexGeneralizedCircle T)
    (a b c : Mobius.ExtendedComplex) (hd : Mobius.TripleDistinct a b c)
    (haS : a∈S) (hbS : b∈S) (hcS : c∈S) (haT : a∈T) (hbT : b∈T) (hcT : c∈T) : S=T := by
  obtain ⟨q,h0,h1,hi⟩:=Mobius.mobius_normalize_triple a b c hd
  have hSi : q.val '' S=Mobius.complexRealAxis :=
    Mobius.complexCircle_through_zero_one_infty (hS.image q.property.1) ⟨a,haS,h0⟩ ⟨b,hbS,h1⟩ ⟨c,hcS,hi⟩
  have hTi : q.val '' T=Mobius.complexRealAxis :=
    Mobius.complexCircle_through_zero_one_infty (hT.image q.property.1) ⟨a,haT,h0⟩ ⟨b,hbT,h1⟩ ⟨c,hcT,hi⟩
  exact Set.image_injective.mpr q.val.injective (hSi.trans hTi.symm)

/-- Three distinct genuine points on two intrinsic horocycles force the same actual ideal centre. -/
theorem IsHHorocycleAt.center_eq_of_three {ξ η : Mobius.ExtendedComplex} {S T : Set ℍ}
    (hS : IsHHorocycleAt ξ S) (hT : IsHHorocycleAt η T)
    (a b c : ℍ) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (haS : a∈S) (hbS : b∈S) (hcS : c∈S) (haT : a∈T) (hbT : b∈T) (hcT : c∈T) : ξ=η := by
  obtain ⟨C,hC,rfl,_hneS⟩:=hS
  obtain ⟨D,hD,rfl,_hneT⟩:=hT
  have hinj : Function.Injective (fun z : ℍ=>((z:ℂ):Mobius.ExtendedComplex)) :=
    OnePoint.coe_injective.comp UpperHalfPlane.coe_injective
  have hd : Mobius.TripleDistinct
    ((a:ℂ):Mobius.ExtendedComplex) ((b:ℂ):Mobius.ExtendedComplex) ((c:ℂ):Mobius.ExtendedComplex) :=
    ⟨hinj.ne hab,hinj.ne hac,hinj.ne hbc⟩
  have he:=complexGeneralizedCircle_eq_of_three C.property D.property _ _ _ hd haS hbS hcS haT hbT hcT
  have hi:=congrArg (fun V : Set Mobius.ExtendedComplex=>V∩halfPlaneIdealBoundary) he
  rw [hC,hD] at hi
  exact Set.singleton_injective hi

/-- Actual determinant-one transport preserves the intrinsic horocycle and its genuine ideal centre. -/
theorem IsHHorocycleAt.realSL_image {ξ : Mobius.ExtendedComplex} {S : Set ℍ} (hS : IsHHorocycleAt ξ S)
    (q : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    IsHHorocycleAt ((realSLMobius q).val ξ) ((q • · : ℍ→ℍ) '' S) := by
  let g:=Matrix.SpecialLinearGroup.mapGL ℝ q
  have hg : 0<g.val.det := by change 0<q.val.det;rw [q.det_coe];norm_num
  have hh:=hS.realGL_image g hg
  change IsHHorocycleAt (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ξ) ((q • · : ℍ→ℍ) '' S) at hh
  simpa only [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,realSLMobius_matrix] using hh

/-- Opposite real determinant-one representatives induce the same genuine action. -/
theorem realSL_negative_action (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) : (-A) • z=A • z := by
  apply UpperHalfPlane.ext
  apply OnePoint.coe_injective
  rw [←realSLMobius_action,←realSLMobius_action,realSLMobius_neg]

/-- A genuine parabolic map preserves each intrinsic horocycle about its actual fixed ideal point. -/
theorem IsHHorocycleAt.parabolic_smul_mem {ξ : Mobius.ExtendedComplex} {S : Set ℍ}
    (hS : IsHHorocycleAt ξ S) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) (hfix : (realSLMobius A).val ξ=ξ)
    {z : ℍ} (hz : z∈S) : A • z∈S := by
  obtain ⟨q,hq⟩:=realSLMobius_exists_send_to_infty ξ hS.center_mem_idealBoundary
  have himage:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHHorocycleAt.realSL_image hS q
  rw [hq] at himage
  obtain ⟨t,_ht,hSimage⟩:=(IsHHorocycleAt_infty_iff _).mp himage
  have hQ : Mobius.MobiusParabolic (realSLMobius (q*A*q⁻¹)) := by
    rw [map_mul,map_mul,map_inv]
    exact (Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨realSLMobius q,rfl⟩)).mp hA
  have hQfix : (realSLMobius (q*A*q⁻¹)).val ∞=∞ := by
    rw [←hq]
    exact (realSLMobius_conjugate_fixed_iff A q ξ).mpr hfix
  obtain ⟨u,_hu,hnorm⟩:=hSL_parabolic_triangular_normal_form (q*A*q⁻¹)
    ((realSLMobius_parabolic_iff _ hQ.1).mp hQ) ((realSLMobius_fixed_infty_iff _).mp hQfix) hQ.1
  have him : ((q*A*q⁻¹) • (q • z)).im=(q • z).im := by
    rcases hnorm with hn|hn
    · rw [hn,hTranslationSL_im]
    · rw [hn,realSL_negative_action,hTranslationSL_im]
  have hzq : q • z∈horizontalHorocycle t := by rw [←hSimage];exact ⟨z,hz,rfl⟩
  have hAzq : q • (A • z)∈horizontalHorocycle t := by
    change (q • (A • z)).im=t
    have he : (q*A*q⁻¹) • (q • z)=q • (A • z) := by simp only [mul_smul,inv_smul_smul]
    rw [←he,him]
    exact hzq
  rw [←hSimage] at hAzq
  obtain ⟨w,hw,he⟩:=hAzq
  exact (isometry_smul ℍ q).injective he ▸ hw



/-- Two genuine parabolic maps with a common actual fixed ideal point move any actual point along the unique intrinsic horocycle through that point. -/
theorem realSL_parabolic_common_fixed_horocycle (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) (hB : Mobius.MobiusParabolic (realSLMobius B))
    (ξ : Mobius.ExtendedComplex) (hξ : ξ∈halfPlaneIdealBoundary)
    (hAf : (realSLMobius A).val ξ=ξ) (hBf : (realSLMobius B).val ξ=ξ) (z : ℍ) :
    ∃S : Set ℍ,IsHHorocycleAt ξ S ∧ z∈S ∧ A • z∈S ∧ B • z∈S := by
  obtain ⟨S,⟨hS,hz⟩,_hunique⟩:=existsUnique_hHorocycleAt_through ξ hξ z
  exact ⟨S,hS,hz,_root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHHorocycleAt.parabolic_smul_mem hS A hA hAf hz,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHHorocycleAt.parabolic_smul_mem hS B hB hBf hz⟩

/-- Given three distinct actual orbit points on a true horocycle, identical independent Gram degeneracy fixes that horocycle's actual ideal centre. -/
theorem realSLHorocycleGram_zero_fixes_horocycle_center (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A≠1) (hB : realSLMobius B≠1) (hne : realSLMobius A≠realSLMobius B)
    (h : realSLHorocycleGramBivariate A B=0) {ξ : Mobius.ExtendedComplex} {S : Set ℍ}
    (hS : IsHHorocycleAt ξ S) (z : ℍ) (hzA : z≠A • z) (hzB : z≠B • z) (hAB : A • z≠B • z)
    (hz : z∈S) (hAz : A • z∈S) (hBz : B • z∈S) :
    Mobius.MobiusParabolic (realSLMobius A) ∧ Mobius.MobiusParabolic (realSLMobius B) ∧
      (realSLMobius A).val ξ=ξ ∧ (realSLMobius B).val ξ=ξ := by
  obtain ⟨hAp,hBp,η,hη,hAf,hBf⟩:=realSLHorocycleGram_zero_classification A B hA hB hne h
  obtain ⟨T,hT,hzT,hAzT,hBzT⟩:=realSL_parabolic_common_fixed_horocycle A B hAp hBp η hη hAf hBf z
  have hξη:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHHorocycleAt.center_eq_of_three hS hT z (A • z) (B •
    z) hzA hzB hAB hz hAz hBz hzT hAzT hBzT
  rw [hξη]
  exact ⟨hAp,hBp,hAf,hBf⟩

end LowDimensionalTopology.Geometry.Hyperbolic
