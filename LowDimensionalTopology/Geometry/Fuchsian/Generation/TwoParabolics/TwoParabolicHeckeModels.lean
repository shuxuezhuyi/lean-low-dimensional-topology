/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.TwoParabolicTriangleModels
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

theorem unitHeckeInversionSL_upperLeft (q : ℕ∞) (hq : 3≤q) :
    unitHeckeInversionSL q hq 0 0=0 := by
  simp [unitHeckeInversionSL,unitHeckeDilationSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL,
    Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.mul_apply,Matrix.adjugate_fin_two,Fin.sum_univ_two,modularInversionSL]

theorem unitHeckeInversionSL_conjugate_negative_translation (q : ℕ∞) (hq : 3≤q) :
    unitHeckeInversionSL q hq*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)*(unitHeckeInversionSL q hq)⁻¹=
      twoParabolicModelSL (4*(Real.cos (triangleOrderAngle q))^2) := by
  let A:=unitHeckeInversionSL q hq
  have ha : A 0 0=0:=unitHeckeInversionSL_upperLeft q hq
  have hd : A 1 1=0:=unitHeckeInversionSL_lowerRight q hq
  have hc : A 1 0=2*Real.cos (triangleOrderAngle q):=unitHeckeInversionSL_lowerLeft q hq
  have hdet:=A.property
  change Matrix.det A.val=1 at hdet
  rw [Matrix.det_fin_two] at hdet
  change A 0 0*A 1 1-A 0 1*A 1 0=1 at hdet
  rw [ha,hd] at hdet
  change A*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)*A⁻¹=_
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoParabolicModelSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.mul_apply,
      Fin.sum_univ_two,ha,hd]
  · nlinarith [hdet]
  · rw [hc]
    ring
  · nlinarith [hdet]

theorem unitHeckeMobiusGroup_generators (q : ℕ∞) (hq : 3≤q) :
    unitHeckeMobiusGroup q hq=Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeInversionSL q hq)} :
        Set Mobius.complexMobiusGroup) := by
  have hH : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeInversionSL q hq)} : Set (ℍ≃ᵢℍ))≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
    rw [unitHeckeInversionSL_native,←unitHeckeGroup_generators]
    exact unitHeckeGroup_le_conformal q hq
  have h:=native_matrix_pair_mobius_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1) (unitHeckeInversionSL q hq) hH
  have hrange : ∀(H K : Subgroup (ℍ≃ᵢℍ))
      (hH : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) (hK : K≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup),
      H=K → (nativeConformalSubgroupMobiusHom H hH).range=
        (nativeConformalSubgroupMobiusHom K hK).range := by
    intro H K hH hK he
    subst K
    rfl
  exact (hrange _ _ _ hH (by rw [unitHeckeGroup_generators,unitHeckeInversionSL_native])).trans h

theorem unitHeckeProductSL_square_twoParabolic (n : ℕ) (hn : 3≤n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeProductSL n hn)^2=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicCornerSL (4*(Real.cos (Real.pi/(n:ℝ)))^2)) := by
  let T:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)
  let S:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeInversionSL n (by exact_mod_cast hn))
  let U:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL (4*(Real.cos (Real.pi/(n:ℝ)))^2))
  have hSorder : orderOf S=2 := by
    rw [realSLMobius_order_eq_native,unitHeckeInversionSL_native,unitHeckeInversion_order_two]
  have hSsq : S*S=1 := by
    have h:=pow_orderOf_eq_one S
    simpa only [hSorder,pow_two] using h
  have hSi : S⁻¹=S := by
    calc
      S⁻¹=S⁻¹*(S*S) := by rw [hSsq,mul_one]
      _=S := by group
  have hU : S*T⁻¹*S⁻¹=U := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius _*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius _)⁻¹*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius _)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius _
    rw [←map_inv,←map_inv,←map_mul,←map_mul]
    rw [←hTranslationSL_neg_one_inverse]
    rw [unitHeckeInversionSL_conjugate_negative_translation]
    rfl
  have hUi : S*T*S=U⁻¹ := by
    have h:=congrArg Inv.inv hU
    simpa only [mul_inv_rev,inv_inv,hSi,mul_assoc] using h
  rw [unitHeckeProductSL,map_mul]
  change (T*S)^2=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1*twoParabolicModelSL _)
  rw [map_mul,←twoParabolicModelSL_inverse,map_inv]
  change (T*S)^2=T*U⁻¹
  calc
    (T*S)^2=T*(S*T*S) := by simp only [pow_two,mul_assoc]
    _=T*U⁻¹ := by rw [hUi]

theorem odd_order_mem_of_square_mem {G : Type*} [Group G] (H : Subgroup G) (a : G)
    (hodd : Odd (orderOf a)) (hmem : a^2∈H) : a∈H := by
  obtain ⟨k,hk⟩:=hodd
  have he : (a^2)^(k+1)=a := by
    rw [←pow_mul,show 2*(k+1)=orderOf a+1 by omega,pow_succ,pow_orderOf_eq_one,one_mul]
  have hm:=H.pow_mem hmem (k+1)
  rwa [he] at hm

theorem twoParabolic_hecke_parameter_odd (n : ℕ) (hn : 3≤n)
    (ho : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (twoParabolicCornerSL (4*(Real.cos (Real.pi/(n:ℝ)))^2)))=n) : Odd n := by
  have hE:=unitHeckeProductSL_order n hn
  have hE2:=unitHeckeProductSL_square_twoParabolic n hn
  by_contra hodd
  have hd : 2∣n := Nat.dvd_of_mod_eq_zero (by
    have hmod : n%2≠1 := by
      intro h
      exact hodd (Nat.odd_iff.mpr h)
    omega)
  have hpow:=orderOf_pow_of_dvd (x:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeProductSL n hn))
    (by decide : (2:ℕ)≠0) (by rwa [hE])
  rw [hE,hE2,ho] at hpow
  have hlt : n/2<n := Nat.div_lt_self (by omega) (by decide)
  omega

theorem twoParabolicCanonicalGroup_eq_hecke (n : ℕ) (hn : 3≤n) (hodd : Odd n) :
    twoParabolicCanonicalGroup (4*(Real.cos (Real.pi/(n:ℝ)))^2)=
      unitHeckeMobiusGroup n (by exact_mod_cast hn) := by
  let K:=twoParabolicCanonicalGroup (4*(Real.cos (Real.pi/(n:ℝ)))^2)
  let H:=unitHeckeMobiusGroup n (by exact_mod_cast hn)
  let T:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)
  let S:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeInversionSL n (by exact_mod_cast hn))
  let U:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL (4*(Real.cos (Real.pi/(n:ℝ)))^2))
  have hTK : T∈K:=Subgroup.subset_closure (by simp [T])
  have hUK : U∈K:=twoParabolicCanonicalGroup_model _
  have hTH : T∈H:=by simpa only [T,_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation] using
    unitHeckeMobiusGroup_translation_mem n (by exact_mod_cast hn)
  have hSH : S∈H:=unitHeckeInversionSL_mem n (by exact_mod_cast hn)
  have hUH : U∈H := by
    have hm:=H.mul_mem (H.mul_mem hSH (H.inv_mem hTH)) (H.inv_mem hSH)
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius _*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius _)⁻¹*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius _)⁻¹∈H at hm
    rw [←map_inv,←map_inv,←map_mul,←map_mul,←hTranslationSL_neg_one_inverse,
      unitHeckeInversionSL_conjugate_negative_translation] at hm
    exact hm
  have hEK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeProductSL n hn)∈K := by
    apply odd_order_mem_of_square_mem K _
    · rwa [unitHeckeProductSL_order]
    · rw [unitHeckeProductSL_square_twoParabolic]
      exact twoParabolicCornerSL_mem _
  have hSK : S∈K := by
    have hm:=K.mul_mem (K.inv_mem hTK) hEK
    change T⁻¹*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1*unitHeckeInversionSL n _)∈K at hm
    rw [map_mul] at hm
    change T⁻¹*(T*S)∈K at hm
    simpa only [inv_mul_cancel_left] using hm
  change K=H
  apply le_antisymm
  · change Subgroup.closure _≤H
    apply (Subgroup.closure_le H).mpr
    intro f hf
    rcases hf with rfl|rfl
    · exact hTH
    · exact hUH
  · change unitHeckeMobiusGroup n _≤K
    rw [unitHeckeMobiusGroup_generators]
    apply (Subgroup.closure_le K).mpr
    intro f hf
    rcases hf with rfl|rfl
    · exact hTK
    · exact hSK


theorem twoParabolic_small_group_models (c : ℝ) (hc : 1≤c) (h4 : c<4)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (twoParabolicCanonicalGroup c)) :
    (∃n : ℕ,∃hn : 3≤n,Odd n ∧ c=4*(Real.cos (Real.pi/(n:ℝ)))^2 ∧
      twoParabolicCanonicalGroup c=unitHeckeMobiusGroup n (by exact_mod_cast hn)) ∨
    (∃p : ℕ,∃hp : 2≤p,c=twoIdealParabolicCoefficient p ∧
      twoParabolicCanonicalGroup c=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoIdealParabolicNormalizer p hp))
        (nativeConformalSubgroupMobiusHom (triangleConformalGroup (twoIdealIntegralTriangle p hp))
          inf_le_right).range) := by
  obtain ⟨r,hr,ho,hform⟩:=twoParabolic_small_parameter_classification c hc h4 hd
  rcases hform with hform|hform
  · right
    have he : c=twoIdealParabolicCoefficient r:=hform
    refine ⟨r,hr,he,?_⟩
    rw [he]
    exact (twoIdeal_mobius_group_normalization r hr).symm
  · left
    have hr3 : 3≤r := by
      by_contra hn
      have hrval : r=2 := by omega
      norm_num [hrval,Real.cos_pi] at hform
      linarith
    have hdouble:=Real.cos_two_mul (Real.pi/(r:ℝ))
    rw [show 2*(Real.pi/(r:ℝ))=2*Real.pi/(r:ℝ) by ring] at hdouble
    have he : c=4*(Real.cos (Real.pi/(r:ℝ)))^2 := by nlinarith [hdouble,hform]
    have hodd : Odd r := twoParabolic_hecke_parameter_odd r hr3 (by rw [←he];exact ho.symm)
    refine ⟨r,hr3,hodd,he,?_⟩
    rw [he]
    exact twoParabolicCanonicalGroup_eq_hecke r hr3 hodd


theorem two_parabolic_exceptional_group_models (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)))
    (hsmall : Matrix.trace (A*B*A⁻¹*B⁻¹).val<18) :
    ∃q : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∃n : ℕ,∃hn : 3≤n,Odd n ∧
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) (Subgroup.closure
          ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))=
          unitHeckeMobiusGroup n (by exact_mod_cast hn) ∧
        Matrix.trace (A*B*A⁻¹*B⁻¹).val=2+16*(Real.cos (Real.pi/(n:ℝ)))^4) ∨
      (∃p : ℕ,∃hp : 2≤p,
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) (Subgroup.closure
          ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))=
          (nativeConformalSubgroupMobiusHom (triangleConformalGroup (twoIdealIntegralTriangle p hp))
            inf_le_right).range ∧
        Matrix.trace (A*B*A⁻¹*B⁻¹).val=2+16*(Real.cos (Real.pi/(2*(p:ℝ))))^4) := by
  obtain ⟨q,c,hc,hq,htr,hdc,_hne⟩:=two_parabolic_discrete_positive_normal_form A B hA hB hd hne
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) (Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))=twoParabolicCanonicalGroup c at hq
  have h4 : c<4 := (twoParabolic_small_trace_parameter c hc).mp (by rwa [←htr])
  rcases twoParabolic_small_group_models c hc h4 hdc with ⟨n,hn,hodd,he,hmodel⟩|⟨p,hp,he,hmodel⟩
  · refine ⟨q,Or.inl ⟨n,hn,hodd,hq.trans hmodel,?_⟩⟩
    rw [htr,he]
    ring
  · refine ⟨(twoIdealParabolicNormalizer p hp)⁻¹*q,Or.inr ⟨p,hp,?_,?_⟩⟩
    · rw [map_mul,map_inv,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose,hq,hmodel]
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.subgroupConjugate_inv_cancel _ _
    · have hdouble:=Real.cos_two_mul (Real.pi/(2*(p:ℝ)))
      rw [show 2*(Real.pi/(2*(p:ℝ)))=Real.pi/(p:ℝ) by ring] at hdouble
      have hcoef : c=4*(Real.cos (Real.pi/(2*(p:ℝ))))^2 := by
        change c=2+2*Real.cos (Real.pi/(p:ℝ)) at he
        nlinarith [he,hdouble]
      rw [htr,hcoef]
      ring

end LowDimensionalTopology.Geometry.Fuchsian
