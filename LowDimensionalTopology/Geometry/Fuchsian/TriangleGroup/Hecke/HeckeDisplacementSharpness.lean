/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.WeakDisplacementGap
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.ParabolicSideNormalizers
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicEllipticOrderBounds
@[expose] public section
noncomputable section
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

/-- The canonical actual elliptic center of the standard Hecke product
is its genuine finite triangle corner. -/
theorem standardHeckeCornerSL_center (n : ℕ) (hn : 3≤n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter (standardHeckeCornerSL n)
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _ (standardHeckeCornerSL_elliptic n hn).1).mp
        (standardHeckeCornerSL_elliptic n hn))=standardHeckeCorner n hn := by
  exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff _ _ _).mp (standardHeckeCornerSL_fixed n hn)).symm

/-- Its actual displacement sine is the source order sine, rather than an
assumed primitive-angle coefficient. -/
theorem standardHeckeCornerSL_half_sine (n : ℕ) (hn : 3≤n) :
    Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle (standardHeckeCornerSL n)
      (standardHeckeCornerSL_elliptic n hn)/2)=Real.sin (Real.pi/(n:ℝ)) := by
  rw [elliptic_actual_angle_height,standardHeckeCornerSL_center n hn]
  have hc : standardHeckeCornerSL n 1 0=1:=by
    norm_num [standardHeckeCornerSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  rw [hc,abs_one,one_mul]
  rfl

/-- Exact algebra in the attained displacement formula for a Hecke corner. -/
theorem hecke_radial_sharp_scalar (S C : ℝ) (hS : 0<S) (hC : 0<C)
    (hcircle : S^2+C^2=1) :
    S*(2*C)^2/(4*S*(S*S+|2*C|))=C^2/(1+2*C-C^2) := by
  have hd : 1+2*C-C^2=S*S+2*C:=by nlinarith only [hcircle]
  rw [abs_of_pos (by positivity : 0<2*C),hd]
  field_simp
  ring

/-- Every finite standard Hecke pair attains the order-dependent universal
maximum-displacement constant exactly. -/
theorem standardHecke_order_displacementM_eq (n : ℕ) (hn : 3≤n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (Real.pi/(n:ℝ)))))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL n))=
      Real.cos (Real.pi/(n:ℝ))/Real.sqrt (1+2*Real.cos (Real.pi/(n:ℝ))-
        Real.cos (Real.pi/(n:ℝ))^2) := by
  let θ:=Real.pi/(n:ℝ)
  have hnR : (2:ℝ)<n:=by exact_mod_cast (by omega : 2<n)
  have hθ:=pi_div_acute_of_two_lt n hnR
  have hS : 0<Real.sin θ:=Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2,Real.pi_pos])
  have hC : 0<Real.cos θ:=Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩
  have hd : 0<1+2*Real.cos θ-Real.cos θ^2:=by
    nlinarith only [Real.sin_sq_add_cos_sq θ,sq_nonneg (Real.sin θ),hC]
  have hM:=translation_elliptic_displacementM_square (standardHeckeCornerSL n)
    (standardHeckeCornerSL_elliptic n hn) (2*Real.cos θ) (by positivity)
  dsimp only at hM
  rw [standardHeckeCornerSL_center n hn,standardHeckeCornerSL_half_sine n hn] at hM
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos θ)))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL n)))^2=
    Real.sin θ*(2*Real.cos θ)^2/(4*Real.sin θ*(Real.sin θ*Real.sin θ+|2*Real.cos θ|)) at hM
  rw [hecke_radial_sharp_scalar _ _ hS hC (Real.sin_sq_add_cos_sq θ)] at hM
  apply (sq_eq_sq₀ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _)
    (div_nonneg hC.le (Real.sqrt_nonneg _))).mp
  rw [div_pow,Real.sq_sqrt hd.le]
  exact hM


/-- The literal original complex group generated by the Hecke translation
and its finite corner element. -/
def sharpHeckePairGroup (n : ℕ) : Subgroup Mobius.complexMobiusGroup :=
  Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (Real.pi/(n:ℝ)))),
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (standardHeckeCornerSL n)}:Set Mobius.complexMobiusGroup)

theorem sharpHeckePairGroup_le_standard (n : ℕ) (hn : 3≤n) :
    sharpHeckePairGroup n≤standardHeckeMobiusGroup n (by exact_mod_cast hn) := by
  apply (Subgroup.closure_le _).mpr
  intro f hf
  rcases hf with rfl|rfl
  · have ht:=standardHeckeMobiusGroup_translation_mem (n:ℕ∞) (by exact_mod_cast hn)
    rw [triangleOrderAngle_nat] at ht
    exact ht
  · exact standardHeckeMobiusGroup_product_mem n hn

/-- Discreteness and original half-plane preservation are inherited from
the actual faithful global Hecke group, not imposed as extra hypotheses. -/
theorem sharpHeckePairGroup_data (n : ℕ) (hn : 3≤n) :
    HalfPlaneFuchsianGroup (sharpHeckePairGroup n) where
  preserves g:=(standardHeckeMobiusData n (by exact_mod_cast hn)).preserves
    ⟨g.val,sharpHeckePairGroup_le_standard n hn g.property⟩
  discrete:=by
    let G:=standardHeckeMobiusGroup n (by exact_mod_cast hn)
    let sharpHeckeStandardDiscrete : DiscreteTopology G:=(standardHeckeMobiusData n (by exact_mod_cast hn)).discrete
    let e : sharpHeckePairGroup n→G:=fun f=>⟨f.val,sharpHeckePairGroup_le_standard n hn f.property⟩
    have hecont : Continuous e:=continuous_subtype_val.subtype_mk _
    have heinj : Function.Injective e:=by
      intro f g he
      exact Subtype.ext (congrArg (fun a:G=>a.val) he)
    exact DiscreteTopology.of_continuous_injective hecont heinj

/-- The actual Hecke translation remains a genuine nontrivial parabolic. -/
theorem sharpHecke_translation_parabolic (n : ℕ) (hn : 3≤n) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (Real.pi/(n:ℝ))))) := by
  rw [parabolicSL_translation_projection]
  apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff _).mpr
  exact_mod_cast (hecke_width_pos (n:ℕ∞) (by exact_mod_cast hn)).ne'

/-- A noninvolutory finite elliptic and a genuine parabolic in the actual
same discrete Hecke group cannot generate an elementary group. -/
theorem sharpHeckePairGroup_nonElementary (n : ℕ) (hn : 3≤n) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (sharpHeckePairGroup n) := by
  let K:=sharpHeckePairGroup n
  let f:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (Real.pi/(n:ℝ))))
  let g:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (standardHeckeCornerSL n)
  have hf : f∈K:=Subgroup.subset_closure (by simp [f])
  have hg : g∈K:=Subgroup.subset_closure (by simp [g])
  intro he
  let sharpHeckeElementaryFinite : Finite K:=elementary_elliptic_noninvolution_finite
    (sharpHeckePairGroup_data n hn).asFuchsianDisc he g hg
    (standardHeckeCornerSL_elliptic n hn) (by rw [standardHeckeMobiusProduct_order n hn];omega)
  have hfin:=isOfFinOrder_of_finite (⟨f,hf⟩:K)
  have hfin' : IsOfFinOrder f:=by
    obtain ⟨k,hk,hpow⟩:=hfin.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨k,hk,congrArg Subtype.val hpow⟩
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_parabolic_or_loxodromic_not_isOfFinOrder f
    (Or.inl (sharpHecke_translation_parabolic n hn)) hfin'

/-- Actual original-group sharpness for every order at least three:
the generators are parabolic and exactly order-n elliptic, their literal
generated whole group is discrete and non-elementary, and the actual
maximum-displacement infimum equals the source constant. -/
theorem parabolic_elliptic_order_bound_sharp (n : ℕ) (hn : 3≤n) :
    ∃A B:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) ∧
      orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)=n ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)=
        Real.cos (Real.pi/(n:ℝ))/Real.sqrt (1+2*Real.cos (Real.pi/(n:ℝ))-
          Real.cos (Real.pi/(n:ℝ))^2) := by
  exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (Real.pi/(n:ℝ))),standardHeckeCornerSL n,
    sharpHecke_translation_parabolic n hn,standardHeckeCornerSL_elliptic n hn,
    standardHeckeMobiusProduct_order n hn,(sharpHeckePairGroup_data n hn).discrete,
    sharpHeckePairGroup_nonElementary n hn,standardHecke_order_displacementM_eq n hn⟩

/-- The exact elementary scalar lower envelope in the source at cos=1/2. -/
theorem elliptic_order_constant_ge_sqrt_seven (C : ℝ) (hC : 1/2≤C) (hCup : C≤1) :
    1/Real.sqrt 7≤C/Real.sqrt (1+2*C-C^2) := by
  have hCpos : 0<C:=by linarith only [hC]
  have hC2 : C^2≤1:=by
    simpa only [one_pow] using (sq_le_sq₀ hCpos.le zero_le_one).mpr hCup
  have hd : 0<1+2*C-C^2:=by linarith only [hC2,hCpos]
  apply (sq_le_sq₀ (div_nonneg zero_le_one (Real.sqrt_nonneg _))
    (div_nonneg hCpos.le (Real.sqrt_nonneg _))).mp
  rw [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤7),div_pow,Real.sq_sqrt hd.le]
  norm_num only [one_pow]
  apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<7) hd).mpr
  have hprod : 0≤(2*C-1)*(4*C+1):=mul_nonneg (by linarith only [hC]) (by linarith only [hC])
  nlinarith only [hprod]

/-- Every actual order q>=3 has the requisite cosine at least one half. -/
theorem elliptic_order_cos_ge_half (q : ℕ) (hq : 3≤q) : 1/2≤Real.cos (Real.pi/(q:ℝ)) := by
  have hqR : (3:ℝ)≤q:=by exact_mod_cast hq
  have hqpos : 0<(q:ℝ):=by linarith only [hqR]
  have hθ : Real.pi/(q:ℝ)≤Real.pi/3:=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hqR
  have h:=Real.cos_le_cos_of_nonneg_of_le_pi (div_nonneg Real.pi_pos.le hqpos.le)
    (by linarith only [Real.pi_pos] : Real.pi/3≤Real.pi) hθ
  rwa [Real.cos_pi_div_three] at h

/-- The source's q>=3 numerical bound applies to every original discrete
parabolic/elliptic pair with no added primitive or normalization assumptions. -/
theorem parabolic_elliptic_displacementM_sqrt_seven
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set Mobius.complexMobiusGroup)))
    (hq : 3≤orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    1/Real.sqrt 7≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  exact (elliptic_order_constant_ge_sqrt_seven _ (elliptic_order_cos_ge_half _ hq)
    (Real.cos_le_one _)).trans (parabolic_elliptic_order_displacementM_bound A B hA hB hd hq)

/-- The lowest order-dependent constant is exactly the printed universal value. -/
theorem elliptic_order_constant_at_three :
    Real.cos (Real.pi/(3:ℝ))/Real.sqrt (1+2*Real.cos (Real.pi/(3:ℝ))-
      Real.cos (Real.pi/(3:ℝ))^2)=1/Real.sqrt 7 := by
  rw [Real.cos_pi_div_three]
  norm_num
  field_simp

/-- The original discrete non-elementary order-three Hecke pair attains
one over sqrt seven for the actual all-point maximum-displacement infimum. -/
theorem parabolic_elliptic_sqrt_seven_sharp :
    ∃A B:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) ∧
      orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)=3 ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)=1/Real.sqrt 7 := by
  obtain ⟨A,B,hA,hB,ho,hd,hn,hM⟩:=parabolic_elliptic_order_bound_sharp 3 (by decide)
  exact ⟨A,B,hA,hB,ho,hd,hn,hM.trans elliptic_order_constant_at_three⟩

end LowDimensionalTopology.Geometry.Fuchsian
