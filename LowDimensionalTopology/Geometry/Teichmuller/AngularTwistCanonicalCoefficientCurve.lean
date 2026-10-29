module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchySeriesIntegral
public import LowDimensionalTopology.Geometry.Teichmuller.ElementaryAngularTwist
public import LowDimensionalTopology.Geometry.Quasiconformal.BeltramiParameterDerivative
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Tactic.Ring

/-!
# The actual angular coefficient curve and its canonical plane variation

The literal elementary coefficients descend to actual right cosets and are
summed before the coefficient curve is encoded in the full-plane Banach ball.
The infinitesimal direction may have norm greater than one. Every real
parameter still gives a strictly subunit coefficient, and its explicit scalar
remainder tends to zero in the actual L-infinity space. The resulting
canonical zero-extended plane solutions have the stated integral derivative.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane ComplexConjugate ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

private theorem coefficientCurve_eq_scalar (θ : Width) (t : ℝ) (z : ℍ) :
    coefficientCurve θ t z =
      ((t : ℂ) / (1 - (t : ℂ) * infinitesimalScale θ)) * infinitesimal θ z := by
  classical
  by_cases hz : Complex.arg (z : ℂ) ∈ interval θ
  · simp only [coefficientCurve, infinitesimal, ite_eq_left hz, div_eq_mul_inv]
    ring
  · simp only [coefficientCurve, infinitesimal, ite_eq_right hz, mul_zero]

open scoped Classical in
/-- The actual elementary coefficient transported by a real Mobius map and
extended by zero on the closed lower half-plane. -/
def pullbackCoefficientCurveZeroExtension (θ : Width) (t : ℝ) (γ : Deck) (ζ : ℂ) : ℂ :=
  if hζ : 0 < ζ.im then
    coefficientCurve θ t (γ • (⟨ζ, hζ⟩ : ℍ)) *
      GammaMeasurableBeltrami.phase γ (⟨ζ, hζ⟩ : ℍ)
  else 0

private theorem pullbackCoefficientCurveZeroExtension_eq_scalar
    (θ : Width) (t : ℝ) (γ : Deck) :
    pullbackCoefficientCurveZeroExtension θ t γ = fun ζ =>
      ((t : ℂ) / (1 - (t : ℂ) * infinitesimalScale θ)) *
        pullbackInfinitesimalZeroExtension θ γ ζ := by
  funext ζ
  by_cases hζ : 0 < ζ.im
  · rw [pullbackCoefficientCurveZeroExtension, dite_eq_left hζ]
    let z : ℍ := ⟨ζ, hζ⟩
    change coefficientCurve θ t (γ • z) * GammaMeasurableBeltrami.phase γ z =
      ((t : ℂ) / (1 - (t : ℂ) * infinitesimalScale θ)) *
        pullbackInfinitesimalZeroExtension θ γ (z : ℂ)
    rw [coefficientCurve_eq_scalar, pullbackInfinitesimalZeroExtension_coe]
    exact mul_assoc _ _ _
  · rw [pullbackCoefficientCurveZeroExtension, dite_eq_right hζ,
      pullbackInfinitesimalZeroExtension_eq_zero_of_im_nonpos θ γ (le_of_not_gt hζ),
      mul_zero]

theorem pullbackCoefficientCurveZeroExtension_rightRel
    (θ : Width) (Γ : Subgroup Deck) (s t : ℝ) (γ δ : Γ)
    (hγδ : QuotientGroup.rightRel (projectiveDilationSubgroup Γ s) γ δ) :
    pullbackCoefficientCurveZeroExtension θ t γ.val =
      pullbackCoefficientCurveZeroExtension θ t δ.val := by
  rw [pullbackCoefficientCurveZeroExtension_eq_scalar,
    pullbackCoefficientCurveZeroExtension_eq_scalar,
    pullbackInfinitesimalZeroExtension_rightRel θ Γ s γ δ hγδ]

/-- The same literal zero-extended coefficient, independent of the actual
right-coset representative. -/
def rightCosetCoefficientCurveZeroExtension (θ : Width) (Γ : Subgroup Deck) (s t : ℝ) :
    Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)) → ℂ → ℂ :=
  Quotient.lift (fun γ : Γ => pullbackCoefficientCurveZeroExtension θ t γ.val)
    (fun γ δ hγδ => pullbackCoefficientCurveZeroExtension_rightRel θ Γ s t γ δ hγδ)

/-- The actual source coefficient sum on the zero-extended plane. -/
def rightCosetCoefficientSum (θ : Width) (Γ : Subgroup Deck) (s t : ℝ) (ζ : ℂ) : ℂ :=
  ∑' u : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
    rightCosetCoefficientCurveZeroExtension θ Γ s t u ζ

private theorem rightCosetCoefficientCurveZeroExtension_eq_scalar
    (θ : Width) (Γ : Subgroup Deck) (s t : ℝ)
    (u : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))) (ζ : ℂ) :
    rightCosetCoefficientCurveZeroExtension θ Γ s t u ζ =
      ((t : ℂ) / (1 - (t : ℂ) * infinitesimalScale θ)) *
        rightCosetInfinitesimalZeroExtension θ Γ s u ζ := by
  refine Quotient.inductionOn u ?_
  intro γ
  exact congrFun (pullbackCoefficientCurveZeroExtension_eq_scalar θ t γ.val) ζ

/-- The literal coefficient sum is the explicit scalar multiple of the same
infinitesimal sum, including both boundary rays of the angular support. -/
theorem rightCosetCoefficientSum_eq_scalar
    (θ : Width) (Γ : Subgroup Deck) (s t : ℝ) (ζ : ℂ) :
    rightCosetCoefficientSum θ Γ s t ζ =
      ((t : ℂ) / (1 - (t : ℂ) * infinitesimalScale θ)) *
        ∑' u : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
          rightCosetInfinitesimalZeroExtension θ Γ s u ζ := by
  unfold rightCosetCoefficientSum
  simp_rw [rightCosetCoefficientCurveZeroExtension_eq_scalar]
  exact tsum_mul_left

private theorem norm_coefficient_scalar_mul_bound_lt_one (θ : Width) (t : ℝ) :
    ‖(t : ℂ) / (1 - (t : ℂ) * infinitesimalScale θ)‖ *
      (1 / (4 * (θ : ℝ))) < 1 := by
  have hθ : 0 < 4 * (θ : ℝ) := mul_pos (by norm_num) θ.property.1
  have hnorm : ‖infinitesimalScale θ‖ = 1 / (4 * (θ : ℝ)) := by
    simp only [infinitesimalScale, norm_div, norm_neg, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ]
  let a : ℂ := (t : ℂ) * infinitesimalScale θ
  have hare : a.re = 0 := by
    simp [a, infinitesimalScale, Complex.mul_re, Complex.div_re]
  have hsq : ‖(1 : ℂ) - a‖ ^ 2 = 1 + ‖a‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, hare]
    ring
  have hlt : ‖a‖ < ‖(1 : ℂ) - a‖ := by
    nlinarith [norm_nonneg a, norm_nonneg ((1 : ℂ) - a)]
  have hdpos : 0 < ‖(1 : ℂ) - a‖ := lt_of_le_of_lt (norm_nonneg a) hlt
  rw [← hnorm, ← norm_mul]
  have heq : ((t : ℂ) / (1 - (t : ℂ) * infinitesimalScale θ)) *
      infinitesimalScale θ = a / (1 - a) := by
    dsimp only [a]
    simp only [div_eq_mul_inv]
    ring
  rw [heq, norm_div]
  exact (div_lt_one hdpos).2 hlt

/-- Actual one-support angular coefficients construct a full-plane bounded
direction, a ball-valued family for every real parameter, and a norm-small
remainder. The same canonical plane solutions have the integral derivative. -/
theorem exists_rightCosetCoefficientSum_canonical_variation
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ) [Countable Γ]
    (hsep : ∀ ζ : ℂ,
      ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
        rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0 →
        rightCosetInfinitesimalZeroExtension θ Γ s v ζ ≠ 0 → u = v) :
    let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
    let ν : ℂ → ℂ := fun ζ => ∑' u : C, rightCosetInfinitesimalZeroExtension θ Γ s u ζ
    ∃ (v : MeasurableBeltramiSpace) (μ : ℝ → MeasurableBeltramiBall)
      (ε : ℝ → MeasurableBeltramiSpace),
      (v : ℂ → ℂ) =ᵐ[volume] ν ∧
      ‖v‖ ≤ 1 / (4 * (θ : ℝ)) ∧
      (∀ t : ℝ, ((μ t).val : ℂ → ℂ) =ᵐ[volume] rightCosetCoefficientSum θ Γ s t) ∧
      (∀ t : ℝ, (μ t).val = (t : ℂ) • (v + ε t)) ∧
      Tendsto ε (𝓝[≠] (0 : ℝ)) (𝓝 0) ∧
      (μ 0).val = 0 ∧
      TendstoLocallyUniformly
        (fun t w => (MeasurableBeltramiBall.normalizedSolution (μ t) w - w) / (t : ℂ))
        (LiZhongQC.ahVar ν) (𝓝[≠] (0 : ℝ)) ∧
      ∀ w : ℂ,
        HasDerivAt (fun t : ℝ => MeasurableBeltramiBall.normalizedSolution (μ t) w)
          (LiZhongQC.ahVar ν w) 0 := by
  let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
  let ν : ℂ → ℂ := fun ζ => ∑' u : C, rightCosetInfinitesimalZeroExtension θ Γ s u ζ
  let B : ℝ := 1 / (4 * (θ : ℝ))
  let a : ℝ → ℂ := fun t => (1 - (t : ℂ) * infinitesimalScale θ)⁻¹
  let lam : ℝ → ℂ := fun t => (t : ℂ) / (1 - (t : ℂ) * infinitesimalScale θ)
  let k : ℝ → ℝ := fun t => ‖lam t‖ * B
  have hB : 0 < B := one_div_pos.mpr (mul_pos (by norm_num) θ.property.1)
  have hνdata := rightCosetCauchySeries_hasSum θ Γ s hsep
  have hm : Measurable ν := hνdata.1
  have hb (ζ : ℂ) : ‖ν ζ‖ ≤ B := hνdata.2.1 ζ
  have hν : LiZhongQC.IsBeltramiCoeff ν univ B := by
    simp only [LiZhongQC.IsBeltramiCoeff, Measure.restrict_univ]
    exact ⟨hm.aestronglyMeasurable, Eventually.of_forall hb⟩
  let hνLp := MeasurableBeltramiBall.coefficientMemLp hν
  let v : MeasurableBeltramiSpace := hνLp.toLp ν
  have hv : (v : ℂ → ℂ) =ᵐ[volume] ν := hνLp.coeFn_toLp
  have hvnorm : ‖v‖ ≤ B := by
    apply lpInfinity_norm_le_of_ae_bound v hB.le
    filter_upwards [hv] with ζ hζ
    rw [hζ]
    exact hb ζ
  have hsum (t : ℝ) (ζ : ℂ) : rightCosetCoefficientSum θ Γ s t ζ = lam t * ν ζ :=
    rightCosetCoefficientSum_eq_scalar θ Γ s t ζ
  have hk₀ (t : ℝ) : 0 ≤ k t := mul_nonneg (norm_nonneg _) hB.le
  have hk (t : ℝ) : k t < 1 := norm_coefficient_scalar_mul_bound_lt_one θ t
  have hμcoeff (t : ℝ) :
      LiZhongQC.IsBeltramiCoeff (rightCosetCoefficientSum θ Γ s t) univ (k t) := by
    have heq : rightCosetCoefficientSum θ Γ s t = fun ζ => lam t * ν ζ :=
      funext (hsum t)
    rw [heq]
    simp only [LiZhongQC.IsBeltramiCoeff, Measure.restrict_univ]
    refine ⟨(measurable_const.mul hm).aestronglyMeasurable, ?_⟩
    apply Eventually.of_forall
    intro ζ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb ζ) (norm_nonneg _)
  let μ : ℝ → MeasurableBeltramiBall := fun t =>
    MeasurableBeltramiBall.ofCoefficient (hk₀ t) (hk t) (hμcoeff t)
  have hμae (t : ℝ) :
      ((μ t).val : ℂ → ℂ) =ᵐ[volume] rightCosetCoefficientSum θ Γ s t :=
    MeasurableBeltramiBall.ofCoefficient_coe_ae (hk₀ t) (hk t) (hμcoeff t)
  have hμclass (t : ℝ) : (μ t).val = lam t • v := by
    apply Lp.ext
    filter_upwards [hμae t, Lp.coeFn_smul (lam t) v, hv] with ζ hμζ hsmul hνζ
    calc
      _ = rightCosetCoefficientSum θ Γ s t ζ := hμζ
      _ = lam t * ν ζ := hsum t ζ
      _ = (lam t • v) ζ := by
        simpa only [Pi.smul_apply, smul_eq_mul, hνζ] using hsmul.symm
  let ε : ℝ → MeasurableBeltramiSpace := fun t => (a t - 1) • v
  have hvadd (t : ℝ) : v + ε t = a t • v := by
    calc
      _ = (1 : ℂ) • v + (a t - 1) • v := by simp only [ε, one_smul]
      _ = ((1 : ℂ) + (a t - 1)) • v := (add_smul _ _ _).symm
      _ = a t • v := by congr 1; ring
  have hμdecomp (t : ℝ) : (μ t).val = (t : ℂ) • (v + ε t) := by
    rw [hμclass t, hvadd t, smul_smul]
    simp only [lam, a, div_eq_mul_inv]
  have ha : Tendsto a (𝓝 (0 : ℝ)) (𝓝 (1 : ℂ)) := by
    have hden : Tendsto (fun t : ℝ => 1 - (t : ℂ) * infinitesimalScale θ)
        (𝓝 (0 : ℝ)) (𝓝 (1 : ℂ)) := by
      simpa only [Complex.ofReal_zero, zero_mul, sub_zero] using
        (tendsto_const_nhds (x := (1 : ℂ))).sub
          ((Complex.continuous_ofReal.tendsto 0).mul_const (infinitesimalScale θ))
    simpa only [inv_one] using hden.inv₀ (one_ne_zero : (1 : ℂ) ≠ 0)
  have hε : Tendsto ε (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have hfull : Tendsto (fun t : ℝ => (a t - 1) • v)
        (𝓝 (0 : ℝ)) (𝓝 (0 : MeasurableBeltramiSpace)) := by
      simpa only [sub_self, zero_smul] using
        (ha.sub (tendsto_const_nhds (x := (1 : ℂ)))).smul_const v
    exact hfull.mono_left nhdsWithin_le_nhds
  have hzero : (μ 0).val = 0 := by
    rw [hμclass 0]
    simp only [lam, Complex.ofReal_zero, zero_div, zero_smul]
  have hvar : Quasiconformal.firstVariation v = LiZhongQC.ahVar ν := by
    funext w
    exact Quasiconformal.firstVariation_eq_of_ae v hv w
  refine ⟨v, μ, ε, hv, hvnorm, hμae, hμdecomp, hε, hzero, ?_, ?_⟩
  · rw [← hvar]
    exact Quasiconformal.normalizedSolution_real_parameter_firstVariation v hε μ
      (Eventually.of_forall hμdecomp)
  · intro w
    rw [← hvar]
    exact Quasiconformal.normalizedSolution_real_parameter_hasDerivAt v hε μ
      (Eventually.of_forall hμdecomp) hzero w

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
