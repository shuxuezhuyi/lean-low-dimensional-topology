module

public import LowDimensionalTopology.Geometry.Quasiconformal.RealCauchyKernel
public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The upper-half-plane Poisson integral and its Lp contraction

The same real probability kernel acts on real and complex functions.
The Cauchy distribution and its mass-one theorems are supplied by
Mathlib, Copyright (c) 2026 David Ledvinka, Apache 2.0.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The Poisson integral on a horizontal slice of the upper half-plane.
For positive η its kernel is η / (π ((x - ξ)^2 + η^2)). -/
def realPoissonIntegral {𝕜 : Type*} [RCLike 𝕜]
    (φ : ℝ → 𝕜) (ξ η : ℝ) : 𝕜 :=
  ∫ x : ℝ, cauchyPDFReal ξ η.toNNReal x • φ x

private theorem cauchyPDF_swap (ξ x : ℝ) (γ : ℝ≥0) :
    cauchyPDF ξ γ x = cauchyPDF x γ ξ := by
  simp only [cauchyPDF_def, cauchyPDFReal_def,
    show (x - ξ) ^ 2 = (ξ - x) ^ 2 by ring]

private theorem realPoissonIntegral_eq_cauchyMeasure
    {𝕜 : Type*} [RCLike 𝕜] (φ : ℝ → 𝕜) (ξ : ℝ) {η : ℝ} (hη : 0 < η) :
    realPoissonIntegral φ ξ η = ∫ x : ℝ, φ x ∂cauchyMeasure ξ η.toNNReal := by
  have hγ : η.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hη)
  rw [cauchyMeasure_of_scale_ne_zero ξ hγ,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_cauchyPDF ξ η.toNNReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) φ]
  unfold realPoissonIntegral
  apply integral_congr_ae
  filter_upwards with x
  rw [cauchyPDF_def, ENNReal.toReal_ofReal (cauchyPDF_pos ξ hγ x).le]

private theorem stronglyMeasurable_realPoissonIntegral
    {𝕜 : Type*} [RCLike 𝕜] {φ : ℝ → 𝕜}
    (hφ : Continuous φ) (η : ℝ) :
    StronglyMeasurable (fun ξ : ℝ => realPoissonIntegral φ ξ η) := by
  have hk : Measurable (fun z : ℝ × ℝ => cauchyPDFReal z.1 η.toNNReal z.2) := by
    unfold cauchyPDFReal
    fun_prop
  have hf : StronglyMeasurable (fun z : ℝ × ℝ =>
      cauchyPDFReal z.1 η.toNNReal z.2 • φ z.2) :=
    hk.stronglyMeasurable.smul (hφ.stronglyMeasurable.comp_measurable measurable_snd)
  exact hf.integral_prod_right'

private theorem realPoissonIntegral_enorm_rpow_le
    {𝕜 : Type*} [RCLike 𝕜] {φ : ℝ → 𝕜}
    (hφ : Continuous φ) {p : ℝ} (hp : 2 ≤ p)
    (ξ : ℝ) {η : ℝ} (hη : 0 < η) :
    ‖realPoissonIntegral φ ξ η‖ₑ ^ p ≤
      ∫⁻ x : ℝ, cauchyPDF ξ η.toNNReal x * ‖φ x‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have hγ : η.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hη)
  have hmean : ‖realPoissonIntegral φ ξ η‖ₑ ≤
      eLpNorm' φ p (cauchyMeasure ξ η.toNNReal) := by
    rw [realPoissonIntegral_eq_cauchyMeasure φ ξ hη]
    calc ‖∫ x : ℝ, φ x ∂cauchyMeasure ξ η.toNNReal‖ₑ
        ≤ ∫⁻ x : ℝ, ‖φ x‖ₑ ∂cauchyMeasure ξ η.toNNReal :=
          enorm_integral_le_lintegral_enorm φ
      _ = eLpNorm' φ 1 (cauchyMeasure ξ η.toNNReal) := by
          simp only [eLpNorm'_eq_lintegral_enorm, ENNReal.rpow_one, one_div_one]
      _ ≤ eLpNorm' φ p (cauchyMeasure ξ η.toNNReal) :=
          eLpNorm'_le_eLpNorm'_of_exponent_le zero_lt_one (by linarith)
            (cauchyMeasure ξ η.toNNReal) hφ.aestronglyMeasurable
  calc ‖realPoissonIntegral φ ξ η‖ₑ ^ p
      ≤ (eLpNorm' φ p (cauchyMeasure ξ η.toNNReal)) ^ p :=
        ENNReal.rpow_le_rpow hmean hp0.le
    _ = ∫⁻ x : ℝ, ‖φ x‖ₑ ^ p ∂cauchyMeasure ξ η.toNNReal := by
        rw [eLpNorm'_eq_lintegral_enorm, ← ENNReal.rpow_mul,
          one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
    _ = ∫⁻ x : ℝ, cauchyPDF ξ η.toNNReal x * ‖φ x‖ₑ ^ p := by
        rw [cauchyMeasure_of_scale_ne_zero ξ hγ,
          lintegral_withDensity_eq_lintegral_mul volume
            (measurable_cauchyPDF ξ η.toNNReal) (hφ.stronglyMeasurable.enorm.pow_const p)]
        rfl

/-- The Poisson integral contracts the extended Lp norm on every positive
horizontal slice. This applies to both real and complex continuous tests. -/
theorem realPoissonIntegral_eLpNorm_le
    {𝕜 : Type*} [RCLike 𝕜] {φ : ℝ → 𝕜}
    (hφ : Continuous φ) {p : ℝ} (hp : 2 ≤ p) {η : ℝ} (hη : 0 < η) :
    eLpNorm (fun ξ : ℝ => realPoissonIntegral φ ξ η) (ENNReal.ofReal p) volume ≤
      eLpNorm φ (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hγ : η.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hη)
  have hjoint : Measurable (fun z : ℝ × ℝ =>
      cauchyPDF z.1 η.toNNReal z.2 * ‖φ z.2‖ₑ ^ p) := by
    have hk : Measurable (fun z : ℝ × ℝ => cauchyPDF z.1 η.toNNReal z.2) := by
      unfold cauchyPDF cauchyPDFReal
      fun_prop
    exact hk.mul ((hφ.stronglyMeasurable.enorm.comp measurable_snd).pow_const p)
  have htotal :
      (∫⁻ ξ : ℝ, ‖realPoissonIntegral φ ξ η‖ₑ ^ p) ≤ ∫⁻ x : ℝ, ‖φ x‖ₑ ^ p := by
    calc (∫⁻ ξ : ℝ, ‖realPoissonIntegral φ ξ η‖ₑ ^ p)
        ≤ ∫⁻ ξ : ℝ, ∫⁻ x : ℝ, cauchyPDF ξ η.toNNReal x * ‖φ x‖ₑ ^ p :=
          lintegral_mono fun ξ => realPoissonIntegral_enorm_rpow_le hφ hp ξ hη
      _ = ∫⁻ x : ℝ, ∫⁻ ξ : ℝ, cauchyPDF ξ η.toNNReal x * ‖φ x‖ₑ ^ p :=
          lintegral_lintegral_swap hjoint.aemeasurable
      _ = ∫⁻ x : ℝ, ‖φ x‖ₑ ^ p := by
          apply lintegral_congr
          intro x
          calc (∫⁻ ξ : ℝ, cauchyPDF ξ η.toNNReal x * ‖φ x‖ₑ ^ p)
              = ∫⁻ ξ : ℝ, cauchyPDF x η.toNNReal ξ * ‖φ x‖ₑ ^ p := by
                apply lintegral_congr
                intro ξ
                rw [cauchyPDF_swap ξ x η.toNNReal]
            _ = ‖φ x‖ₑ ^ p := by
                rw [lintegral_mul_const _ (measurable_cauchyPDF x η.toNNReal),
                  lintegral_cauchyPDF_eq_one x hγ, one_mul]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
      ENNReal.ofReal_ne_top (stronglyMeasurable_realPoissonIntegral hφ η).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
      ENNReal.ofReal_ne_top hφ.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  exact ENNReal.rpow_le_rpow htotal (one_div_nonneg.mpr hp0.le)

/-- Continuous compact real or complex tests have Poisson slices in the
same Lp space, with no change in the input exponent. -/
theorem realPoissonIntegral_memLp
    {𝕜 : Type*} [RCLike 𝕜] {φ : ℝ → 𝕜}
    (hφ : Continuous φ) (hcompact : HasCompactSupport φ)
    {p : ℝ} (hp : 2 ≤ p) {η : ℝ} (hη : 0 < η) :
    MemLp (fun ξ : ℝ => realPoissonIntegral φ ξ η) (ENNReal.ofReal p) volume := by
  rw [memLp_iff]
  exact (realPoissonIntegral_eLpNorm_le hφ hp hη).trans_lt
    (hφ.memLp_of_hasCompactSupport hcompact).eLpNorm_lt_top

/-- For a real test, the imaginary part of the Cauchy integral is exactly
its real Poisson integral. -/
theorem realCauchyIntegral_im_eq_realPoissonIntegral {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hcompact : HasCompactSupport φ)
    (ξ : ℝ) {η : ℝ} (hη : 0 < η) :
    (realCauchyIntegral φ ξ η).im = realPoissonIntegral φ ξ η := by
  rw [(realCauchyIntegral_re_im hφ hcompact ξ hη).2, realPoissonIntegral,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [cauchyPDFReal_def, Real.coe_toNNReal η hη.le, smul_eq_mul, div_eq_mul_inv]
  ring

/-- The imaginary Cauchy slice used in the real Riesz argument satisfies
the same extended Lp bound. -/
theorem realCauchyIntegral_im_eLpNorm_le {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hcompact : HasCompactSupport φ)
    {p : ℝ} (hp : 2 ≤ p) {η : ℝ} (hη : 0 < η) :
    eLpNorm (fun ξ : ℝ => (realCauchyIntegral φ ξ η).im) (ENNReal.ofReal p) volume ≤
      eLpNorm φ (ENNReal.ofReal p) volume := by
  simp_rw [realCauchyIntegral_im_eq_realPoissonIntegral hφ hcompact _ hη]
  exact realPoissonIntegral_eLpNorm_le hφ hp hη

/-- The imaginary Cauchy slice of a compact real test belongs to Lp. -/
theorem realCauchyIntegral_im_memLp {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hcompact : HasCompactSupport φ)
    {p : ℝ} (hp : 2 ≤ p) {η : ℝ} (hη : 0 < η) :
    MemLp (fun ξ : ℝ => (realCauchyIntegral φ ξ η).im) (ENNReal.ofReal p) volume := by
  simp_rw [realCauchyIntegral_im_eq_realPoissonIntegral hφ hcompact _ hη]
  exact realPoissonIntegral_memLp hφ hcompact hp hη

end LowDimensionalTopology.Geometry.Quasiconformal
