module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertConvolutionLogFormula
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertLogGreen
public import Mathlib.Tactic.Ring

/-!
# The compact-test Green identity for the original convolution

The original renormalized convolution agrees almost everywhere with its
explicit logarithmic difference. The two genuine logarithmic Green
identities therefore give the compact-test integration-by-parts formula
with the original rational poles and normalization.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- A compact continuous test times the original convolution is genuinely
integrable, including when its support contains either evaluation pole. -/
theorem integrable_compactTest_mul_renormalizedInverseNormConvolution
    {ψ : ℂ → ℂ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (w : ℂ) :
    Integrable (fun z : ℂ => ψ z * renormalizedInverseNormConvolution w z) volume := by
  have h₀ := integrable_compactTest_mul_realLogNormKernel hψ hc (0 : ℂ)
  simp only [sub_zero] at h₀
  have hw := integrable_compactTest_mul_realLogNormKernel hψ hc w
  have hi := (h₀.sub hw).const_mul (2 * (Real.pi : ℂ))
  refine hi.congr ?_
  filter_upwards [ae_renormalizedInverseNormConvolution_eq_logKernel w] with z hz
  rw [hz, renormalizedLogNormKernel]
  simp only [Pi.sub_apply]
  ring

/-- The compact-test integration-by-parts formula for the literal
renormalized convolution on the original complex plane. -/
theorem integral_dz_mul_renormalizedInverseNormConvolution {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) (w : ℂ) :
    (∫ z : ℂ, LiZhongQC.dz φ z * renormalizedInverseNormConvolution w z) =
      (Real.pi : ℂ) *
        ((∫ z : ℂ, φ z / (z - w)) - (∫ z : ℂ, φ z / z)) := by
  have hφ₁ : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hdzc := LiZhongQC.dz_hasCompactSupport hc
  have hdzcont := LiZhongQC.continuous_dz hφ₁
  have h₀ := integrable_compactTest_mul_realLogNormKernel hdzcont hdzc (0 : ℂ)
  simp only [sub_zero] at h₀
  have hw := integrable_compactTest_mul_realLogNormKernel hdzcont hdzc w
  have hgreen₀ := integral_dz_mul_realLogNormKernel hφ₁ hc (0 : ℂ)
  simp only [sub_zero] at hgreen₀
  have hgreenw := integral_dz_mul_realLogNormKernel hφ₁ hc w
  calc
    (∫ z : ℂ, LiZhongQC.dz φ z * renormalizedInverseNormConvolution w z) =
        ∫ z : ℂ, (2 * (Real.pi : ℂ)) *
          (LiZhongQC.dz φ z * realLogNormKernel z -
            LiZhongQC.dz φ z * realLogNormKernel (z - w)) := by
      apply integral_congr_ae
      filter_upwards [ae_renormalizedInverseNormConvolution_eq_logKernel w] with z hz
      rw [hz, renormalizedLogNormKernel]
      ring
    _ = (2 * (Real.pi : ℂ)) *
        ((∫ z : ℂ, LiZhongQC.dz φ z * realLogNormKernel z) -
          (∫ z : ℂ, LiZhongQC.dz φ z * realLogNormKernel (z - w))) := by
      rw [integral_const_mul, integral_sub h₀ hw]
    _ = _ := by
      rw [hgreen₀, hgreenw]
      ring

end LowDimensionalTopology.Geometry.Quasiconformal
