/-
The real derivative of a norm power is reused from Wu Xiaobin's
Li-Zhong-QC-formalization, commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertPotential
public import LowDimensionalTopology.External.LiZhongQC.Ch03.S15_Distortion

/-!
# The ordinary derivative of the inverse-norm kernel away from its pole

The Wirtinger derivative gives the literal circular singular kernel.
The pole is excluded from this ordinary derivative calculation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex
open scoped ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The full real derivative of `1 / |z|` at a nonzero point. -/
theorem hasFDerivAt_inverseNormKernel {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt inverseNormKernel
      (Complex.ofRealCLM.comp ((-(‖z‖ ^ 3)⁻¹) • innerSL ℝ z)) z := by
  have hc : (-1 : ℝ) * ‖z‖ ^ ((-1 : ℝ) - 2) = -(‖z‖ ^ 3)⁻¹ := by
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  convert! (Complex.ofRealCLM.hasFDerivAt.comp z
    (LiZhongQC.s15_ra_hasFDerivAt_norm_rpow hz (-1))) using 1 <;>
    simp only [Function.comp_def, Complex.ofRealCLM_apply,
      Real.rpow_neg_one, Complex.ofReal_inv, hc]
  funext w
  rfl

/-- The Wirtinger derivative of the inverse norm at a nonzero point. -/
theorem dz_inverseNormKernel {z : ℂ} (hz : z ≠ 0) :
    LiZhongQC.dz inverseNormKernel z =
      -(conj z) / (2 * (‖z‖ : ℂ) ^ 3) := by
  rw [LiZhongQC.dz, (hasFDerivAt_inverseNormKernel hz).fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, Complex.inner, smul_eq_mul]
  apply Complex.ext <;>
    simp [div_eq_mul_inv, Complex.mul_re, Complex.mul_im] <;> ring

/-- Differentiating `-2 / |z|` yields the exact circular singular kernel. -/
theorem dz_negTwo_inverseNormKernel {z : ℂ} (hz : z ≠ 0) :
    LiZhongQC.dz (fun w => (-2 : ℂ) * inverseNormKernel w) z =
      1 / (z * (‖z‖ : ℂ)) := by
  have hdiff := (hasFDerivAt_inverseNormKernel hz).differentiableAt
  have he :
      fderiv ℝ (fun w => (-2 : ℂ) * inverseNormKernel w) z =
        (-2 : ℂ) • fderiv ℝ inverseNormKernel z := by
    have hfun : (-2 : ℂ) • inverseNormKernel =
        fun w : ℂ => (-2 : ℂ) * inverseNormKernel w := by
      funext w
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hfun]
    exact (hdiff.hasFDerivAt.const_smul (-2 : ℂ)).fderiv
  have hdz : LiZhongQC.dz (fun w => (-2 : ℂ) * inverseNormKernel w) z =
      (-2 : ℂ) * LiZhongQC.dz inverseNormKernel z := by
    simp only [LiZhongQC.dz, he, smul_apply, smul_eq_mul]
    ring
  rw [hdz, dz_inverseNormKernel hz]
  have hr : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hn : z * conj z = (‖z‖ : ℂ) ^ 2 := by
    simpa only [Complex.ofReal_pow] using Complex.mul_conj' z
  have hconj : conj z = (‖z‖ : ℂ) ^ 2 / z := by
    apply (eq_div_iff hz).mpr
    simpa only [mul_comm] using hn
  rw [hconj]
  field_simp [hz, hr]

end LowDimensionalTopology.Geometry.Quasiconformal
