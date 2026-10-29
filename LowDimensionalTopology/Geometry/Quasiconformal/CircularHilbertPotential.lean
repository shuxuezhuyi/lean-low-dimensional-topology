/-
The Cauchy-kernel integrability and compact-support differentiation APIs are
reused from Wu Xiaobin's Li-Zhong-QC-formalization, commit
1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.External.LiZhongQC.Ch02.S11_IntegralOperators
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# The inverse-norm potential for the circular Hilbert transform

The inverse-norm kernel is locally integrable on the actual complex plane.
Convolution with a compact smooth test is differentiable, with derivatives
transferred to the test. No principal-value convergence is inferred from a
totalized integral.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The locally integrable inverse-norm kernel on the original complex plane. -/
def inverseNormKernel (z : ℂ) : ℂ := (‖z‖ : ℂ)⁻¹

theorem locallyIntegrable_inverseNormKernel :
    LocallyIntegrable inverseNormKernel (volume : Measure ℂ) := by
  intro x
  refine ⟨Metric.ball (0 : ℂ) (‖x‖ + 1),
    Metric.isOpen_ball.mem_nhds (by simp only [Metric.mem_ball, dist_zero_right]; linarith), ?_⟩
  have hi := LiZhongQC.integrableOn_cauchy_kernel_ball
    (R := ‖x‖ + 1) (by positivity) (0 : ℂ)
  refine Integrable.mono hi ?_ (Eventually.of_forall fun z => ?_)
  · exact ((measurable_ofReal.comp measurable_norm).inv.aestronglyMeasurable).restrict
  · simp [inverseNormKernel, norm_inv, Complex.norm_real]

/-- Convolution by `1 / |z|`, before the circular transform's factor `1 / π`. -/
def inverseNormPotential (φ : ℂ → ℂ) : ℂ → ℂ :=
  convolution inverseNormKernel φ (ContinuousLinearMap.mul ℝ ℂ) volume

/-- The potential is continuously differentiable for a compact C1 test. -/
theorem contDiff_inverseNormPotential {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    ContDiff ℝ 1 (inverseNormPotential φ) :=
  hc.contDiff_convolution_right _ locallyIntegrable_inverseNormKernel hφ

/-- The derivative of the potential is the potential of the test derivative. -/
theorem fderiv_inverseNormPotential_apply {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (z v : ℂ) :
    fderiv ℝ (inverseNormPotential φ) z v =
      inverseNormPotential (fun w => fderiv ℝ φ w v) z := by
  have hd : HasFDerivAt (inverseNormPotential φ)
      (convolution inverseNormKernel (fderiv ℝ φ)
        ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ) volume z) z :=
    hc.hasFDerivAt_convolution_right _ locallyIntegrable_inverseNormKernel hφ z
  have hex := (hc.fderiv (𝕜 := ℝ)).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ) locallyIntegrable_inverseNormKernel
    (hφ.continuous_fderiv one_ne_zero) z
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex,
    inverseNormPotential, convolution_def]
  simp

/-- The inverse-norm potential commutes with the complex Wirtinger derivative
when it is transferred to a compact C1 test. -/
theorem dz_inverseNormPotential {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (z : ℂ) :
    LiZhongQC.dz (inverseNormPotential φ) z =
      inverseNormPotential (LiZhongQC.dz φ) z := by
  rw [LiZhongQC.dz, fderiv_inverseNormPotential_apply hφ hc,
    fderiv_inverseNormPotential_apply hφ hc]
  unfold inverseNormPotential
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  have hi1' := LiZhongQC.hasCompactSupport_fderiv_apply hc (1 : ℂ)
  have hiI' := LiZhongQC.hasCompactSupport_fderiv_apply hc I
  have hint1 := hi1'.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_inverseNormKernel
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const) z
  have hintI := hiI'.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_inverseNormKernel
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const) z
  have hInt1 : Integrable
      (fun t : ℂ => inverseNormKernel t * fderiv ℝ φ (z - t) 1) volume := by
    simpa only [ContinuousLinearMap.mul_apply'] using hint1.integrable
  have hIntI : Integrable
      (fun t : ℂ => inverseNormKernel t * fderiv ℝ φ (z - t) I) volume := by
    simpa only [ContinuousLinearMap.mul_apply'] using hintI.integrable
  have heq :
      (fun t => inverseNormKernel t * LiZhongQC.dz φ (z - t)) =
        fun t => (1 / 2 : ℂ) * (inverseNormKernel t * fderiv ℝ φ (z - t) 1) +
          (-I / 2) * (inverseNormKernel t * fderiv ℝ φ (z - t) I) := by
    funext t
    simp only [LiZhongQC.dz]
    ring
  rw [heq, integral_add (hInt1.const_mul _) (hIntI.const_mul _),
    integral_const_mul, integral_const_mul]
  ring

end LowDimensionalTopology.Geometry.Quasiconformal
