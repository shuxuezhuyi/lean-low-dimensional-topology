module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertKernelErrors
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertDiscDerivative
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The derivative of the actual renormalized inverse-norm convolution

At one fixed large radius, a local equality with finite disc potentials
and differentiable error integrals gives the full real derivative. The
two finite-disc Wirtinger limits and the two vanishing error limits then
identify the Wirtinger derivative of the original convolution.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The total integral retains the real-valued form of its literal
inverse-distance integrand, including at totalized poles. -/
theorem renormalizedInverseNormConvolution_eq_ofReal_integral (w z : ℂ) :
    renormalizedInverseNormConvolution w z =
      Complex.ofReal (∫ t : ℂ, (‖t - w‖⁻¹ - ‖t‖⁻¹) * ‖z - t‖⁻¹) := by
  unfold renormalizedInverseNormConvolution
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    simp only [renormalizedInverseNormConvolutionIntegrand,
      renormalizedInverseNormKernel, inverseNormKernel,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_inv]

/-- The original convolution has zero imaginary part. -/
theorem im_renormalizedInverseNormConvolution (w z : ℂ) :
    (renormalizedInverseNormConvolution w z).im = 0 := by
  simp only [renormalizedInverseNormConvolution_eq_ofReal_integral, Complex.ofReal_im]

/-- Complex conjugation fixes the original convolution pointwise. -/
theorem conj_renormalizedInverseNormConvolution (w z : ℂ) :
    conj (renormalizedInverseNormConvolution w z) =
      renormalizedInverseNormConvolution w z := by
  simp only [renormalizedInverseNormConvolution_eq_ofReal_integral, Complex.conj_ofReal]

private theorem renormalizedInverseNormConvolution_eventuallyEq_decomposition
    {R : ℝ} (hR : 0 < R) {w z : ℂ} (hz : z ≠ 0) (hzw : z ≠ w) :
    renormalizedInverseNormConvolution w =ᶠ[𝓝 z]
      fun x : ℂ => inverseNormDiscPotential R (x - w) - inverseNormDiscPotential R x -
        inverseNormRecenteringError R w x + renormalizedInverseNormConvolutionTail R w x := by
  filter_upwards [eventually_ne_nhds hz, eventually_ne_nhds hzw] with x hx0 hxw
  exact renormalizedInverseNormConvolution_eq_disc_sub_error_add_tail hR hx0 hxw

/-- A single sufficiently large radius gives the full real derivative of
the original convolution by a local equality with four differentiable
actual functions. -/
theorem hasFDerivAt_renormalizedInverseNormConvolution_of_radius
    {R : ℝ} {w z : ℂ} (hz : z ≠ 0) (hzw : z ≠ w)
    (hR : 4 * (‖z‖ + ‖w‖ + 1) < R) :
    HasFDerivAt (renormalizedInverseNormConvolution w)
      (fderiv ℝ (inverseNormDiscPotential R) (z - w) -
        fderiv ℝ (inverseNormDiscPotential R) z -
        fderiv ℝ (inverseNormRecenteringError R w) z +
        fderiv ℝ (renormalizedInverseNormConvolutionTail R w) z) z := by
  have hR0 : 0 < R := by linarith [norm_nonneg z, norm_nonneg w]
  have hzR : ‖z‖ < R := by linarith [norm_nonneg z, norm_nonneg w]
  have hzwR : ‖z - w‖ < R := by
    have htri := norm_sub_le z w
    linarith [norm_nonneg z, norm_nonneg w]
  have hd₁ : HasFDerivAt (inverseNormDiscPotential R)
      (fderiv ℝ (inverseNormDiscPotential R) (z - w)) (z - w) :=
    ((hasFDerivAt_inverseNormDiscPotential
      (sub_ne_zero.mpr hzw) hzwR).differentiableAt).hasFDerivAt
  have h₁ : HasFDerivAt (fun x : ℂ => inverseNormDiscPotential R (x - w))
      (fderiv ℝ (inverseNormDiscPotential R) (z - w)) z := by
    convert! hd₁.comp z ((hasFDerivAt_id z).sub_const w) using 1
  have h₂ : HasFDerivAt (inverseNormDiscPotential R)
      (fderiv ℝ (inverseNormDiscPotential R) z) z :=
    (hasFDerivAt_inverseNormDiscPotential hz hzR).differentiableAt.hasFDerivAt
  have h₃ : HasFDerivAt (inverseNormRecenteringError R w)
      (fderiv ℝ (inverseNormRecenteringError R w) z) z :=
    (hasFDerivAt_inverseNormRecenteringError hz hR).differentiableAt.hasFDerivAt
  have h₄ : HasFDerivAt (renormalizedInverseNormConvolutionTail R w)
      (fderiv ℝ (renormalizedInverseNormConvolutionTail R w) z) z :=
    ((hasFDerivAt_renormalizedInverseNormConvolutionTail
      hz hzw hR).differentiableAt).hasFDerivAt
  have hsum : HasFDerivAt
      (fun x : ℂ => inverseNormDiscPotential R (x - w) - inverseNormDiscPotential R x -
        inverseNormRecenteringError R w x + renormalizedInverseNormConvolutionTail R w x)
      (fderiv ℝ (inverseNormDiscPotential R) (z - w) -
        fderiv ℝ (inverseNormDiscPotential R) z -
        fderiv ℝ (inverseNormRecenteringError R w) z +
        fderiv ℝ (renormalizedInverseNormConvolutionTail R w) z) z :=
    ((h₁.sub h₂).sub h₃).add h₄
  exact hsum.congr_of_eventuallyEq
    (renormalizedInverseNormConvolution_eventuallyEq_decomposition hR0 hz hzw)

/-- The actual convolution is real differentiable away from its two
evaluation poles. -/
theorem differentiableAt_renormalizedInverseNormConvolution {w z : ℂ}
    (hz : z ≠ 0) (hzw : z ≠ w) :
    DifferentiableAt ℝ (renormalizedInverseNormConvolution w) z := by
  exact (hasFDerivAt_renormalizedInverseNormConvolution_of_radius
    (R := 4 * (‖z‖ + ‖w‖ + 1) + 1) hz hzw (by linarith)).differentiableAt

/-- Uniqueness of the real derivative differentiates the actual local
decomposition at every sufficiently large radius. -/
theorem dz_renormalizedInverseNormConvolution_eq_disc_sub_error_add_tail
    {R : ℝ} {w z : ℂ} (hz : z ≠ 0) (hzw : z ≠ w)
    (hR : 4 * (‖z‖ + ‖w‖ + 1) < R) :
    LiZhongQC.dz (renormalizedInverseNormConvolution w) z =
      LiZhongQC.dz (inverseNormDiscPotential R) (z - w) -
        LiZhongQC.dz (inverseNormDiscPotential R) z -
        LiZhongQC.dz (inverseNormRecenteringError R w) z +
        LiZhongQC.dz (renormalizedInverseNormConvolutionTail R w) z := by
  have hd := hasFDerivAt_renormalizedInverseNormConvolution_of_radius hz hzw hR
  simp only [LiZhongQC.dz, hd.fderiv, add_apply, sub_apply]
  ring

/-- The Wirtinger derivative of the actual renormalized convolution has
the two original rational poles with their exact coefficients. -/
theorem dz_renormalizedInverseNormConvolution {w z : ℂ}
    (hz : z ≠ 0) (hzw : z ≠ w) :
    LiZhongQC.dz (renormalizedInverseNormConvolution w) z =
      -(Real.pi : ℂ) / (z - w) + (Real.pi : ℂ) / z := by
  have h₁ := tendsto_dz_inverseNormDiscPotential (sub_ne_zero.mpr hzw)
  have h₂ := tendsto_dz_inverseNormDiscPotential hz
  have h₃ := tendsto_dz_inverseNormRecenteringError (w := w) hz
  have h₄ := tendsto_dz_renormalizedInverseNormConvolutionTail hz hzw
  have hlim : Tendsto
      (fun R : ℝ => LiZhongQC.dz (inverseNormDiscPotential R) (z - w) -
        LiZhongQC.dz (inverseNormDiscPotential R) z -
        LiZhongQC.dz (inverseNormRecenteringError R w) z +
        LiZhongQC.dz (renormalizedInverseNormConvolutionTail R w) z)
      atTop (𝓝 (-(Real.pi : ℂ) / (z - w) + (Real.pi : ℂ) / z)) := by
    simpa only [neg_div, sub_neg_eq_add, sub_zero, add_zero] using ((h₁.sub h₂).sub h₃).add h₄
  have heq : (fun _R : ℝ => LiZhongQC.dz (renormalizedInverseNormConvolution w) z) =ᶠ[atTop]
      fun R : ℝ => LiZhongQC.dz (inverseNormDiscPotential R) (z - w) -
        LiZhongQC.dz (inverseNormDiscPotential R) z -
        LiZhongQC.dz (inverseNormRecenteringError R w) z +
        LiZhongQC.dz (renormalizedInverseNormConvolutionTail R w) z := by
    filter_upwards [eventually_gt_atTop (4 * (‖z‖ + ‖w‖ + 1))] with R hR
    exact dz_renormalizedInverseNormConvolution_eq_disc_sub_error_add_tail hz hzw hR
  have hconst : Tendsto
      (fun _R : ℝ => LiZhongQC.dz (renormalizedInverseNormConvolution w) z)
      atTop (𝓝 (-(Real.pi : ℂ) / (z - w) + (Real.pi : ℂ) / z)) :=
    (Filter.tendsto_congr' heq).mpr hlim
  exact tendsto_nhds_unique tendsto_const_nhds hconst

end LowDimensionalTopology.Geometry.Quasiconformal
