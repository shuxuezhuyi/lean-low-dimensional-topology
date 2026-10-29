module

public import LowDimensionalTopology.Geometry.Quasiconformal.RealDirectionalHilbert
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The elementary Cauchy-kernel calculation in the unfinished Riesz proof

Writing the Cauchy integral of a real test as `u + iv` identifies its two
kernels. The statements below formalize exactly that calculation. They make
no assertion of harmonicity, boundary convergence, or the unfinished Riesz
inequality.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The upper-half-plane Cauchy integral used in the notes' Riesz calculation. -/
def realCauchyIntegral (φ : ℝ → ℝ) (ξ η : ℝ) : ℂ :=
  ((1 / Real.pi : ℝ) : ℂ) *
    ∫ x : ℝ, (φ x : ℂ) / ((x : ℂ) - ((ξ : ℂ) + (η : ℂ) * I))

private theorem real_cauchy_kernel_re (a x ξ η : ℝ) :
    ((a : ℂ) / ((x : ℂ) - ((ξ : ℂ) + (η : ℂ) * I))).re =
      a * (x - ξ) / ((x - ξ) ^ 2 + η ^ 2) := by
  simp [Complex.div_re, Complex.normSq_apply, pow_two]

private theorem real_cauchy_kernel_im (a x ξ η : ℝ) :
    ((a : ℂ) / ((x : ℂ) - ((ξ : ℂ) + (η : ℂ) * I))).im =
      a * η / ((x - ξ) ^ 2 + η ^ 2) := by
  simp [Complex.div_im, Complex.normSq_apply, pow_two, neg_div]

private theorem integrable_real_cauchy_kernel {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hcompact : HasCompactSupport φ)
    (ξ : ℝ) {η : ℝ} (hη : 0 < η) :
    Integrable (fun x : ℝ =>
      (φ x : ℂ) / ((x : ℂ) - ((ξ : ℂ) + (η : ℂ) * I))) := by
  have hne (x : ℝ) : (x : ℂ) - ((ξ : ℂ) + (η : ℂ) * I) ≠ 0 := by
    intro hz
    exact (ne_of_gt hη) (by simpa using congrArg Complex.im hz)
  have hcontinuous : Continuous (fun x : ℝ =>
      (φ x : ℂ) / ((x : ℂ) - ((ξ : ℂ) + (η : ℂ) * I))) :=
    (Complex.continuous_ofReal.comp hφ).div
      (Complex.continuous_ofReal.sub continuous_const) hne
  have hc : HasCompactSupport (fun x : ℝ =>
      (φ x : ℂ) / ((x : ℂ) - ((ξ : ℂ) + (η : ℂ) * I))) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hcompact ⊢
    exact hcompact.mono fun x hx => by simp [hx]
  exact hcontinuous.integrable_of_hasCompactSupport hc

/-- The real and imaginary parts in the notes' displayed Cauchy-kernel identity.
Smooth compact real tests are included; only continuity and compact support
are needed for this particular calculation. -/
theorem realCauchyIntegral_re_im {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hcompact : HasCompactSupport φ)
    (ξ : ℝ) {η : ℝ} (hη : 0 < η) :
    (realCauchyIntegral φ ξ η).re =
        (1 / Real.pi) * ∫ x : ℝ, φ x * (x - ξ) / ((x - ξ) ^ 2 + η ^ 2) ∧
      (realCauchyIntegral φ ξ η).im =
        (1 / Real.pi) * ∫ x : ℝ, φ x * η / ((x - ξ) ^ 2 + η ^ 2) := by
  have hint := integrable_real_cauchy_kernel hφ hcompact ξ hη
  constructor
  · rw [realCauchyIntegral, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hre := integral_re hint
    simp only [RCLike.re_eq_complex_re] at hre
    rw [← hre]
    simp only [real_cauchy_kernel_re]
  · rw [realCauchyIntegral, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    have him := integral_im hint
    simp only [RCLike.im_eq_complex_im] at him
    rw [← him]
    simp only [real_cauchy_kernel_im]

end LowDimensionalTopology.Geometry.Quasiconformal
