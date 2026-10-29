module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertPotential

/-!
# The renormalized inverse-norm potential

The difference kernel retains the original integration variable and pole.
For compact C1 tests its integral is an actual integrable difference, and
its Wirtinger derivative agrees with the unrenormalized potential.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The inverse-norm kernel with its value at the reference pole subtracted. -/
def renormalizedInverseNormKernel (z ζ : ℂ) : ℂ :=
  inverseNormKernel (z - ζ) - inverseNormKernel z

/-- The actual difference-kernel potential on the original complex plane. -/
def renormalizedInverseNormPotential (φ : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  ∫ z : ℂ, φ z * renormalizedInverseNormKernel z ζ

/-- The convolution potential has the original-variable integral formula. -/
theorem inverseNormPotential_eq_integral (φ : ℂ → ℂ) (ζ : ℂ) :
    inverseNormPotential φ ζ = ∫ z : ℂ, φ z * inverseNormKernel (z - ζ) := by
  unfold inverseNormPotential
  rw [convolution_def]
  symm
  rw [← integral_sub_left_eq_self
    (fun z : ℂ => φ z * inverseNormKernel (z - ζ)) volume ζ]
  apply integral_congr_ae
  filter_upwards with z
  simp [inverseNormKernel, mul_comm]

/-- Compact continuity supplies genuine integrability at every pole. -/
theorem integrable_inverseNormPotential {φ : ℂ → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (ζ : ℂ) :
    Integrable (fun z : ℂ => φ z * inverseNormKernel (z - ζ))
      (volume : Measure ℂ) := by
  have h := (hc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_inverseNormKernel hφ ζ).integrable_swap
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [ContinuousLinearMap.mul_apply']
  rw [show inverseNormKernel (ζ - z) = inverseNormKernel (z - ζ) by
    simp only [inverseNormKernel, norm_sub_rev]]
  exact mul_comm _ _

/-- On compact continuous tests the renormalization subtracts one actual
constant value of the same potential. -/
theorem renormalizedInverseNormPotential_eq_sub {φ : ℂ → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (ζ : ℂ) :
    renormalizedInverseNormPotential φ ζ =
      inverseNormPotential φ ζ - inverseNormPotential φ 0 := by
  have hζ := integrable_inverseNormPotential hφ hc ζ
  have h0 := integrable_inverseNormPotential hφ hc 0
  simp only [sub_zero] at h0
  have heq : (fun z : ℂ => φ z * renormalizedInverseNormKernel z ζ) =
      fun z : ℂ => φ z * inverseNormKernel (z - ζ) - φ z * inverseNormKernel z := by
    funext z
    simp only [renormalizedInverseNormKernel, mul_sub]
  rw [renormalizedInverseNormPotential, heq, integral_sub hζ h0,
    inverseNormPotential_eq_integral, inverseNormPotential_eq_integral]
  simp only [sub_zero]

/-- Renormalization changes no Wirtinger derivative for a compact C1 test. -/
theorem dz_renormalizedInverseNormPotential {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (ζ : ℂ) :
    LiZhongQC.dz (renormalizedInverseNormPotential φ) ζ =
      LiZhongQC.dz (inverseNormPotential φ) ζ := by
  have heq : renormalizedInverseNormPotential φ =
      fun w => inverseNormPotential φ w - inverseNormPotential φ 0 := by
    funext w
    exact renormalizedInverseNormPotential_eq_sub hφ.continuous hc w
  rw [heq, LiZhongQC.dz_sub_pointwise
    ((contDiff_inverseNormPotential hφ hc).differentiable one_ne_zero ζ)
    (differentiableAt_const (inverseNormPotential φ 0))]
  simp [LiZhongQC.dz]

end LowDimensionalTopology.Geometry.Quasiconformal
