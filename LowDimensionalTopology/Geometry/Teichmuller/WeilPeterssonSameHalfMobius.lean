module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSourceKernels
public import LowDimensionalTopology.Geometry.Teichmuller.GammaLpOperators
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S23_QCOnSurfaces

/-!
# The same-half-plane Cauchy factors under the actual deck action

The existing determinant-one Möbius difference identity gives the literal
first-order difference and its inverse square on the original upper half-plane.
The formulas also hold when the two points coincide. No principal-value
transformation, operator identity or change of integration domain is asserted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open GammaMeasurableBeltrami

/-- The exact difference of two actual upper points after the same deck map. -/
theorem upper_difference_smul (γ : Deck) (ξ η : ℍ) :
    ((γ • ξ : ℍ) : ℂ) - ((γ • η : ℍ) : ℂ) =
      ((ξ : ℂ) - (η : ℂ)) / (denominator γ ξ * denominator γ η) := by
  have hd : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
    exact_mod_cast LiZhongQC.k24_det_realR γ
  rw [LiZhongQC.h36t_coe_smul, LiZhongQC.h36t_coe_smul]
  simpa only [denominator] using
    (LiZhongQC.h36t_mob_sub hd (denominator_ne_zero γ ξ) (denominator_ne_zero γ η))

/-- The original same-half-plane Cauchy square has its two squared deck factors. -/
theorem cauchySquare_upper_smul (γ : Deck) (ξ η : ℍ) :
    cauchySquare ((γ • ξ : ℍ) : ℂ) ((γ • η : ℍ) : ℂ) =
      denominator γ ξ ^ 2 * denominator γ η ^ 2 * cauchySquare ξ η := by
  unfold cauchySquare
  rw [upper_difference_smul, div_pow, one_div_div, mul_pow]
  simp only [div_eq_mul_inv, one_mul]

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
