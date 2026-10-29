module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Reciprocal substitution on the original counterclockwise unit circle

The actual parameter reversal and one-period translation prove the identity
without differentiability of the integrand. The total Bochner-integral
identity also includes functions that are not circle integrable.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex MeasureTheory
open scoped Real

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Reciprocal substitution preserves the oriented unit-circle integral
with the literal inverse-square factor. No derivative of `f` is required. -/
theorem circleIntegral_unit_inversion (f : ℂ → ℂ) :
    (∮ z in C(0, 1), f (z⁻¹) / z ^ 2) = ∮ z in C(0, 1), f z := by
  let G : ℝ → ℂ := fun θ => circleMap 0 1 θ * I * f (circleMap 0 1 θ)
  have hG : Function.Periodic G (2 * Real.pi) := by
    intro θ
    dsimp only [G]
    rw [(periodic_circleMap 0 1) θ]
  have hinv (θ : ℝ) : circleMap 0 1 (-θ) = (circleMap 0 1 θ)⁻¹ := by
    simpa only [inv_one] using (circleMap_zero_inv 1 θ).symm
  calc
    (∮ z in C(0, 1), f (z⁻¹) / z ^ 2) = ∫ θ in 0..2 * Real.pi, G (-θ) := by
      simp only [circleIntegral, deriv_circleMap, smul_eq_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      have hzero : circleMap 0 1 θ ≠ 0 := by simp
      dsimp only [G]
      rw [hinv]
      field_simp [hzero]
    _ = ∫ θ in -(2 * Real.pi)..0, G θ := by
      rw [intervalIntegral.integral_comp_neg, neg_zero]
    _ = ∫ θ in 0..2 * Real.pi, G θ := by
      simpa only [neg_add_cancel, zero_add] using
        hG.intervalIntegral_add_eq (-(2 * Real.pi)) 0
    _ = ∮ z in C(0, 1), f z := by
      simp only [circleIntegral, deriv_circleMap, smul_eq_mul, G]

end LowDimensionalTopology.Geometry.Quasiconformal
