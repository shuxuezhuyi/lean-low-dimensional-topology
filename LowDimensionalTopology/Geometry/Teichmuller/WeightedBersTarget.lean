module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaSourceCoefficient
public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# A faithful weighted supremum realization of Bers functions

The values on the actual lower half-plane are multiplied by the square of
height and retained pointwise in Mathlib's complete bounded-family space.
Its norm is the literal weighted supremum; no almost-everywhere quotient or
independently chosen topology on raw function space is involved.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

abbrev Lower := {z : ℂ // z ∈ LiZhongQC.lowerHalf}
abbrev Target := lp (fun _ : Lower => ℂ) (∞ : ℝ≥0∞)

/-- The actual positive square-height weight at a lower-half-plane point. -/
def weight (z : Lower) : ℂ := ((z.val.im ^ 2 : ℝ) : ℂ)

theorem weight_ne_zero (z : Lower) : weight z ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (show z.val.im ≠ 0 from ne_of_lt z.property))

/-- Retain every lower-half-plane value with its actual Bers norm weight. -/
def encode (φ : ℂ → ℂ)
    (hφ : ∃ C : ℝ, ∀ z ∈ LiZhongQC.lowerHalf, ‖φ z‖ * z.im ^ 2 ≤ C) : Target := by
  refine ⟨fun z => φ z * weight z, memℓp_infty ?_⟩
  obtain ⟨C, hC⟩ := hφ
  refine ⟨C, ?_⟩
  rintro _ ⟨z, rfl⟩
  simpa only [norm_mul, weight, Complex.norm_real, Real.norm_eq_abs, abs_sq] using hC z z.property

@[simp] theorem encode_apply (φ : ℂ → ℂ) (hφ) (z : Lower) :
    encode φ hφ z = φ z * weight z := rfl

/-- The actual Banach norm is exactly the weighted pointwise supremum. -/
theorem norm_encode (φ : ℂ → ℂ) (hφ) :
    ‖encode φ hφ‖ = ⨆ z : Lower, ‖φ z‖ * z.val.im ^ 2 := by
  rw [lp.norm_eq_ciSup]
  simp only [encode_apply, norm_mul, weight, Complex.norm_real, Real.norm_eq_abs,
    abs_sq]

/-- This realization preserves equality of the original functions on the lower half-plane. -/
theorem encode_eq_iff (φ ψ : ℂ → ℂ) (hφ) (hψ) :
    encode φ hφ = encode ψ hψ ↔ EqOn φ ψ LiZhongQC.lowerHalf := by
  constructor
  · intro h z hz
    exact mul_right_cancel₀ (weight_ne_zero ⟨z, hz⟩)
      (congrArg (fun f : Target => f ⟨z, hz⟩) h)
  · intro h
    apply lp.ext
    funext z
    exact congrArg (fun a : ℂ => a * weight z) (h z.property)

/-- Completeness is inherited from Mathlib's actual supremum-norm space. -/
theorem completeSpace : CompleteSpace Target := inferInstance

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
