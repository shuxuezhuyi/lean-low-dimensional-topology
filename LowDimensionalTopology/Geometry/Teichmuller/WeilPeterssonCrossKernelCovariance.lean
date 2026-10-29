module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSourceKernels
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Covariance of the same cross-half-plane Cauchy-square factors

The actual special-linear action has its literal fractional-linear formula.
The determinant-one identity gives the cross-difference transformation, and
the three diagonal absolute factors cancel exactly against the three squared
height densities. No operator or convergence hypothesis occurs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open GammaMeasurableBeltrami

private theorem denominator_conj_ne_zero (γ : Deck) (z : ℍ) :
    conj (denominator γ z) ≠ 0 := by
  intro h
  apply denominator_ne_zero γ z
  simpa only [Complex.conj_conj, map_zero] using congrArg conj h

private theorem deck_fraction (γ : Deck) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) =
      ((γ 0 0 : ℂ) * z + γ 0 1) / denominator γ z := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [denominator]

private theorem cross_difference_smul (γ : Deck) (ξ η : ℍ) :
    conj ((γ • ξ : ℍ) : ℂ) - ((γ • η : ℍ) : ℂ) =
      (conj (ξ : ℂ) - (η : ℂ)) /
        (conj (denominator γ ξ) * denominator γ η) := by
  have hd : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
    exact_mod_cast LiZhongQC.b33_d_det γ
  rw [deck_fraction, deck_fraction]
  simp only [map_div₀, map_add, map_mul, Complex.conj_ofReal]
  field_simp [denominator_ne_zero γ η, denominator_conj_ne_zero γ ξ]
  unfold denominator
  simp only [map_add, map_mul, Complex.conj_ofReal]
  linear_combination (conj (ξ : ℂ) - (η : ℂ)) * hd

/-- The actual upper cross-kernel retains its two literal denominator factors. -/
theorem cauchySquare_cross_smul (γ : Deck) (ξ η : ℍ) :
    cauchySquare (conj ((γ • ξ : ℍ) : ℂ)) ((γ • η : ℍ) : ℂ) =
      conj (denominator γ ξ) ^ 2 * denominator γ η ^ 2 *
        cauchySquare (conj (ξ : ℂ)) η := by
  unfold cauchySquare
  rw [cross_difference_smul, div_pow, one_div_div, mul_pow]
  simp only [div_eq_mul_inv, one_mul]

/-- Conjugation gives the same actual lower cross-kernel transformation. -/
theorem cauchySquare_lower_smul (γ : Deck) (ξ η : ℍ) :
    cauchySquare ((γ • ξ : ℍ) : ℂ) (conj ((γ • η : ℍ) : ℂ)) =
      denominator γ ξ ^ 2 * conj (denominator γ η) ^ 2 *
        cauchySquare ξ (conj (η : ℂ)) := by
  have hc (a b : ℍ) : cauchySquare a (conj (b : ℂ)) =
      conj (cauchySquare (conj (a : ℂ)) b) := by
    simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
  rw [hc, cauchySquare_cross_smul]
  simp only [map_mul, map_pow, Complex.conj_conj, ← hc]

/-- The literal absolute product on the mixed-kernel diagonal. -/
def diagonalCrossAbsolute (ζ ξ η : ℍ) : ℝ :=
  ‖cauchySquare (conj (ξ : ℂ)) ζ * cauchySquare (conj (ξ : ℂ)) η *
    cauchySquare η (conj (ζ : ℂ))‖

/-- The exact squared-height density cancels the diagonal product's actual
special-linear covariance, for every three original upper points. -/
theorem diagonalCrossAbsolute_density_smul (γ : Deck) (ζ ξ η : ℍ) :
    ((γ • ζ : ℍ).im ^ 2 * (γ • ξ : ℍ).im ^ 2 * (γ • η : ℍ).im ^ 2) *
        diagonalCrossAbsolute (γ • ζ) (γ • ξ) (γ • η) =
      (ζ.im ^ 2 * ξ.im ^ 2 * η.im ^ 2) * diagonalCrossAbsolute ζ ξ η := by
  have him (z : ℍ) : (γ • z : ℍ).im = z.im / Complex.normSq (denominator γ z) := by
    simp [MulAction.compHom_smul_def, UpperHalfPlane.im_smul_eq_div_normSq,
      Matrix.SpecialLinearGroup.det_mapGL, UpperHalfPlane.denom, denominator]
  have hn (z : ℍ) : ‖denominator γ z‖ ≠ 0 := norm_ne_zero_iff.mpr (denominator_ne_zero γ z)
  unfold diagonalCrossAbsolute
  rw [cauchySquare_cross_smul, cauchySquare_cross_smul, cauchySquare_lower_smul]
  simp only [norm_mul, norm_pow, Complex.norm_conj, him, Complex.normSq_eq_norm_sq]
  field_simp [hn ζ, hn ξ, hn η]

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
