module

public import LowDimensionalTopology.Geometry.Quasiconformal.RieszBookConstant
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Absorbing the two-component factor into the Riesz constant

The real slice estimate has constant D^(-1/2). The two-component
comparison contributes 2^(1/2-1/p). The printed constant D^(-p/2)
absorbs this factor throughout p≥2 and remains exactly one at p=2.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- A quantitative bound on the same denominator used by the real slice
calculation; this is stronger than its upper bound by one. -/
theorem rieszBookDenominator_le_inv {p : ℝ} (hp : 2 ≤ p) :
    rieszBookDenominator p ≤ 1 / (p - 1) := by
  have hp0 : 0 < p := by linarith
  have hden : 0 < p - 1 := by linarith
  have hbase : 1 ≤ p / (p - 1) := (le_div_iff₀ hden).2 (by linarith)
  have hexp : 2 / p ≤ 1 := (div_le_one hp0).2 hp
  have hpow := Real.rpow_le_rpow_of_exponent_le hbase hexp
  rw [Real.rpow_one] at hpow
  calc rieszBookDenominator p ≤ p / (p - 1) - 1 := sub_le_sub_right hpow 1
    _ = 1 / (p - 1) := by
        field_simp [hden.ne']
        ring

/-- The two-component loss is no larger than the real slice constant. -/
theorem riesz_component_factor_le_real_constant {p : ℝ} (hp : 2 ≤ p) :
    (2 : ℝ) ^ ((1 / 2 : ℝ) - 1 / p) ≤
      (rieszBookDenominator p) ^ (-(1 / 2 : ℝ)) := by
  have hp0 : 0 < p := by linarith
  have hden : 0 < p - 1 := by linarith
  have hD : 0 < rieszBookDenominator p := (rieszBookDenominator_bounds hp).1
  have h20 : 0 ≤ 2 / p := div_nonneg (by norm_num) hp0.le
  have h21 : 2 / p ≤ 1 := (div_le_one hp0).2 hp
  have ht0 : 0 ≤ 1 - 2 / p := sub_nonneg.mpr h21
  have ht1 : 1 - 2 / p ≤ 1 := by linarith
  have hBern : (2 : ℝ) ^ (1 - 2 / p) ≤ 1 + (1 - 2 / p) := by
    have h := _root_.rpow_one_add_le_one_add_mul_self
      (s := (1 : ℝ)) (by norm_num) ht0 ht1
    rw [show (1 : ℝ) + 1 = 2 by norm_num, mul_one] at h
    exact h
  have hlinear : 1 + (1 - 2 / p) ≤ p - 1 := by
    have hprod : 0 ≤ (p - 1) * (p - 2) := mul_nonneg (by linarith) (by linarith)
    rw [show 1 + (1 - 2 / p) = (2 * p - 2) / p by
      field_simp [hp0.ne']; ring, div_le_iff₀ hp0]
    nlinarith
  have hmulD : rieszBookDenominator p * (p - 1) ≤ 1 :=
    (le_div_iff₀ hden).mp (rieszBookDenominator_le_inv hp)
  have hinv : p - 1 ≤ (rieszBookDenominator p)⁻¹ := by
    rw [← one_div, le_div_iff₀ hD]
    simpa [mul_comm] using hmulD
  have hroot := Real.rpow_le_rpow
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    ((hBern.trans hlinear).trans hinv) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (1 - 2 / p) * (1 / 2 : ℝ) = (1 / 2 : ℝ) - 1 / p by ring,
    ← Real.rpow_neg_eq_inv_rpow (rieszBookDenominator p) (1 / 2)] at hroot
  exact hroot

/-- The actual printed constant absorbs both the real estimate and the
two-component norm factor, including the endpoint p=2. -/
theorem riesz_real_constant_mul_component_factor_le_book {p : ℝ} (hp : 2 ≤ p) :
    (rieszBookDenominator p) ^ (-(1 / 2 : ℝ)) *
        (2 : ℝ) ^ ((1 / 2 : ℝ) - 1 / p) ≤ rieszBookConstant p := by
  have hD : 0 < rieszBookDenominator p := (rieszBookDenominator_bounds hp).1
  have hfactor := riesz_component_factor_le_real_constant hp
  have hε0 : 0 ≤ (1 / 2 : ℝ) - 1 / p :=
    sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp)
  have hB1 : 1 ≤ (rieszBookDenominator p) ^ (-(1 / 2 : ℝ)) :=
    (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hε0).trans hfactor
  calc (rieszBookDenominator p) ^ (-(1 / 2 : ℝ)) *
        (2 : ℝ) ^ ((1 / 2 : ℝ) - 1 / p)
      ≤ (rieszBookDenominator p) ^ (-(1 / 2 : ℝ)) *
          (rieszBookDenominator p) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hD.le _)
    _ = ((rieszBookDenominator p) ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) := by
        rw [Real.rpow_two, pow_two]
    _ ≤ ((rieszBookDenominator p) ^ (-(1 / 2 : ℝ))) ^ p :=
        Real.rpow_le_rpow_of_exponent_le hB1 hp
    _ = rieszBookConstant p := by
        dsimp [rieszBookConstant]
        rw [← Real.rpow_mul hD.le,
          show (-(1 / 2 : ℝ)) * p = -(p / 2) by ring,
          Real.rpow_neg hD.le, one_div]

/-- Complexification preserves the exact Hilbert-space normalization. -/
theorem riesz_complexification_constant_two :
    (rieszBookDenominator 2) ^ (-(1 / 2 : ℝ)) *
      (2 : ℝ) ^ ((1 / 2 : ℝ) - 1 / 2) = 1 := by
  norm_num [rieszBookDenominator, Real.rpow_one]

end LowDimensionalTopology.Geometry.Quasiconformal
