module

public import LowDimensionalTopology.Geometry.Quasiconformal.RealCauchyHolomorphic
public import LowDimensionalTopology.Geometry.Quasiconformal.OffSupportCauchyKernels
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Uniform decay of the upper-half-plane Cauchy integral

The Cauchy integral and its complex derivative obey inverse-linear and
inverse-square bounds on every region with a positive lower bound on
imaginary part. The existing `OffSupportCauchy.inverse_le_profile` estimate
applies to the original compactly supported real test.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem realCauchy_power_integral_norm_le {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hcompact : HasCompactSupport φ) {R δ : ℝ}
    (hδ : 0 < δ) (hR : ∀ x ∈ tsupport φ, ‖x‖ ≤ R)
    {z : ℂ} (hz : δ ≤ z.im) (n : ℕ) :
    ‖∫ x : ℝ, (φ x : ℂ) / ((x : ℂ) - z) ^ n‖ ≤
      (((1 + R + δ) / δ) * (1 + ‖z‖)⁻¹) ^ n * ∫ x : ℝ, |φ x| := by
  have hz0 : 0 < z.im := hδ.trans_le hz
  have hnorm : Integrable (fun x : ℝ => |φ x|) := by
    simpa only [Real.norm_eq_abs] using
      (hφ.integrable_of_hasCompactSupport hcompact).norm
  have hbound (x : ℝ) :
      ‖(φ x : ℂ) / ((x : ℂ) - z) ^ n‖ ≤
        ((((1 + R + δ) / δ) * (1 + ‖z‖)⁻¹) ^ n) * |φ x| := by
    by_cases hx : φ x = 0
    · simp [hx]
    have hxR : ‖(x : ℂ)‖ ≤ R := by
      simpa only [Complex.norm_real] using hR x (subset_tsupport φ hx)
    have hsep : δ ≤ ‖z - (x : ℂ)‖ := by
      have him := Complex.abs_im_le_norm (z - (x : ℂ))
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, abs_of_pos hz0] at him
      exact hz.trans him
    have hi : ‖(x : ℂ) - z‖⁻¹ ≤ ((1 + R + δ) / δ) * (1 + ‖z‖)⁻¹ := by
      simpa only [norm_inv, norm_sub_rev] using
        OffSupportCauchy.inverse_le_profile hδ hsep hxR
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv,
      ← inv_pow]
    calc
      |φ x| * (‖(x : ℂ) - z‖⁻¹) ^ n ≤
          |φ x| * (((1 + R + δ) / δ) * (1 + ‖z‖)⁻¹) ^ n :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hi n) (abs_nonneg _)
      _ = _ := mul_comm _ _
  calc
    _ ≤ ∫ x : ℝ,
        ((((1 + R + δ) / δ) * (1 + ‖z‖)⁻¹) ^ n) * |φ x| :=
      norm_integral_le_of_norm_le (hnorm.const_mul _) (Filter.Eventually.of_forall hbound)
    _ = _ := integral_const_mul _ _

/-- The actual Cauchy function and its actual derivative have uniform decay
on every closed upper half-plane a positive distance above the real axis.
This is the book's compact-support estimate, with no extra tail premise. -/
theorem exists_realCauchy_decay_profile {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hcompact : HasCompactSupport φ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, δ ≤ z.im →
      ‖realCauchyFunction φ z‖ ≤ M / (1 + ‖z‖) ∧
        ‖deriv (realCauchyFunction φ) z‖ ≤ M / (1 + ‖z‖) ^ 2 := by
  obtain ⟨R, hR0, hR⟩ := hcompact.isCompact.isBounded.exists_pos_norm_le
  let C : ℝ := (1 / Real.pi) * ∫ x : ℝ, |φ x|
  let K : ℝ := (1 + R + δ) / δ
  let M : ℝ := C * (K + K ^ 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (one_div_nonneg.2 Real.pi_pos.le)
      (integral_nonneg fun x => abs_nonneg (φ x))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hCK : C * K ≤ M := by
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg K)) hC
  have hCK2 : C * K ^ 2 ≤ M := by
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hK) hC
  have hnormcoef : ‖((1 / Real.pi : ℝ) : ℂ)‖ = 1 / Real.pi := by
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.2 Real.pi_pos)]
  refine ⟨M, hM, fun z hz => ?_⟩
  have hz0 : 0 < z.im := hδ.trans_le hz
  have hden : 0 ≤ 1 + ‖z‖ := by positivity
  constructor
  · rw [realCauchyFunction, norm_mul, hnormcoef]
    calc
      _ ≤ (1 / Real.pi) *
          ((K * (1 + ‖z‖)⁻¹) * ∫ x : ℝ, |φ x|) := by
        apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.2 Real.pi_pos.le)
        simpa only [pow_one, K] using
          realCauchy_power_integral_norm_le hφ hcompact hδ hR hz 1
      _ = (C * K) / (1 + ‖z‖) := by dsimp [C]; ring
      _ ≤ M / (1 + ‖z‖) := div_le_div_of_nonneg_right hCK hden
  · rw [(hasDerivAt_realCauchyFunction hφ hcompact hz0).deriv, norm_mul, hnormcoef]
    calc
      _ ≤ (1 / Real.pi) *
          ((K * (1 + ‖z‖)⁻¹) ^ 2 * ∫ x : ℝ, |φ x|) := by
        exact mul_le_mul_of_nonneg_left
          (realCauchy_power_integral_norm_le hφ hcompact hδ hR hz 2)
          (one_div_nonneg.2 Real.pi_pos.le)
      _ = (C * K ^ 2) / (1 + ‖z‖) ^ 2 := by
        dsimp [C]
        simp only [div_eq_mul_inv, ← inv_pow, mul_pow]
        ring
      _ ≤ M / (1 + ‖z‖) ^ 2 :=
        div_le_div_of_nonneg_right hCK2 (sq_nonneg _)

end LowDimensionalTopology.Geometry.Quasiconformal
