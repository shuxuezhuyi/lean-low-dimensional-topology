module

public import LowDimensionalTopology.External.LiZhongQC.Ch07.S26_TeichmullerUniqueness
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Ingredients for the general rectangle equality argument

These are next-batch candidates only. They do not change the frozen
rectangle statements or assert the missing boundary length integral.
The general QC integral argument reuses Wu Xiaobin's attributed
LiZhongQC APIs; see the fixed source manifest and THIRD_PARTY_NOTICES.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory LiZhongQC
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller

/-- The existing general QC Jacobian estimate bounds the quadratic
derivative energy on any measurable part of the actual domain. -/
theorem rectangle_general_qc_energy_bound {h : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hqc : IsKQC h D K) {σ : Set ℂ} (hσ : MeasurableSet σ) (hσD : σ ⊆ D) :
    ∫⁻ z in σ, ENNReal.ofReal ((‖dz h z‖ + ‖dzbar h z‖) ^ 2) ≤
      ENNReal.ofReal K * volume (h '' σ) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hqc.2.1
  have hsq : ∀ᵐ z ∂(volume.restrict D),
      (‖dz h z‖ + ‖dzbar h z‖) ^ 2 ≤ K * jacobian h z := by
    filter_upwards [thm9_4_dilatation_ae hqc] with z hz
    have h0 : 0 ≤ ‖dz h z‖ + ‖dzbar h z‖ :=
      add_nonneg (norm_nonneg _) (norm_nonneg _)
    unfold jacobian
    nlinarith
  calc ∫⁻ z in σ, ENNReal.ofReal ((‖dz h z‖ + ‖dzbar h z‖) ^ 2)
      ≤ ∫⁻ z in σ, ENNReal.ofReal K * ENNReal.ofReal (jacobian h z) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hσD hsq] with z hz
        rw [← ENNReal.ofReal_mul hK0]
        exact ENNReal.ofReal_le_ofReal hz
    _ = ENNReal.ofReal K * ∫⁻ z in σ, ENNReal.ofReal (jacobian h z) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * volume (h '' σ) := by
        gcongr
        exact lintegral_jacobian_le_volume_image hqc hσ hσD

/-- The two pointwise equalities forced by the length-area chain imply
the real affine Beltrami coefficient, without a C¹ hypothesis. -/
theorem rectangle_beltrami_of_pointwise_equalities {A B : ℂ} {K : ℝ}
    (hK : 1 ≤ K) (hlt : ‖B‖ < ‖A‖)
    (htriangle : ‖A + B‖ = ‖A‖ + ‖B‖)
    (hsaturation : (‖A‖ + ‖B‖) ^ 2 = K * (‖A‖ ^ 2 - ‖B‖ ^ 2)) :
    B / A = (((K - 1) / (K + 1) : ℝ) : ℂ) := by
  have hApos : 0 < ‖A‖ := (norm_nonneg B).trans_lt hlt
  have hA : A ≠ 0 := norm_pos_iff.mp hApos
  obtain ⟨r, hr, hB⟩ :=
    (z26_norm_add_eq_iff A B 1 (by simp) hA).mp (by simpa using htriangle)
  simp only [mul_one] at hB
  have hBnorm : ‖B‖ = r * ‖A‖ := by
    rw [hB, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hsum : ‖A‖ + ‖B‖ ≠ 0 := ne_of_gt (by positivity)
  have hlinear : ‖A‖ + ‖B‖ = K * (‖A‖ - ‖B‖) := by
    apply mul_left_cancel₀ hsum
    calc (‖A‖ + ‖B‖) * (‖A‖ + ‖B‖) = (‖A‖ + ‖B‖) ^ 2 := by ring
      _ = K * (‖A‖ ^ 2 - ‖B‖ ^ 2) := hsaturation
      _ = (‖A‖ + ‖B‖) * (K * (‖A‖ - ‖B‖)) := by ring
  have hrK : r = (K - 1) / (K + 1) := by
    apply (eq_div_iff (show K + 1 ≠ 0 by linarith)).2
    apply mul_right_cancel₀ hApos.ne'
    rw [hBnorm] at hlinear
    nlinarith [hlinear]
  rw [hB, mul_div_cancel_right₀ _ hA, hrK]

end LowDimensionalTopology.Geometry.Teichmuller
