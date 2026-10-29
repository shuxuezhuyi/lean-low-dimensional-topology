module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCrossKernelCovariance
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSameHalfMobius
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The invariant same-half positive exclusion
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate Pointwise ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open GammaMeasurableBeltrami

private theorem invariantCut_cross_norm (a b : ℍ) :
    ‖cauchySquare a (conj (b : ℂ))‖ = ‖cauchySquare (conj (a : ℂ)) b‖ := by
  have hc : cauchySquare (conj (a : ℂ)) b = conj (cauchySquare a (conj (b : ℂ))) := by
    simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
  exact ((congrArg norm hc).trans (Complex.norm_conj _)).symm

/-- The same invariant positive cut as the finite six-factor source density.
The kernel value at the same-half diagonal is already zero. -/
def invariantFourSameHalfKernel (e : ℝ) (ρ η : ℍ) : ℂ :=
  if e ^ 2 * ‖cauchySquare ρ η‖ < ‖cauchySquare ρ (conj (η : ℂ))‖
  then cauchySquare ρ η else 0

theorem invariantFourSameHalfKernel_measurable (e : ℝ) :
    Measurable (fun a : ℍ × ℍ => invariantFourSameHalfKernel e a.1 a.2) := by
  have hk : Measurable (fun a : ℍ × ℍ => cauchySquare a.1 a.2) := by
    unfold cauchySquare
    fun_prop
  have hc : Measurable (fun a : ℍ × ℍ => cauchySquare a.1 (conj (a.2 : ℂ))) := by
    unfold cauchySquare
    fun_prop
  exact Measurable.ite (measurableSet_lt (measurable_const.mul hk.norm) hc.norm)
    hk measurable_const

theorem invariantFourSameHalfKernel_cross_bound (e : ℝ) (he : 0 < e) (ρ η : ℍ) :
    ‖invariantFourSameHalfKernel e ρ η‖ ≤ ‖cauchySquare (conj (ρ : ℂ)) η‖ / e ^ 2 := by
  by_cases h : e ^ 2 * ‖cauchySquare ρ η‖ < ‖cauchySquare ρ (conj (η : ℂ))‖
  · rw [invariantFourSameHalfKernel, ite_eq_left h]
    apply (le_div_iff₀ (sq_pos_of_pos he)).2
    simpa only [invariantCut_cross_norm, mul_comm] using h.le
  · rw [invariantFourSameHalfKernel, ite_eq_right h, norm_zero]
    exact div_nonneg (norm_nonneg _) (sq_nonneg _)

theorem invariantFourSameHalfKernel_original_exclusion (e : ℝ) (he : 0 < e) (ρ η : ℍ) :
    invariantFourSameHalfKernel e ρ η =
      if e * ‖(ρ : ℂ) - conj (η : ℂ)‖ < ‖(ρ : ℂ) - η‖
      then cauchySquare ρ η else 0 := by
  by_cases hρη : ρ = η
  · subst ρ
    simp [invariantFourSameHalfKernel, cauchySquare]
  · have hs : 0 < ‖(ρ : ℂ) - η‖ :=
      norm_pos_iff.2 (sub_ne_zero.2 (UpperHalfPlane.coe_injective.ne hρη))
    have hc : 0 < ‖(ρ : ℂ) - conj (η : ℂ)‖ := by
      have him : 0 < ((ρ : ℂ) - conj (η : ℂ)).im := by
        simpa only [sub_im, conj_im, UpperHalfPlane.coe_im, sub_neg_eq_add] using
          add_pos ρ.im_pos η.im_pos
      exact him.trans_le ((le_abs_self _).trans (Complex.abs_im_le_norm _))
    have hcut : (e ^ 2 * ‖cauchySquare ρ η‖ < ‖cauchySquare ρ (conj (η : ℂ))‖) ↔
        e * ‖(ρ : ℂ) - conj (η : ℂ)‖ < ‖(ρ : ℂ) - η‖ := by
      simp only [cauchySquare, norm_div, norm_one, norm_pow]
      rw [mul_one_div, div_lt_div_iff₀ (sq_pos_of_pos hs) (sq_pos_of_pos hc),
        one_mul, ← mul_pow, sq_lt_sq₀ (mul_nonneg he.le hc.le) hs.le]
    exact if_congr hcut rfl rfl

theorem invariantFourSameHalfKernel_deck (e : ℝ) (γ : Deck) (ρ η : ℍ) :
    invariantFourSameHalfKernel e (γ • ρ) (γ • η) =
      denominator γ ρ ^ 2 * denominator γ η ^ 2 * invariantFourSameHalfKernel e ρ η := by
  let A : ℝ := ‖denominator γ ρ‖ ^ 2 * ‖denominator γ η‖ ^ 2
  have hA : 0 < A := by
    exact mul_pos
      (sq_pos_of_pos (norm_pos_iff.2 (denominator_ne_zero γ ρ)))
      (sq_pos_of_pos (norm_pos_iff.2 (denominator_ne_zero γ η)))
  have hu : ‖cauchySquare (γ • ρ : ℍ) (γ • η : ℍ)‖ = A * ‖cauchySquare ρ η‖ := by
    rw [cauchySquare_upper_smul]
    simp only [norm_mul, norm_pow]
    rfl
  have hc : ‖cauchySquare (γ • ρ : ℍ) (conj ((γ • η : ℍ) : ℂ))‖ =
      A * ‖cauchySquare ρ (conj (η : ℂ))‖ := by
    rw [cauchySquare_lower_smul]
    simp only [norm_mul, norm_pow, Complex.norm_conj]
    rfl
  have hcut : (e ^ 2 * ‖cauchySquare (γ • ρ : ℍ) (γ • η : ℍ)‖ <
      ‖cauchySquare (γ • ρ : ℍ) (conj ((γ • η : ℍ) : ℂ))‖) ↔
      e ^ 2 * ‖cauchySquare ρ η‖ < ‖cauchySquare ρ (conj (η : ℂ))‖ := by
    rw [hu, hc, show e ^ 2 * (A * ‖cauchySquare ρ η‖) =
      A * (e ^ 2 * ‖cauchySquare ρ η‖) by ring, mul_lt_mul_iff_right₀ hA]
  unfold invariantFourSameHalfKernel
  simp only [hcut]
  split_ifs
  · exact cauchySquare_upper_smul γ ρ η
  · exact (mul_zero _).symm


end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
