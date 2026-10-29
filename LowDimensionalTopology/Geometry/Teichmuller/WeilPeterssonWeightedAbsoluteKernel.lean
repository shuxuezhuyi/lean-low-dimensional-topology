module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSourceKernels
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# The actual cross-kernel weighted absolute row integral

The same Cauchy-square kernel is integrated in its literal real coordinates.
The horizontal integral is the existing arctangent integral. The vertical
weight y^(-1/2) has an integrable profile at both zero and infinity. Its actual
scaling gives one common finite row constant for the half-plane kernel.
No operator bound, PV, WP formula or convergence hypothesis is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Real Complex Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

private def verticalAbsoluteProfile (b y : ℝ) : ℝ := y ^ (-(1 / 2 : ℝ)) / (b + y)

private theorem unit_verticalAbsoluteProfile_integrable :
    IntegrableOn (verticalAbsoluteProfile 1) (Ioi 0) := by
  have hm : Measurable (verticalAbsoluteProfile 1) := by
    unfold verticalAbsoluteProfile
    fun_prop
  have hnear : IntegrableOn (verticalAbsoluteProfile 1) (Ioo 0 2) := by
    refine ((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 2)).2
      (by norm_num : -1 < -(1 / 2 : ℝ))).mono' hm.aestronglyMeasurable.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioo fun y hy => ?_
    have hnonneg : 0 ≤ verticalAbsoluteProfile 1 y :=
      div_nonneg (Real.rpow_nonneg hy.1.le (-(1 / 2 : ℝ))) (add_nonneg zero_le_one hy.1.le)
    rw [Real.norm_of_nonneg hnonneg]
    exact div_le_self (Real.rpow_nonneg hy.1.le _) (by linarith [hy.1])
  have hfar : IntegrableOn (verticalAbsoluteProfile 1) (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1)).mono' hm.aestronglyMeasurable.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
    have hy0 : 0 < y := zero_lt_one.trans hy
    rw [Real.norm_of_nonneg (by unfold verticalAbsoluteProfile; positivity)]
    calc
      verticalAbsoluteProfile 1 y ≤ y ^ (-(1 / 2 : ℝ)) / y :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le _) hy0 (by linarith)
      _ = y ^ (-(3 / 2 : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hy0]
        congr 1
        norm_num
  apply (integrableOn_union.mpr ⟨hnear, hfar⟩).mono_set
  intro y hy
  by_cases h : y < 2
  · exact Or.inl ⟨hy, h⟩
  · exact Or.inr ((by norm_num : (1 : ℝ) < 2).trans_le (not_lt.mp h))

private theorem verticalAbsoluteProfile_scale {b : ℝ} (hb : 0 < b) {y : ℝ} (hy : 0 < y) :
    verticalAbsoluteProfile b (b * y) =
      b ^ (-(3 / 2 : ℝ)) * verticalAbsoluteProfile 1 y := by
  have hp : b ^ (-(1 / 2 : ℝ)) / b = b ^ (-(3 / 2 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hb]
    congr 1
    norm_num
  unfold verticalAbsoluteProfile
  rw [Real.mul_rpow hb.le hy.le, ← hp]
  field_simp [hb.ne']

private theorem verticalAbsoluteProfile_integrable_and_integral {b : ℝ} (hb : 0 < b) :
    IntegrableOn (verticalAbsoluteProfile b) (Ioi 0) ∧
      (∫ y in Ioi 0, verticalAbsoluteProfile b y) =
        b ^ (-(1 / 2 : ℝ)) * ∫ y in Ioi 0, verticalAbsoluteProfile 1 y := by
  have hs (y : ℝ) (hy : y ∈ Ioi 0) := verticalAbsoluteProfile_scale hb hy
  have hi : IntegrableOn (fun y => verticalAbsoluteProfile b (b * y)) (Ioi 0) :=
    IntegrableOn.congr_fun
      (unit_verticalAbsoluteProfile_integrable.const_mul (b ^ (-(3 / 2 : ℝ))))
      (fun y hy => (hs y hy).symm) measurableSet_Ioi
  have hactual : IntegrableOn (verticalAbsoluteProfile b) (Ioi 0) := by
    simpa only [mul_zero] using (integrableOn_Ioi_comp_mul_left_iff
      (verticalAbsoluteProfile b) 0 hb).mp hi
  refine ⟨hactual, ?_⟩
  have he := integral_comp_mul_left_Ioi' (verticalAbsoluteProfile b) 0 hb
  simp only [mul_zero, smul_eq_mul] at he
  rw [setIntegral_congr_fun measurableSet_Ioi hs, integral_const_mul] at he
  have hp : b * b ^ (-(3 / 2 : ℝ)) = b ^ (-(1 / 2 : ℝ)) := by
    calc
      _ = b ^ ((1 : ℝ) + -(3 / 2 : ℝ)) := by rw [Real.rpow_add hb, Real.rpow_one]
      _ = _ := by congr 1; norm_num
  rw [← he, ← mul_assoc, hp]

private theorem horizontalCauchy_integrable_and_integral (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => ((x - a) ^ 2 + b ^ 2)⁻¹) ∧
      (∫ x : ℝ, ((x - a) ^ 2 + b ^ 2)⁻¹) = Real.pi / b := by
  have hi := integrable_inv_one_add_mul_sq (b := b⁻¹) (inv_ne_zero hb.ne')
  have ht : Integrable (fun x : ℝ => (1 + (b⁻¹ * (x - a)) ^ 2)⁻¹) := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure ℝ) (-a)).integrable_comp_of_integrable hi
  have he (x : ℝ) : ((x - a) ^ 2 + b ^ 2)⁻¹ =
      (b ^ 2)⁻¹ * (1 + (b⁻¹ * (x - a)) ^ 2)⁻¹ := by
    field_simp [hb.ne']; ring
  have hfun : (fun x : ℝ => ((x - a) ^ 2 + b ^ 2)⁻¹) =
      fun x => (b ^ 2)⁻¹ * (1 + (b⁻¹ * (x - a)) ^ 2)⁻¹ := funext he
  rw [hfun]
  refine ⟨ht.const_mul _, ?_⟩
  rw [integral_const_mul,
    integral_sub_right_eq_self (f := fun x : ℝ => (1 + (b⁻¹ * x) ^ 2)⁻¹),
    integral_univ_inv_one_add_mul_sq, abs_of_pos (inv_pos.mpr hb)]
  field_simp [hb.ne']

private theorem cauchySquare_norm_cartesian (ξ : ℍ) (x y : ℝ) :
    ‖cauchySquare (conj (ξ : ℂ)) ((x : ℂ) + (y : ℂ) * I)‖ =
      ((x - ξ.re) ^ 2 + (y + ξ.im) ^ 2)⁻¹ := by
  rw [cauchySquare, norm_div, norm_one, norm_pow, Complex.sq_norm]
  simp only [Complex.normSq_apply, sub_re, sub_im, conj_re, conj_im,
    add_re, add_im, mul_re, mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, one_div]
  congr 1
  ring

/-- The SAME actual cross-kernel has absolutely convergent weighted real
slices and an integrable outer slice, with its literal common scaling. -/
theorem cauchySquare_weighted_absolute_iterated (ξ : ℍ) :
    (∀ y : ℝ, 0 < y → Integrable (fun x : ℝ =>
      ‖cauchySquare (conj (ξ : ℂ)) ((x : ℂ) + (y : ℂ) * I)‖ * y ^ (-(1 / 2 : ℝ)))) ∧
    IntegrableOn (fun y : ℝ => ∫ x : ℝ,
      ‖cauchySquare (conj (ξ : ℂ)) ((x : ℂ) + (y : ℂ) * I)‖ * y ^ (-(1 / 2 : ℝ))) (Ioi 0) ∧
    (∫ y : ℝ in Ioi 0, ∫ x : ℝ,
      ‖cauchySquare (conj (ξ : ℂ)) ((x : ℂ) + (y : ℂ) * I)‖ * y ^ (-(1 / 2 : ℝ))) =
      Real.pi * (∫ t : ℝ in Ioi 0, t ^ (-(1 / 2 : ℝ)) / (1 + t)) * ξ.im ^ (-(1 / 2 : ℝ)) := by
  have hs (y : ℝ) (hy : y ∈ Ioi 0) :
      (∫ x : ℝ, ‖cauchySquare (conj (ξ : ℂ)) ((x : ℂ) + (y : ℂ) * I)‖ *
        y ^ (-(1 / 2 : ℝ))) = Real.pi * verticalAbsoluteProfile ξ.im y := by
    simp_rw [cauchySquare_norm_cartesian]
    rw [integral_mul_const, (horizontalCauchy_integrable_and_integral ξ.re
      (add_pos hy ξ.im_pos)).2]
    unfold verticalAbsoluteProfile
    ring
  have hi := verticalAbsoluteProfile_integrable_and_integral ξ.im_pos
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    simpa only [cauchySquare_norm_cartesian] using
      (horizontalCauchy_integrable_and_integral ξ.re (add_pos hy ξ.im_pos)).1.mul_const
        (y ^ (-(1 / 2 : ℝ)))
  · exact IntegrableOn.congr_fun (hi.1.const_mul Real.pi)
      (fun y hy => (hs y hy).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi hs, integral_const_mul, hi.2]
    unfold verticalAbsoluteProfile
    ring

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
