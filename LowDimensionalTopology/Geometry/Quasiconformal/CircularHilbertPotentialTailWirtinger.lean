module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertPotentialTailDerivative

/-!
# The Wirtinger coefficient of the actual inverse-norm potential tail

The full derivative integral is genuinely integrable. Its two coordinate
values therefore pass through the integral and give exactly one half of
the circular tail kernel, with the sign from the moving evaluation point.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem norm_fderiv_inverseNormKernel_wirtinger_le {v : ℂ} (hv : v ≠ 0) :
    ‖fderiv ℝ inverseNormKernel v‖ ≤ (‖v‖ ^ 2)⁻¹ := by
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [(hasFDerivAt_inverseNormKernel hv).fderiv]
  calc
    ‖Complex.ofRealCLM.comp ((-(‖v‖ ^ 3)⁻¹) • innerSL ℝ v)‖ ≤
        ‖Complex.ofRealCLM‖ * ‖(-(‖v‖ ^ 3)⁻¹) • innerSL ℝ v‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = (‖v‖ ^ 3)⁻¹ * ‖v‖ := by
      rw [Complex.ofRealCLM_norm, one_mul, norm_smul, innerSL_apply_norm]
      simp only [Real.norm_eq_abs, abs_neg, abs_inv, abs_pow,
        abs_of_nonneg (norm_nonneg v)]
    _ = (‖v‖ ^ 2)⁻¹ := by field_simp [hv0.ne']

/-- The derivative integrand of an actual potential tail is integrable,
so its coordinate values can be integrated separately. -/
theorem integrable_inverseNormPotentialTailDerivative {p : ℝ} (hp : 1 < p)
    {d : ℂ → ℂ} (hd : MemLp d (ENNReal.ofReal p) (volume : Measure ℂ)) (z : ℂ)
    {r : ℝ} (hr : 0 < r) (hzero : ∀ t : ℂ, ‖t - z‖ ≤ r → d t = 0) :
    Integrable (fun t : ℂ => d t • ((fderiv ℝ inverseNormKernel (t - z)).comp
      (-ContinuousLinearMap.id ℝ ℂ))) (volume : Measure ℂ) := by
  have hi : Integrable (fun t : ℂ => d t / (t - z) ^ 2) (volume : Measure ℂ) := by
    have htail := LiZhongQC.integrableOn_truncated_kernel hp hd z hr
    apply htail.integrable_of_forall_notMem_eq_zero
    intro t ht
    rw [hzero t (le_of_not_gt ht), zero_div]
  have hmeas : AEStronglyMeasurable
      (fun t : ℂ => d t • ((fderiv ℝ inverseNormKernel (t - z)).comp
        (-ContinuousLinearMap.id ℝ ℂ))) (volume : Measure ℂ) := by
    have hcomp : Continuous
        (fun A : ℂ →L[ℝ] ℂ => A.comp (-ContinuousLinearMap.id ℝ ℂ)) :=
      continuous_id.clm_comp_const _
    have hm : Measurable (fun t : ℂ => (fderiv ℝ inverseNormKernel (t - z)).comp
        (-ContinuousLinearMap.id ℝ ℂ)) :=
      hcomp.measurable.comp
        ((measurable_fderiv ℝ inverseNormKernel).comp (measurable_id.sub_const z))
    exact hd.aestronglyMeasurable.smul hm.aestronglyMeasurable
  refine hi.norm.mono' hmeas (Eventually.of_forall fun t => ?_)
  by_cases ht : d t = 0
  · simp only [ht, zero_smul, norm_zero, zero_div, le_refl]
  · have htz : t - z ≠ 0 := by
      intro h
      apply ht
      apply hzero
      rw [h, norm_zero]
      exact hr.le
    have hcompnorm : ‖(fderiv ℝ inverseNormKernel (t - z)).comp
        (-ContinuousLinearMap.id ℝ ℂ)‖ ≤ ‖fderiv ℝ inverseNormKernel (t - z)‖ := by
      simpa only [norm_neg, ContinuousLinearMap.norm_id, mul_one] using
        ContinuousLinearMap.opNorm_comp_le
          (fderiv ℝ inverseNormKernel (t - z)) (-ContinuousLinearMap.id ℝ ℂ)
    calc
      ‖d t • ((fderiv ℝ inverseNormKernel (t - z)).comp
          (-ContinuousLinearMap.id ℝ ℂ))‖ ≤ ‖d t‖ * (‖t - z‖ ^ 2)⁻¹ := by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left
          (hcompnorm.trans (norm_fderiv_inverseNormKernel_wirtinger_le htz)) (norm_nonneg _)
      _ = ‖d t / (t - z) ^ 2‖ := by
        rw [norm_div, norm_pow, div_eq_mul_inv]

/-- The derivative of a potential tail has the exact positive half-kernel
coefficient after differentiating the moving pole. -/
theorem dz_renormalizedInverseNormPotential_of_vanishing {p : ℝ} (hp : 1 < p)
    {d : ℂ → ℂ} (hd : MemLp d (ENNReal.ofReal p) (volume : Measure ℂ)) (z : ℂ)
    {r : ℝ} (hr : 0 < r) (hzero : ∀ t : ℂ, ‖t - z‖ ≤ r → d t = 0)
    (hint : Integrable (fun t : ℂ => d t * renormalizedInverseNormKernel t z)
      (volume : Measure ℂ)) :
    LiZhongQC.dz (renormalizedInverseNormPotential d) z =
      (1 / 2 : ℂ) * ∫ t : ℂ, d t / ((t - z) * (‖t - z‖ : ℂ)) := by
  let D : ℂ → ℂ →L[ℝ] ℂ := fun t => d t •
    ((fderiv ℝ inverseNormKernel (t - z)).comp (-ContinuousLinearMap.id ℝ ℂ))
  have hD : Integrable D (volume : Measure ℂ) :=
    integrable_inverseNormPotentialTailDerivative hp hd z hr hzero
  have hfd := hasFDerivAt_renormalizedInverseNormPotential_of_vanishing hp hd z hr hzero hint
  rw [LiZhongQC.dz, hfd.fderiv]
  change ((∫ t : ℂ, D t) 1 - I * (∫ t : ℂ, D t) I) / 2 = _
  rw [ContinuousLinearMap.integral_apply hD, ContinuousLinearMap.integral_apply hD,
    ← integral_const_mul I,
    ← integral_sub (hD.apply_continuousLinearMap 1)
      ((hD.apply_continuousLinearMap I).const_mul I), ← integral_div]
  calc
    (∫ t : ℂ, (D t 1 - I * D t I) / 2) =
        ∫ t : ℂ, (1 / 2 : ℂ) * (d t / ((t - z) * (‖t - z‖ : ℂ))) := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : d t = 0
      · simp [D, ht]
      · have hu : t - z ≠ 0 := by
          intro h
          apply ht
          apply hzero
          rw [h, norm_zero]
          exact hr.le
        have hDv (v : ℂ) : D t v = -(d t) * fderiv ℝ inverseNormKernel (t - z) v := by
          simp only [D, smul_apply, ContinuousLinearMap.comp_apply, neg_apply,
            ContinuousLinearMap.id_apply, map_neg, smul_eq_mul]
          ring
        have hcoord : (D t 1 - I * D t I) / 2 =
            -(d t) * LiZhongQC.dz inverseNormKernel (t - z) := by
          rw [hDv, hDv, LiZhongQC.dz]
          ring
        rw [hcoord, dz_inverseNormKernel hu]
        have hρ : (‖t - z‖ : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu)
        have hn : (t - z) * conj (t - z) = (‖t - z‖ : ℂ) ^ 2 := by
          simpa only [Complex.ofReal_pow] using Complex.mul_conj' (t - z)
        have hconj : conj (t - z) = (‖t - z‖ : ℂ) ^ 2 / (t - z) := by
          apply (eq_div_iff hu).mpr
          simpa only [mul_comm] using hn
        rw [hconj]
        field_simp [hu, hρ]
    _ = (1 / 2 : ℂ) * ∫ t : ℂ, d t / ((t - z) * (‖t - z‖ : ℂ)) :=
      integral_const_mul _ _

end LowDimensionalTopology.Geometry.Quasiconformal
