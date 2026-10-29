module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertRenormalizedKernel

/-!
# Integrability of the renormalized inverse-norm convolution

The difference of the two inverse-norm kernels has enough cancellation at
infinity to be convolved with a third inverse-norm kernel. Distinct poles
are treated by the local integrability of the Cauchy kernel.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

theorem norm_inverseNormKernel (t : ℂ) :
    ‖inverseNormKernel t‖ = ‖t‖⁻¹ := by
  simp [inverseNormKernel, Complex.norm_real]

theorem measurable_inverseNormKernel : Measurable inverseNormKernel :=
  (measurable_ofReal.comp measurable_norm).inv

/-- A product of two distinct inverse distances is bounded locally by a sum
of the two individual inverse distances. The totalized values at the poles
also satisfy the estimate. -/
theorem inverseNormKernel_mul_norm_le {a b : ℂ} (hab : a ≠ b) (t : ℂ) :
    ‖inverseNormKernel (t - a) * inverseNormKernel (t - b)‖ ≤
      (‖t - a‖⁻¹ + ‖t - b‖⁻¹) / ‖a - b‖ := by
  have hd : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  rw [norm_mul, norm_inverseNormKernel, norm_inverseNormKernel]
  by_cases hta : t = a
  · subst t
    simp only [sub_self, norm_zero, inv_zero, zero_mul, zero_add]
    positivity
  by_cases htb : t = b
  · subst t
    simp only [sub_self, norm_zero, inv_zero, mul_zero, add_zero]
    positivity
  have ha : 0 < ‖t - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hta)
  have hb : 0 < ‖t - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr htb)
  have htri : ‖a - b‖ ≤ ‖t - a‖ + ‖t - b‖ := by
    simpa only [dist_eq_norm, norm_sub_rev a t] using dist_triangle a t b
  apply (le_div_iff₀ hd).mpr
  calc
    ‖t - a‖⁻¹ * ‖t - b‖⁻¹ * ‖a - b‖ ≤
        ‖t - a‖⁻¹ * ‖t - b‖⁻¹ * (‖t - a‖ + ‖t - b‖) :=
      mul_le_mul_of_nonneg_left htri (by positivity)
    _ = ‖t - a‖⁻¹ + ‖t - b‖⁻¹ := by
      field_simp [ha.ne', hb.ne']
      ring

/-- Two distinct inverse-norm singularities give an integrable product on
every bounded disc. -/
theorem integrableOn_inverseNormKernel_mul_ball {R : ℝ} (hR : 0 < R)
    {a b : ℂ} (hab : a ≠ b) :
    IntegrableOn (fun t : ℂ =>
      inverseNormKernel (t - a) * inverseNormKernel (t - b)) (Metric.ball 0 R) := by
  have hi (c : ℂ) : IntegrableOn (fun t : ℂ => ‖t - c‖⁻¹)
      (Metric.ball (0 : ℂ) R) (volume : Measure ℂ) := by
    change Integrable (fun t : ℂ => ‖t - c‖⁻¹)
      ((volume : Measure ℂ).restrict (Metric.ball (0 : ℂ) R))
    convert! (LiZhongQC.integrableOn_cauchy_kernel_ball hR c).norm using 1
    funext t
    rw [one_div, norm_inv]
  refine ((hi a).add (hi b) |>.div_const ‖a - b‖).mono' ?_ ?_
  · exact ((measurable_inverseNormKernel.comp (measurable_id.sub_const a)).mul
      (measurable_inverseNormKernel.comp (measurable_id.sub_const b))).aestronglyMeasurable.restrict
  · exact Eventually.of_forall (inverseNormKernel_mul_norm_le hab)

/-- The integrand of the renormalized convolution, retaining the original
complex integration variable. -/
def renormalizedInverseNormConvolutionIntegrand (z w t : ℂ) : ℂ :=
  renormalizedInverseNormKernel t w * inverseNormKernel (z - t)

/-- The renormalized convolution on the actual complex plane. Its
integrability away from its two evaluation poles is proved separately. -/
def renormalizedInverseNormConvolution (w z : ℂ) : ℂ :=
  ∫ t : ℂ, renormalizedInverseNormConvolutionIntegrand z w t

theorem measurable_renormalizedInverseNormConvolutionIntegrand (z w : ℂ) :
    Measurable (renormalizedInverseNormConvolutionIntegrand z w) := by
  exact ((measurable_inverseNormKernel.comp (measurable_id.sub_const w)).sub
    measurable_inverseNormKernel).mul
    (measurable_inverseNormKernel.comp (measurable_const.sub measurable_id))

/-- The three possible finite poles are integrable when the evaluation
point is distinct from the two poles of the renormalized kernel. -/
theorem integrableOn_renormalizedInverseNormConvolutionIntegrand_ball
    {R : ℝ} (hR : 0 < R) {z w : ℂ} (hz0 : z ≠ 0) (hzw : z ≠ w) :
    IntegrableOn (renormalizedInverseNormConvolutionIntegrand z w)
      (Metric.ball 0 R) := by
  have h := (integrableOn_inverseNormKernel_mul_ball hR hzw.symm).sub
    (integrableOn_inverseNormKernel_mul_ball hR hz0.symm)
  convert h using 1
  funext t
  simp only [renormalizedInverseNormConvolutionIntegrand,
    renormalizedInverseNormKernel, Pi.sub_apply, sub_zero, sub_mul]
  rw [show inverseNormKernel (z - t) = inverseNormKernel (t - z) by
    simp only [inverseNormKernel, norm_sub_rev]]

/-- The cancellation in the difference kernel is controlled by the
distance between its two poles. -/
theorem norm_renormalizedInverseNormKernel_le {t w : ℂ}
    (ht : t ≠ 0) (htw : t ≠ w) :
    ‖renormalizedInverseNormKernel t w‖ ≤
      ‖w‖ / (‖t - w‖ * ‖t‖) := by
  have ha : 0 < ‖t - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr htw)
  have hb : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hdiff : |‖t‖ - ‖t - w‖| ≤ ‖w‖ := by
    simpa only [sub_sub_cancel] using abs_norm_sub_norm_le t (t - w)
  calc
    ‖renormalizedInverseNormKernel t w‖ =
        |‖t‖ - ‖t - w‖| / (‖t - w‖ * ‖t‖) := by
      simp only [renormalizedInverseNormKernel, inverseNormKernel,
        ← Complex.ofReal_inv, ← Complex.ofReal_sub, Complex.norm_real]
      rw [inv_sub_inv ha.ne' hb.ne', Real.norm_eq_abs, abs_div, abs_mul,
        abs_of_pos ha, abs_of_pos hb]
    _ ≤ ‖w‖ / (‖t - w‖ * ‖t‖) :=
      div_le_div_of_nonneg_right hdiff (by positivity)

private theorem inverseProduct_le_cubic {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 ≤ d)
    (hba : b ≤ 2 * a) (hbc : b ≤ 2 * c) :
    d / (a * b) * c⁻¹ ≤ 4 * d / b ^ 3 := by
  have hprod : b * b ≤ (2 * a) * (2 * c) :=
    mul_le_mul hba hbc hb.le (by positivity)
  have hcube : b ^ 3 ≤ 4 * (a * b * c) := by
    nlinarith [mul_le_mul_of_nonneg_right hprod hb.le]
  calc
    d / (a * b) * c⁻¹ = d / (a * b * c) := by
      field_simp [ha.ne', hb.ne', hc.ne']
    _ ≤ 4 * d / b ^ 3 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hcube)]

/-- The integrable cubic decay of the complete difference-kernel
integrand. -/
theorem norm_renormalizedInverseNormConvolutionIntegrand_le {z w t : ℂ}
    (ht : 0 < ‖t‖) (hw : 2 * ‖w‖ < ‖t‖) (hz : 2 * ‖z‖ < ‖t‖) :
    ‖renormalizedInverseNormConvolutionIntegrand z w t‖ ≤
      4 * ‖w‖ / ‖t‖ ^ 3 := by
  have htw : 0 < ‖t - w‖ := by
    have := norm_sub_norm_le t w
    linarith
  have hzt : 0 < ‖z - t‖ := by
    have := norm_sub_norm_le t z
    rw [norm_sub_rev t z] at this
    linarith
  have hba : ‖t‖ ≤ 2 * ‖t - w‖ := by
    have := norm_sub_norm_le t w
    linarith
  have hbc : ‖t‖ ≤ 2 * ‖z - t‖ := by
    have := norm_sub_norm_le t z
    rw [norm_sub_rev t z] at this
    linarith
  have hcancel := norm_renormalizedInverseNormKernel_le
    (norm_pos_iff.mp ht) (sub_ne_zero.mp (norm_pos_iff.mp htw))
  calc
    ‖renormalizedInverseNormConvolutionIntegrand z w t‖ =
        ‖renormalizedInverseNormKernel t w‖ * ‖z - t‖⁻¹ := by
      rw [renormalizedInverseNormConvolutionIntegrand, norm_mul, norm_inverseNormKernel]
    _ ≤ (‖w‖ / (‖t - w‖ * ‖t‖)) * ‖z - t‖⁻¹ :=
      mul_le_mul_of_nonneg_right hcancel (by positivity)
    _ ≤ 4 * ‖w‖ / ‖t‖ ^ 3 :=
      inverseProduct_le_cubic htw ht hzt (norm_nonneg w) hba hbc

/-- The cubic radial majorant is integrable outside a positive disc. -/
theorem integrableOn_inv_norm_cubic {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun t : ℂ => (‖t‖ ^ 3)⁻¹) {t : ℂ | R < ‖t‖} := by
  refine ⟨(measurable_norm.pow_const 3).inv.aestronglyMeasurable.restrict, ?_⟩
  have hae : (fun t : ℂ => ‖(‖t‖ ^ 3)⁻¹‖ₑ) =ᵐ[
      volume.restrict {t : ℂ | R < ‖t‖}] fun t : ℂ => ‖t‖ₑ ^ (-(3 : ℝ)) := by
    filter_upwards [self_mem_ae_restrict
      ((isOpen_lt continuous_const continuous_norm).measurableSet)] with t ht
    have htpos : 0 < ‖t‖ := lt_trans hR ht
    rw [Real.enorm_of_nonneg (by positivity), ENNReal.rpow_neg,
      ← ofReal_norm t, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (norm_nonneg t),
      ENNReal.ofReal_inv_of_pos (by positivity)]
  rw [hasFiniteIntegral_iff_enorm, lintegral_congr_ae hae,
    LiZhongQC.lintegral_compl_ball_enorm_rpow_neg (by norm_num : (2 : ℝ) < 3) hR]
  finiteness

/-- The renormalized convolution is a genuine absolutely integrable
integral at every point distinct from its two evaluation poles. -/
theorem integrable_renormalizedInverseNormConvolutionIntegrand {z w : ℂ}
    (hz0 : z ≠ 0) (hzw : z ≠ w) :
    Integrable (renormalizedInverseNormConvolutionIntegrand z w) volume := by
  let R : ℝ := 4 * (‖z‖ + ‖w‖ + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hnear := integrableOn_renormalizedInverseNormConvolutionIntegrand_ball hR hz0 hzw
  have hfar : IntegrableOn (renormalizedInverseNormConvolutionIntegrand z w)
      {t : ℂ | R / 2 < ‖t‖} := by
    have hR' : 0 < R / 2 := by positivity
    have hmajor := (integrableOn_inv_norm_cubic hR').const_mul (4 * ‖w‖)
    refine hmajor.mono'
      (measurable_renormalizedInverseNormConvolutionIntegrand z w).aestronglyMeasurable.restrict ?_
    filter_upwards [self_mem_ae_restrict
      ((isOpen_lt continuous_const continuous_norm).measurableSet)] with t ht
    have ht0 : 0 < ‖t‖ := lt_trans hR' ht
    have hw : 2 * ‖w‖ < ‖t‖ := by
      dsimp [R] at ht
      linarith [norm_nonneg z]
    have hz : 2 * ‖z‖ < ‖t‖ := by
      dsimp [R] at ht
      linarith [norm_nonneg w]
    simpa only [div_eq_mul_inv] using
      norm_renormalizedInverseNormConvolutionIntegrand_le ht0 hw hz
  have hcover : Metric.ball (0 : ℂ) R ∪ {t : ℂ | R / 2 < ‖t‖} = univ := by
    apply Set.eq_univ_of_forall
    intro t
    by_cases ht : ‖t‖ < R
    · exact Or.inl (by simpa only [Metric.mem_ball, dist_zero_right] using ht)
    · apply Or.inr
      change R / 2 < ‖t‖
      have ht' : R ≤ ‖t‖ := le_of_not_gt ht
      linarith
  simpa only [hcover, integrableOn_univ] using hnear.union hfar

end LowDimensionalTopology.Geometry.Quasiconformal
