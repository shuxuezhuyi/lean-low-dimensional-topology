module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertKernelDecomposition
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertKernel
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Differentiating the concrete convolution error integrals

The change-of-center terms and the far tail have no evaluation pole on
their integration regions when the radius is large. Their actual real
derivatives can therefore be passed under the integral using integrable
cubic bounds.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem norm_fderiv_inverseNormKernel_le {v : ℂ} (hv : v ≠ 0) :
    ‖fderiv ℝ inverseNormKernel v‖ ≤ (‖v‖ ^ 2)⁻¹ := by
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  calc
    ‖fderiv ℝ inverseNormKernel v‖ = (‖v‖ ^ 3)⁻¹ * ‖v‖ := by
      rw [(hasFDerivAt_inverseNormKernel hv).fderiv]
      change ‖Complex.ofRealLI.toContinuousLinearMap.comp
        ((-(‖v‖ ^ 3)⁻¹) • innerSL ℝ v)‖ = _
      rw [Complex.ofRealLI.norm_toContinuousLinearMap_comp, norm_smul, innerSL_apply_norm]
      simp only [Real.norm_eq_abs, abs_neg, abs_inv, abs_pow,
        abs_of_nonneg (norm_nonneg v)]
    _ = (‖v‖ ^ 2)⁻¹ := by
      field_simp [hvp.ne']
    _ ≤ (‖v‖ ^ 2)⁻¹ := le_rfl

/-- The actual derivative integrand of the reference-pole product. -/
def inverseNormReferenceDerivativeIntegrand (z t : ℂ) : ℂ →L[ℝ] ℂ :=
  inverseNormKernel t • fderiv ℝ inverseNormKernel (z - t)

/-- The actual derivative integrand of the translated far tail. -/
def inverseNormTailDerivativeIntegrand (w z u : ℂ) : ℂ →L[ℝ] ℂ :=
  renormalizedInverseNormKernel (u + w) w •
    fderiv ℝ inverseNormKernel (z - (u + w))

private theorem norm_point_mem_ball_le {z z₀ : ℂ} (hz : z ∈ Metric.ball z₀ 1) :
    ‖z‖ < ‖z₀‖ + 1 := by
  have hd : ‖z - z₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have htri : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z - z₀) z₀
  linarith

private theorem norm_inverseNormReferenceDerivativeIntegrand_le {z t : ℂ}
    (ht : 0 < ‖t‖) (hz : 2 * ‖z‖ < ‖t‖) :
    ‖inverseNormReferenceDerivativeIntegrand z t‖ ≤ 4 * (‖t‖ ^ 3)⁻¹ := by
  have htri : ‖t‖ - ‖z‖ ≤ ‖z - t‖ := by
    simpa only [norm_sub_rev t z] using norm_sub_norm_le t z
  have hc : 0 < ‖z - t‖ := by linarith
  have hbc : ‖t‖ ≤ 2 * ‖z - t‖ := by linarith
  have hsq : ‖t‖ ^ 2 ≤ 4 * ‖z - t‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbc)
      (by positivity : 0 ≤ 2 * ‖z - t‖ + ‖t‖)]
  calc
    ‖inverseNormReferenceDerivativeIntegrand z t‖ =
        ‖t‖⁻¹ * ‖fderiv ℝ inverseNormKernel (z - t)‖ := by
      rw [inverseNormReferenceDerivativeIntegrand, norm_smul, norm_inverseNormKernel]
    _ ≤ ‖t‖⁻¹ * (‖z - t‖ ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (norm_fderiv_inverseNormKernel_le (norm_pos_iff.mp hc)) (by positivity)
    _ = 1 / (‖t‖ * ‖z - t‖ ^ 2) := by rw [one_div, mul_inv]
    _ ≤ 4 / ‖t‖ ^ 3 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hsq ht.le]
    _ = 4 * (‖t‖ ^ 3)⁻¹ := div_eq_mul_inv _ _

private theorem hasFDerivAt_inverseNormReferenceIntegrand {z t : ℂ}
    (hzt : z - t ≠ 0) :
    HasFDerivAt (fun v : ℂ => inverseNormKernel t * inverseNormKernel (v - t))
      (inverseNormReferenceDerivativeIntegrand z t) z := by
  have hk := (hasFDerivAt_inverseNormKernel hzt).differentiableAt.hasFDerivAt
  have hc : HasFDerivAt (fun v : ℂ => inverseNormKernel (v - t))
      (fderiv ℝ inverseNormKernel (z - t)) z := by
    convert! hk.comp z ((hasFDerivAt_id z).sub_const t) using 1
  unfold inverseNormReferenceDerivativeIntegrand
  convert! hc.const_smul (inverseNormKernel t) using 1

private theorem measurable_inverseNormReferenceDerivativeIntegrand (z : ℂ) :
    Measurable (inverseNormReferenceDerivativeIntegrand z) :=
  measurable_inverseNormKernel.smul
    ((measurable_fderiv ℝ inverseNormKernel).comp (measurable_const.sub measurable_id))

private theorem hasFDerivAt_reference_integral_on_exterior_subset
    {S : Set ℂ} (hS : MeasurableSet S) {R : ℝ} {z₀ : ℂ}
    (hR : 4 * (‖z₀‖ + 1) < R)
    (hsub : S ⊆ {t : ℂ | R / 2 < ‖t‖})
    (hint : IntegrableOn
      (fun t : ℂ => inverseNormKernel t * inverseNormKernel (z₀ - t)) S) :
    HasFDerivAt
      (fun z : ℂ => ∫ t in S, inverseNormKernel t * inverseNormKernel (z - t))
      (∫ t in S, inverseNormReferenceDerivativeIntegrand z₀ t) z₀ := by
  have hR0 : 0 < R := by linarith [norm_nonneg z₀]
  have hmajor : IntegrableOn (fun t : ℂ => 4 * (‖t‖ ^ 3)⁻¹) S
      (volume : Measure ℂ) :=
    IntegrableOn.mono_set
      ((integrableOn_inv_norm_cubic (by positivity : 0 < R / 2)).const_mul 4) hsub
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z t : ℂ => inverseNormKernel t * inverseNormKernel (z - t))
    (F' := fun z t : ℂ => inverseNormReferenceDerivativeIntegrand z t)
    (μ := volume.restrict S) (bound := fun t : ℂ => 4 * (‖t‖ ^ 3)⁻¹)
    (s := Metric.ball z₀ 1) (Metric.ball_mem_nhds z₀ one_pos) ?_ hint ?_ ?_ hmajor ?_
  · apply Eventually.of_forall
    intro z
    have hm : Measurable (fun t : ℂ =>
        inverseNormKernel t * inverseNormKernel (z - t)) :=
      measurable_inverseNormKernel.mul
        (measurable_inverseNormKernel.comp (measurable_const.sub measurable_id))
    exact hm.aestronglyMeasurable.restrict
  · exact (measurable_inverseNormReferenceDerivativeIntegrand z₀).aestronglyMeasurable.restrict
  · filter_upwards [self_mem_ae_restrict hS] with t ht
    intro z hz
    have hlow : R / 2 < ‖t‖ := hsub ht
    have hzM := norm_point_mem_ball_le hz
    exact norm_inverseNormReferenceDerivativeIntegrand_le (by linarith)
      (by linarith)
  · filter_upwards [self_mem_ae_restrict hS] with t ht
    intro z hz
    have hlow : R / 2 < ‖t‖ := hsub ht
    have hzM := norm_point_mem_ball_le hz
    have htri : ‖t‖ - ‖z‖ ≤ ‖z - t‖ := by
      simpa only [norm_sub_rev t z] using norm_sub_norm_le t z
    exact hasFDerivAt_inverseNormReferenceIntegrand
      (norm_pos_iff.mp (by linarith : 0 < ‖z - t‖))

private theorem recentering_domains_exterior {R : ℝ} {w : ℂ}
    (hR : 0 < R) (hw : 2 * ‖w‖ < R) :
    (Metric.ball w R \ Metric.ball (0 : ℂ) R ⊆ {t : ℂ | R / 2 < ‖t‖}) ∧
    (Metric.ball (0 : ℂ) R \ Metric.ball w R ⊆ {t : ℂ | R / 2 < ‖t‖}) := by
  constructor
  · intro t ht
    change R / 2 < ‖t‖
    have hn : R ≤ ‖t‖ := by
      simpa only [Metric.mem_ball, dist_zero_right, not_lt] using ht.2
    linarith
  · intro t ht
    change R / 2 < ‖t‖
    have hn : R ≤ ‖t - w‖ := by
      simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using ht.2
    have htri := norm_sub_le t w
    linarith

/-- The actual change-of-center correction is differentiable, with its
derivative expressed by the two ordinary set-difference integrals. -/
theorem hasFDerivAt_inverseNormRecenteringError {R : ℝ} {w z₀ : ℂ}
    (hz₀ : z₀ ≠ 0) (hR : 4 * (‖z₀‖ + ‖w‖ + 1) < R) :
    HasFDerivAt (inverseNormRecenteringError R w)
      ((∫ t in Metric.ball w R \ Metric.ball (0 : ℂ) R,
          inverseNormReferenceDerivativeIntegrand z₀ t) -
        ∫ t in Metric.ball (0 : ℂ) R \ Metric.ball w R,
          inverseNormReferenceDerivativeIntegrand z₀ t) z₀ := by
  have hR0 : 0 < R := by linarith [norm_nonneg z₀, norm_nonneg w]
  have hw : 2 * ‖w‖ < R := by linarith [norm_nonneg z₀, norm_nonneg w]
  have hr : 4 * (‖z₀‖ + 1) < R := by linarith [norm_nonneg w]
  have hsub := recentering_domains_exterior hR0 hw
  have h₁ := hasFDerivAt_reference_integral_on_exterior_subset
    (measurableSet_ball.diff measurableSet_ball) hr hsub.1
    ((integrableOn_inverseNormReference_shiftedBall hR0 hz₀ w).mono_set sdiff_subset)
  have h₂ := hasFDerivAt_reference_integral_on_exterior_subset
    (measurableSet_ball.diff measurableSet_ball) hr hsub.2
    ((integrableOn_inverseNormDiscPotential hR0 hz₀).mono_set sdiff_subset)
  exact h₁.sub h₂

/-- Translation retains the actual tail integral and its original pole. -/
theorem renormalizedInverseNormConvolutionTail_eq_translated (R : ℝ) (w z : ℂ) :
    renormalizedInverseNormConvolutionTail R w z =
      ∫ u in (Metric.ball (0 : ℂ) R)ᶜ,
        renormalizedInverseNormConvolutionIntegrand z w (u + w) := by
  have hemb : MeasurableEmbedding (fun u : ℂ => u + w) :=
    (Homeomorph.addRight w).isClosedEmbedding.measurableEmbedding
  have hpre : (fun u : ℂ => u + w) ⁻¹' (Metric.ball w R)ᶜ =
      (Metric.ball (0 : ℂ) R)ᶜ := by
    ext u
    simp only [mem_preimage, mem_compl_iff, Metric.mem_ball, dist_eq_norm,
      add_sub_cancel_right, sub_zero]
  have h := (measurePreserving_add_right volume w).setIntegral_preimage_emb hemb
    (renormalizedInverseNormConvolutionIntegrand z w) (Metric.ball w R)ᶜ
  rw [hpre] at h
  exact h.symm

private theorem inverseProduct_le_tailCubic {a b c d R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 ≤ d) (hR : 0 < R)
    (hRb : R ≤ b) (hba : b ≤ 2 * a) (hbc : b ≤ 2 * c) :
    d / (b * a) * (c ^ 2)⁻¹ ≤ (8 * d / R) * (b ^ 3)⁻¹ := by
  have hsq : b ^ 2 ≤ 4 * c ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbc) (by positivity : 0 ≤ 2 * c + b)]
  have hprod : b * b ^ 2 ≤ (2 * a) * (4 * c ^ 2) :=
    mul_le_mul hba hsq (sq_nonneg b) (by positivity)
  have hden : R * b ^ 3 ≤ 8 * (b * a * c ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hprod hb.le,
      mul_le_mul_of_nonneg_right hRb (pow_nonneg hb.le 3)]
  calc
    d / (b * a) * (c ^ 2)⁻¹ = d / (b * a * c ^ 2) := by
      field_simp [ha.ne', hb.ne', hc.ne']
    _ ≤ (8 * d) / (R * b ^ 3) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hden)]
    _ = (8 * d / R) * (b ^ 3)⁻¹ := by
      field_simp [hR.ne', hb.ne']

private theorem norm_inverseNormTailDerivativeIntegrand_le {w z u : ℂ} {R : ℝ}
    (hR : 0 < R) (hRu : R ≤ ‖u‖) (hw : 2 * ‖w‖ < ‖u‖)
    (hz : 2 * ‖z - w‖ < ‖u‖) :
    ‖inverseNormTailDerivativeIntegrand w z u‖ ≤
      (8 * ‖w‖ / R) * (‖u‖ ^ 3)⁻¹ := by
  have hup : 0 < ‖u‖ := lt_of_lt_of_le hR hRu
  have hta : ‖u‖ - ‖w‖ ≤ ‖u + w‖ := by
    simpa only [norm_neg, sub_neg_eq_add] using norm_sub_norm_le u (-w)
  have htc : ‖u‖ - ‖z - w‖ ≤ ‖z - (u + w)‖ := by
    have h := norm_sub_norm_le u (z - w)
    rw [norm_sub_rev u (z - w), show z - w - u = z - (u + w) by ring] at h
    exact h
  have ha : 0 < ‖u + w‖ := by linarith
  have hc : 0 < ‖z - (u + w)‖ := by linarith
  have hba : ‖u‖ ≤ 2 * ‖u + w‖ := by linarith
  have hbc : ‖u‖ ≤ 2 * ‖z - (u + w)‖ := by linarith
  have htw : u + w ≠ w := by
    intro h
    have hu : u = 0 := add_right_cancel (by simpa only [zero_add] using h)
    exact (norm_pos_iff.mp hup) hu
  have hcancel := norm_renormalizedInverseNormKernel_le (norm_pos_iff.mp ha) htw
  simp only [add_sub_cancel_right] at hcancel
  calc
    ‖inverseNormTailDerivativeIntegrand w z u‖ =
        ‖renormalizedInverseNormKernel (u + w) w‖ *
          ‖fderiv ℝ inverseNormKernel (z - (u + w))‖ := by
      rw [inverseNormTailDerivativeIntegrand, norm_smul]
    _ ≤ (‖w‖ / (‖u‖ * ‖u + w‖)) * (‖z - (u + w)‖ ^ 2)⁻¹ :=
      mul_le_mul hcancel
        (norm_fderiv_inverseNormKernel_le (norm_pos_iff.mp hc))
        (norm_nonneg _) (by positivity)
    _ ≤ (8 * ‖w‖ / R) * (‖u‖ ^ 3)⁻¹ :=
      inverseProduct_le_tailCubic ha hup hc (norm_nonneg w) hR hRu hba hbc

private theorem hasFDerivAt_inverseNormTailIntegrand {w z u : ℂ}
    (hzu : z - (u + w) ≠ 0) :
    HasFDerivAt
      (fun v : ℂ => renormalizedInverseNormConvolutionIntegrand v w (u + w))
      (inverseNormTailDerivativeIntegrand w z u) z := by
  have hk := (hasFDerivAt_inverseNormKernel hzu).differentiableAt.hasFDerivAt
  have hc : HasFDerivAt (fun v : ℂ => inverseNormKernel (v - (u + w)))
      (fderiv ℝ inverseNormKernel (z - (u + w))) z := by
    convert! hk.comp z ((hasFDerivAt_id z).sub_const (u + w)) using 1
  unfold inverseNormTailDerivativeIntegrand renormalizedInverseNormConvolutionIntegrand
  convert! hc.const_smul (renormalizedInverseNormKernel (u + w) w) using 1

private theorem measurable_inverseNormTailDerivativeIntegrand (w z : ℂ) :
    Measurable (inverseNormTailDerivativeIntegrand w z) := by
  exact (((measurable_inverseNormKernel.comp
      ((measurable_id.add_const w).sub_const w)).sub
        (measurable_inverseNormKernel.comp (measurable_id.add_const w))).smul
    ((measurable_fderiv ℝ inverseNormKernel).comp
      (measurable_const.sub (measurable_id.add_const w))))

/-- The actual far tail is differentiable on a neighborhood whose size is
independent of the integration variable. -/
theorem hasFDerivAt_renormalizedInverseNormConvolutionTail {R : ℝ} {w z₀ : ℂ}
    (hz₀ : z₀ ≠ 0) (hz₀w : z₀ ≠ w)
    (hR : 4 * (‖z₀‖ + ‖w‖ + 1) < R) :
    HasFDerivAt (renormalizedInverseNormConvolutionTail R w)
      (∫ u in (Metric.ball (0 : ℂ) R)ᶜ,
        inverseNormTailDerivativeIntegrand w z₀ u) z₀ := by
  have hR0 : 0 < R := by linarith [norm_nonneg z₀, norm_nonneg w]
  have hsub : (Metric.ball (0 : ℂ) R)ᶜ ⊆ {u : ℂ | R / 2 < ‖u‖} := by
    intro u hu
    change R / 2 < ‖u‖
    have hn : R ≤ ‖u‖ := by
      simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hu
    linarith
  have hmajor : IntegrableOn
      (fun u : ℂ => (8 * ‖w‖ / R) * (‖u‖ ^ 3)⁻¹)
      (Metric.ball (0 : ℂ) R)ᶜ (volume : Measure ℂ) :=
    IntegrableOn.mono_set
      ((integrableOn_inv_norm_cubic (by positivity : 0 < R / 2)).const_mul
        (8 * ‖w‖ / R)) hsub
  have hemb : MeasurableEmbedding (fun u : ℂ => u + w) :=
    (Homeomorph.addRight w).isClosedEmbedding.measurableEmbedding
  have hpre : (fun u : ℂ => u + w) ⁻¹' (Metric.ball w R)ᶜ =
      (Metric.ball (0 : ℂ) R)ᶜ := by
    ext u
    simp only [mem_preimage, mem_compl_iff, Metric.mem_ball, dist_eq_norm,
      add_sub_cancel_right, sub_zero]
  have hint : IntegrableOn
      (fun u : ℂ => renormalizedInverseNormConvolutionIntegrand z₀ w (u + w))
      (Metric.ball (0 : ℂ) R)ᶜ := by
    have h := ((measurePreserving_add_right volume w).integrableOn_comp_preimage hemb).mpr
      ((integrable_renormalizedInverseNormConvolutionIntegrand hz₀ hz₀w).integrableOn
        (s := (Metric.ball w R)ᶜ))
    simpa only [Function.comp_def, hpre] using h
  have hd : HasFDerivAt
      (fun z : ℂ => ∫ u in (Metric.ball (0 : ℂ) R)ᶜ,
        renormalizedInverseNormConvolutionIntegrand z w (u + w))
      (∫ u in (Metric.ball (0 : ℂ) R)ᶜ,
        inverseNormTailDerivativeIntegrand w z₀ u) z₀ := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun z u : ℂ => renormalizedInverseNormConvolutionIntegrand z w (u + w))
      (F' := fun z u : ℂ => inverseNormTailDerivativeIntegrand w z u)
      (μ := volume.restrict (Metric.ball (0 : ℂ) R)ᶜ)
      (bound := fun u : ℂ => (8 * ‖w‖ / R) * (‖u‖ ^ 3)⁻¹)
      (s := Metric.ball z₀ 1) (Metric.ball_mem_nhds z₀ one_pos) ?_ hint ?_ ?_ hmajor ?_
    · exact Eventually.of_forall fun z =>
        ((measurable_renormalizedInverseNormConvolutionIntegrand z w).comp
          (measurable_id.add_const w)).aestronglyMeasurable.restrict
    · exact (measurable_inverseNormTailDerivativeIntegrand w z₀).aestronglyMeasurable.restrict
    · filter_upwards [self_mem_ae_restrict measurableSet_ball.compl] with u hu
      intro z hz
      have hn : R ≤ ‖u‖ := by
        simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hu
      have hzM := norm_point_mem_ball_le hz
      have htri := norm_sub_le z w
      exact norm_inverseNormTailDerivativeIntegrand_le hR0 hn
        (by linarith [norm_nonneg z₀, norm_nonneg w]) (by linarith)
    · filter_upwards [self_mem_ae_restrict measurableSet_ball.compl] with u hu
      intro z hz
      have hn : R ≤ ‖u‖ := by
        simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hu
      have hzM := norm_point_mem_ball_le hz
      have hzw := norm_sub_le z w
      have htri : ‖u‖ - ‖z - w‖ ≤ ‖z - (u + w)‖ := by
        have h := norm_sub_norm_le u (z - w)
        rw [norm_sub_rev u (z - w), show z - w - u = z - (u + w) by ring] at h
        exact h
      exact hasFDerivAt_inverseNormTailIntegrand
        (norm_pos_iff.mp (by linarith : 0 < ‖z - (u + w)‖))
  apply hd.congr_of_eventuallyEq
  exact Eventually.of_forall (renormalizedInverseNormConvolutionTail_eq_translated R w)

private theorem integral_inv_norm_cubic {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ t in {t : ℂ | ρ < ‖t‖}, (‖t‖ ^ 3)⁻¹) = 2 * Real.pi / ρ := by
  have heq : (fun t : ℂ => ENNReal.ofReal ((‖t‖ ^ 3)⁻¹)) =ᵐ[
      volume.restrict {t : ℂ | ρ < ‖t‖}]
        fun t : ℂ => ‖t‖ₑ ^ (-(3 : ℝ)) := by
    filter_upwards [self_mem_ae_restrict
      ((isOpen_lt continuous_const continuous_norm).measurableSet)] with t ht
    have htpos : 0 < ‖t‖ := lt_trans hρ ht
    rw [ENNReal.rpow_neg, ← ofReal_norm t,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (norm_nonneg t),
      ENNReal.ofReal_inv_of_pos (by positivity)]
  have hv := ofReal_integral_eq_lintegral_ofReal (integrableOn_inv_norm_cubic hρ)
    (Eventually.of_forall fun t : ℂ => by positivity)
  rw [lintegral_congr_ae heq,
    LiZhongQC.lintegral_compl_ball_enorm_rpow_neg (by norm_num : (2 : ℝ) < 3) hρ] at hv
  norm_num [Real.rpow_neg_one] at hv
  have hn : 0 ≤ ∫ t in {t : ℂ | ρ < ‖t‖}, (‖t‖ ^ 3)⁻¹ :=
    integral_nonneg (fun t => by positivity)
  have h := congrArg ENNReal.toReal hv
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hn,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal Real.pi_pos.le,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hρ.le), div_eq_mul_inv] using h

private theorem norm_integral_referenceDerivative_le
    {S : Set ℂ} (hS : MeasurableSet S) {R : ℝ} {z₀ : ℂ}
    (hR : 4 * (‖z₀‖ + 1) < R)
    (hsub : S ⊆ {t : ℂ | R / 2 < ‖t‖}) :
    ‖∫ t in S, inverseNormReferenceDerivativeIntegrand z₀ t‖ ≤ 16 * Real.pi / R := by
  have hR0 : 0 < R := by linarith [norm_nonneg z₀]
  have hmajor : IntegrableOn (fun t : ℂ => 4 * (‖t‖ ^ 3)⁻¹)
      {t : ℂ | R / 2 < ‖t‖} (volume : Measure ℂ) :=
    (integrableOn_inv_norm_cubic (by positivity : 0 < R / 2)).const_mul 4
  have hbound : ∀ᵐ t ∂volume.restrict S,
      ‖inverseNormReferenceDerivativeIntegrand z₀ t‖ ≤ 4 * (‖t‖ ^ 3)⁻¹ := by
    filter_upwards [self_mem_ae_restrict hS] with t ht
    have hlow : R / 2 < ‖t‖ := hsub ht
    exact norm_inverseNormReferenceDerivativeIntegrand_le (by linarith)
      (by linarith)
  calc
    ‖∫ t in S, inverseNormReferenceDerivativeIntegrand z₀ t‖ ≤
        ∫ t in S, 4 * (‖t‖ ^ 3)⁻¹ :=
      norm_integral_le_of_norm_le (IntegrableOn.mono_set hmajor hsub) hbound
    _ ≤ ∫ t in {t : ℂ | R / 2 < ‖t‖}, 4 * (‖t‖ ^ 3)⁻¹ :=
      setIntegral_mono_set hmajor (Eventually.of_forall fun t => by positivity)
        (Eventually.of_forall hsub)
    _ = 16 * Real.pi / R := by
      rw [integral_const_mul, integral_inv_norm_cubic (by positivity : 0 < R / 2)]
      field_simp [hR0.ne']
      ring

/-- The full real derivative of the change-of-center correction tends to
zero with an explicit exterior-integral bound. -/
theorem norm_fderiv_inverseNormRecenteringError_le {R : ℝ} {w z₀ : ℂ}
    (hz₀ : z₀ ≠ 0) (hR : 4 * (‖z₀‖ + ‖w‖ + 1) < R) :
    ‖fderiv ℝ (inverseNormRecenteringError R w) z₀‖ ≤ 32 * Real.pi / R := by
  have hR0 : 0 < R := by linarith [norm_nonneg z₀, norm_nonneg w]
  have hw : 2 * ‖w‖ < R := by linarith [norm_nonneg z₀, norm_nonneg w]
  have hr : 4 * (‖z₀‖ + 1) < R := by linarith [norm_nonneg w]
  have hsub := recentering_domains_exterior hR0 hw
  rw [(hasFDerivAt_inverseNormRecenteringError hz₀ hR).fderiv]
  calc
    ‖(∫ t in Metric.ball w R \ Metric.ball (0 : ℂ) R,
          inverseNormReferenceDerivativeIntegrand z₀ t) -
        ∫ t in Metric.ball (0 : ℂ) R \ Metric.ball w R,
          inverseNormReferenceDerivativeIntegrand z₀ t‖ ≤
        ‖∫ t in Metric.ball w R \ Metric.ball (0 : ℂ) R,
          inverseNormReferenceDerivativeIntegrand z₀ t‖ +
        ‖∫ t in Metric.ball (0 : ℂ) R \ Metric.ball w R,
          inverseNormReferenceDerivativeIntegrand z₀ t‖ := norm_sub_le _ _
    _ ≤ 16 * Real.pi / R + 16 * Real.pi / R :=
      add_le_add
        (norm_integral_referenceDerivative_le
          (measurableSet_ball.diff measurableSet_ball) hr hsub.1)
        (norm_integral_referenceDerivative_le
          (measurableSet_ball.diff measurableSet_ball) hr hsub.2)
    _ = 32 * Real.pi / R := by ring

/-- The derivative of the actual far tail has a vanishing bound uniform
on each fixed bounded neighborhood of the evaluation point. -/
theorem norm_fderiv_renormalizedInverseNormConvolutionTail_le {R : ℝ} {w z₀ : ℂ}
    (hz₀ : z₀ ≠ 0) (hz₀w : z₀ ≠ w)
    (hR : 4 * (‖z₀‖ + ‖w‖ + 1) < R) :
    ‖fderiv ℝ (renormalizedInverseNormConvolutionTail R w) z₀‖ ≤
      32 * Real.pi * ‖w‖ / R ^ 2 := by
  have hR0 : 0 < R := by linarith [norm_nonneg z₀, norm_nonneg w]
  have hsub : (Metric.ball (0 : ℂ) R)ᶜ ⊆ {u : ℂ | R / 2 < ‖u‖} := by
    intro u hu
    change R / 2 < ‖u‖
    have hn : R ≤ ‖u‖ := by
      simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hu
    linarith
  have hmajor : IntegrableOn (fun u : ℂ => (8 * ‖w‖ / R) * (‖u‖ ^ 3)⁻¹)
      {u : ℂ | R / 2 < ‖u‖} (volume : Measure ℂ) :=
    (integrableOn_inv_norm_cubic (by positivity : 0 < R / 2)).const_mul (8 * ‖w‖ / R)
  have hbound : ∀ᵐ u ∂volume.restrict (Metric.ball (0 : ℂ) R)ᶜ,
      ‖inverseNormTailDerivativeIntegrand w z₀ u‖ ≤
        (8 * ‖w‖ / R) * (‖u‖ ^ 3)⁻¹ := by
    filter_upwards [self_mem_ae_restrict measurableSet_ball.compl] with u hu
    have hn : R ≤ ‖u‖ := by
      simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hu
    have htri := norm_sub_le z₀ w
    exact norm_inverseNormTailDerivativeIntegrand_le hR0 hn
      (by linarith [norm_nonneg z₀, norm_nonneg w]) (by linarith)
  rw [(hasFDerivAt_renormalizedInverseNormConvolutionTail hz₀ hz₀w hR).fderiv]
  calc
    ‖∫ u in (Metric.ball (0 : ℂ) R)ᶜ,
        inverseNormTailDerivativeIntegrand w z₀ u‖ ≤
      ∫ u in (Metric.ball (0 : ℂ) R)ᶜ,
        (8 * ‖w‖ / R) * (‖u‖ ^ 3)⁻¹ :=
      norm_integral_le_of_norm_le (IntegrableOn.mono_set hmajor hsub) hbound
    _ ≤ ∫ u in {u : ℂ | R / 2 < ‖u‖}, (8 * ‖w‖ / R) * (‖u‖ ^ 3)⁻¹ :=
      setIntegral_mono_set hmajor (Eventually.of_forall fun u => by positivity)
        (Eventually.of_forall hsub)
    _ = 32 * Real.pi * ‖w‖ / R ^ 2 := by
      rw [integral_const_mul, integral_inv_norm_cubic (by positivity : 0 < R / 2)]
      field_simp [hR0.ne']
      ring

private theorem norm_dz_le_fderiv (f : ℂ → ℂ) (z : ℂ) :
    ‖LiZhongQC.dz f z‖ ≤ ‖fderiv ℝ f z‖ := by
  have h₁ := (fderiv ℝ f z).le_opNorm (1 : ℂ)
  have hI := (fderiv ℝ f z).le_opNorm I
  simp only [norm_one, norm_I, mul_one] at h₁ hI
  calc
    ‖LiZhongQC.dz f z‖ =
        ‖fderiv ℝ f z 1 - I * fderiv ℝ f z I‖ / 2 := by
      simp only [LiZhongQC.dz, norm_div, norm_ofNat]
    _ ≤ (‖fderiv ℝ f z 1‖ + ‖fderiv ℝ f z I‖) / 2 := by
      gcongr
      simpa only [norm_mul, norm_I, one_mul] using
        norm_sub_le (fderiv ℝ f z 1) (I * fderiv ℝ f z I)
    _ ≤ ‖fderiv ℝ f z‖ := by linarith

/-- The actual change-of-center Wirtinger derivative tends to zero. -/
theorem tendsto_dz_inverseNormRecenteringError {w z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun R : ℝ => LiZhongQC.dz (inverseNormRecenteringError R w) z)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun R : ℝ => 32 * Real.pi / R) atTop (𝓝 0) := by
    simpa only [id] using
      (tendsto_const_nhds (x := 32 * Real.pi)).div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop (4 * (‖z‖ + ‖w‖ + 1))] with R hR
  exact (norm_dz_le_fderiv _ _).trans (norm_fderiv_inverseNormRecenteringError_le hz hR)

/-- The actual far-tail Wirtinger derivative tends to zero. -/
theorem tendsto_dz_renormalizedInverseNormConvolutionTail {w z : ℂ}
    (hz : z ≠ 0) (hzw : z ≠ w) :
    Tendsto (fun R : ℝ => LiZhongQC.dz (renormalizedInverseNormConvolutionTail R w) z)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun R : ℝ => 32 * Real.pi * ‖w‖ / R ^ 2) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := 32 * Real.pi * ‖w‖)).div_atTop
      (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop (4 * (‖z‖ + ‖w‖ + 1))] with R hR
  exact (norm_dz_le_fderiv _ _).trans
    (norm_fderiv_renormalizedInverseNormConvolutionTail_le hz hzw hR)

end LowDimensionalTopology.Geometry.Quasiconformal
