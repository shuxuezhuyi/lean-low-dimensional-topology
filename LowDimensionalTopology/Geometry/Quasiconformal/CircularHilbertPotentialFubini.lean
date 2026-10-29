module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertKernelConvolution
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Absolute integrability before iterating the inverse-norm potential

For a compact continuous test, the norm convolution is continuous and
controls the bounded part of the double integral. Cancellation in the
renormalized kernel gives an integrable cubic bound at infinity. Fubini
is applied only after combining these two genuine integrability facts.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex Metric

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The actual double integrand for a compact test and the renormalized
inverse-norm kernel is absolutely integrable on the product plane. -/
theorem integrable_compactTest_inverseNormConvolution {ψ : ℂ → ℂ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (w : ℂ) :
    Integrable (fun p : ℂ × ℂ => ψ p.1 *
      renormalizedInverseNormConvolutionIntegrand p.1 w p.2)
      ((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  let H : ℂ × ℂ → ℂ := fun p => ψ p.1 *
    renormalizedInverseNormConvolutionIntegrand p.1 w p.2
  let M : ℂ → ℝ := convolution (fun t : ℂ => ‖inverseNormKernel t‖)
    (fun z : ℂ => ‖ψ z‖) (ContinuousLinearMap.mul ℝ ℝ) volume
  let N : ℂ → ℝ := fun t => ∫ z : ℂ, ‖H (z, t)‖
  have hKnorm : LocallyIntegrable (fun t : ℂ => ‖inverseNormKernel t‖)
      (volume : Measure ℂ) :=
    locallyIntegrableOn_univ.mp
      ((locallyIntegrable_inverseNormKernel.locallyIntegrableOn univ).norm)
  have hMcont : Continuous M :=
    hc.norm.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hKnorm hψ.norm
  have hMformula (t : ℂ) : M t = ∫ z : ℂ, ‖ψ z‖ * ‖inverseNormKernel (z - t)‖ := by
    dsimp only [M]
    rw [convolution_eq_swap]
    apply integral_congr_ae
    filter_upwards with z
    simp only [ContinuousLinearMap.mul_apply', inverseNormKernel, norm_sub_rev]
    exact mul_comm _ _
  have hδmeas : Measurable (fun t : ℂ => renormalizedInverseNormKernel t w) :=
    (measurable_inverseNormKernel.comp (measurable_id.sub_const w)).sub
      measurable_inverseNormKernel
  have hHmeas : Measurable H :=
    (hψ.measurable.comp measurable_fst).mul
      ((hδmeas.comp measurable_snd).mul
        (measurable_inverseNormKernel.comp (measurable_fst.sub measurable_snd)))
  have hsection (t : ℂ) : Integrable (fun z : ℂ => H (z, t)) (volume : Measure ℂ) := by
    have hi := (integrable_inverseNormPotential hψ hc t).const_mul
      (renormalizedInverseNormKernel t w)
    apply hi.congr
    filter_upwards with z
    dsimp [H, renormalizedInverseNormConvolutionIntegrand]
    ring
  have hNformula (t : ℂ) : N t = ‖renormalizedInverseNormKernel t w‖ * M t := by
    dsimp only [N]
    rw [hMformula, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    simp only [H, renormalizedInverseNormConvolutionIntegrand, norm_mul]
    ring
  have hNmeas : AEStronglyMeasurable N (volume : Measure ℂ) := by
    have heq : N = fun t => ‖renormalizedInverseNormKernel t w‖ * M t :=
      funext hNformula
    rw [heq]
    exact (hδmeas.norm.mul hMcont.measurable).aestronglyMeasurable
  obtain ⟨A₀, hA₀⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  let A : ℝ := max A₀ 0 + 1
  let R : ℝ := 4 * (‖w‖ + A + 1)
  have hA : 0 < A := by dsimp [A]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : 0 < R + 1 := by positivity
  have hψbound (z : ℂ) (hz : z ∈ tsupport ψ) : ‖z‖ ≤ A := by
    have h := mem_closedBall_zero_iff.mp (hA₀ hz)
    dsimp [A]
    linarith [le_max_left A₀ 0]
  have hiK (c : ℂ) : IntegrableOn (fun t : ℂ => ‖inverseNormKernel (t - c)‖)
      (closedBall (0 : ℂ) R) (volume : Measure ℂ) := by
    have hi : IntegrableOn (fun t : ℂ => ‖inverseNormKernel (t - c)‖)
        (ball (0 : ℂ) (R + 1)) (volume : Measure ℂ) := by
      simp only [norm_inverseNormKernel]
      change Integrable (fun t : ℂ => ‖t - c‖⁻¹)
        ((volume : Measure ℂ).restrict (ball (0 : ℂ) (R + 1)))
      convert! (LiZhongQC.integrableOn_cauchy_kernel_ball hR1 c).norm using 1
      funext t
      rw [one_div, norm_inv]
    apply hi.mono_set
    intro t ht
    rw [mem_ball_zero_iff]
    have h := mem_closedBall_zero_iff.mp ht
    linarith
  have hi0 := hiK 0
  simp only [sub_zero] at hi0
  have hδnear : IntegrableOn (fun t : ℂ => ‖renormalizedInverseNormKernel t w‖)
      (closedBall (0 : ℂ) R) (volume : Measure ℂ) := by
    refine ((hiK w).add hi0).mono' hδmeas.norm.aestronglyMeasurable.restrict ?_
    apply Eventually.of_forall
    intro t
    simp only [norm_norm, renormalizedInverseNormKernel]
    exact norm_sub_le _ _
  have hnear : IntegrableOn N (closedBall (0 : ℂ) R) (volume : Measure ℂ) := by
    have hi := hδnear.mul_continuousOn hMcont.continuousOn (isCompact_closedBall 0 R)
    apply hi.congr
    exact Eventually.of_forall fun t => (hNformula t).symm
  have hψint : Integrable ψ (volume : Measure ℂ) := hψ.integrable_of_hasCompactSupport hc
  have hNbound (t : ℂ) (ht : R < ‖t‖) :
      N t ≤ ((∫ z : ℂ, ‖ψ z‖) * (4 * ‖w‖)) * (‖t‖ ^ 3)⁻¹ := by
    have ht0 : 0 < ‖t‖ := hR.trans ht
    have hwt : 2 * ‖w‖ < ‖t‖ := by dsimp [R] at ht; linarith [norm_nonneg w]
    have hpoint (z : ℂ) : ‖H (z, t)‖ ≤ ‖ψ z‖ * (4 * ‖w‖ / ‖t‖ ^ 3) := by
      by_cases hz : z ∈ tsupport ψ
      · have hzt : 2 * ‖z‖ < ‖t‖ := by
          have hb := hψbound z hz
          dsimp [R] at ht
          linarith [norm_nonneg w]
        dsimp only [H]
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (norm_renormalizedInverseNormConvolutionIntegrand_le ht0 hwt hzt)
          (norm_nonneg _)
      · dsimp only [H]
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, norm_zero, zero_mul]
    calc
      N t = ∫ z : ℂ, ‖H (z, t)‖ := rfl
      _ ≤ ∫ z : ℂ, ‖ψ z‖ * (4 * ‖w‖ / ‖t‖ ^ 3) :=
        integral_mono (hsection t).norm (hψint.norm.mul_const _)
          hpoint
      _ = (∫ z : ℂ, ‖ψ z‖) * (4 * ‖w‖ / ‖t‖ ^ 3) := integral_mul_const _ _
      _ = _ := by rw [div_eq_mul_inv]; ring
  have hfar : IntegrableOn N {t : ℂ | R < ‖t‖} (volume : Measure ℂ) := by
    have hi := (integrableOn_inv_norm_cubic hR).const_mul
      ((∫ z : ℂ, ‖ψ z‖) * (4 * ‖w‖))
    refine hi.mono' hNmeas.restrict ?_
    filter_upwards [self_mem_ae_restrict
      ((isOpen_lt continuous_const continuous_norm).measurableSet)] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun z => norm_nonneg (H (z, t)))]
    exact hNbound t ht
  have hcover : closedBall (0 : ℂ) R ∪ {t : ℂ | R < ‖t‖} = univ := by
    ext t
    simp only [mem_union, mem_closedBall_zero_iff, mem_ofPred_eq, mem_univ, iff_true]
    exact le_or_gt _ _
  have hNint : Integrable N (volume : Measure ℂ) := by
    simpa only [hcover, integrableOn_univ] using hnear.union hfar
  apply (integrable_prod_iff' hHmeas.aestronglyMeasurable).mpr
  exact ⟨Eventually.of_forall hsection, hNint⟩

/-- Fubini gives the literal renormalized potential of the first potential,
with both integration variables and the original reference pole retained. -/
theorem renormalizedInverseNormPotential_inverseNormPotential {ψ : ℂ → ℂ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (w : ℂ) :
    renormalizedInverseNormPotential (inverseNormPotential ψ) w =
      ∫ z : ℂ, ψ z * renormalizedInverseNormConvolution w z := by
  have hi := integrable_compactTest_inverseNormConvolution hψ hc w
  calc
    renormalizedInverseNormPotential (inverseNormPotential ψ) w =
        ∫ t : ℂ, ∫ z : ℂ, ψ z * renormalizedInverseNormConvolutionIntegrand z w t := by
      rw [renormalizedInverseNormPotential]
      apply integral_congr_ae
      filter_upwards with t
      rw [inverseNormPotential_eq_integral, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with z
      dsimp only [renormalizedInverseNormConvolutionIntegrand]
      ring
    _ = ∫ z : ℂ, ∫ t : ℂ, ψ z * renormalizedInverseNormConvolutionIntegrand z w t :=
      (integral_integral_swap hi).symm
    _ = ∫ z : ℂ, ψ z * renormalizedInverseNormConvolution w z := by
      apply integral_congr_ae
      filter_upwards with z
      rw [integral_const_mul, renormalizedInverseNormConvolution]

end LowDimensionalTopology.Geometry.Quasiconformal
