/-
The real norm-power derivative is reused from Wu Xiaobin's
Li-Zhong-QC-formalization, commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertKernelConvolution
public import LowDimensionalTopology.External.LiZhongQC.Ch03.S15_Distortion
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The real logarithmic kernel for the compact convolution Green identity

The kernel is locally integrable on the complex plane, differentiable
away from its pole, and has a vanishing logarithmic circle factor.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex Metric
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The real logarithm of the complex norm, embedded in the complex plane. -/
def realLogNormKernel (z : ℂ) : ℂ := (Real.log ‖z‖ : ℂ)

theorem measurable_realLogNormKernel : Measurable realLogNormKernel :=
  measurable_ofReal.comp (Real.measurable_log.comp measurable_norm)

theorem conj_realLogNormKernel (z : ℂ) : conj (realLogNormKernel z) = realLogNormKernel z := by
  simp only [realLogNormKernel, Complex.conj_ofReal]

/-- The logarithmic singularity is controlled by a norm and an inverse
norm, with the totalized value at zero included. -/
theorem abs_log_le_add_inv {r : ℝ} (hr : 0 ≤ r) : |Real.log r| ≤ r + r⁻¹ := by
  by_cases h0 : r = 0
  · simp only [h0, Real.log_zero, abs_zero, inv_zero, add_zero, le_refl]
  have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm h0)
  have h₁ := Real.log_le_sub_one_of_pos hp
  have h₂ := Real.one_sub_inv_le_log_of_pos hp
  apply abs_le.mpr
  constructor <;> linarith [inv_nonneg.mpr hr]

/-- The translated real logarithmic kernel has a genuine integral on
every bounded disc, including discs containing its pole. -/
theorem integrableOn_realLogNormKernel_ball {R : ℝ} (hR : 0 < R) (a : ℂ) :
    IntegrableOn (fun z : ℂ => realLogNormKernel (z - a)) (ball (0 : ℂ) R) := by
  have hi : IntegrableOn (fun z : ℂ => ‖z - a‖⁻¹) (ball (0 : ℂ) R)
      (volume : Measure ℂ) := by
    change Integrable (fun z : ℂ => ‖z - a‖⁻¹)
      ((volume : Measure ℂ).restrict (ball (0 : ℂ) R))
    convert! (LiZhongQC.integrableOn_cauchy_kernel_ball hR a).norm using 1
    funext z
    rw [one_div, norm_inv]
  have hn : IntegrableOn (fun z : ℂ => ‖z - a‖) (ball (0 : ℂ) R)
      (volume : Measure ℂ) :=
    (((continuous_id.sub continuous_const).norm.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) R))).mono_set ball_subset_closedBall
  refine Integrable.mono' (hn.add hi)
    (measurable_realLogNormKernel.comp (measurable_id.sub_const a)).aestronglyMeasurable.restrict ?_
  apply Eventually.of_forall
  intro z
  simpa only [realLogNormKernel, Complex.norm_real, Real.norm_eq_abs, Pi.add_apply] using
    abs_log_le_add_inv (norm_nonneg (z - a))

theorem locallyIntegrable_realLogNormKernel :
    LocallyIntegrable realLogNormKernel (volume : Measure ℂ) := by
  intro z
  refine ⟨ball (0 : ℂ) (‖z‖ + 1),
    isOpen_ball.mem_nhds (by simp only [mem_ball, dist_zero_right]; linarith), ?_⟩
  simpa only [sub_zero] using
    integrableOn_realLogNormKernel_ball (by positivity : 0 < ‖z‖ + 1) (0 : ℂ)

/-- The logarithmic kernel is C1 away from its actual pole. -/
theorem contDiffAt_realLogNormKernel {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ 1 realLogNormKernel z := by
  have hn : ContDiffAt ℝ 1 (fun v : ℂ => ‖v‖) z := contDiffAt_id.norm ℝ hz
  have hl := hn.log (norm_ne_zero_iff.mpr hz)
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp z hl

/-- The full real derivative of the literal real logarithmic kernel. -/
theorem hasFDerivAt_realLogNormKernel {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt realLogNormKernel
      (Complex.ofRealCLM.comp (((‖z‖ ^ 2)⁻¹) • innerSL ℝ z)) z := by
  have hn : HasFDerivAt (fun v : ℂ => ‖v‖) (‖z‖⁻¹ • innerSL ℝ z) z := by
    convert! LiZhongQC.s15_ra_hasFDerivAt_norm_rpow hz (1 : ℝ) using 1 <;>
      simp only [Real.rpow_one, one_mul,
        show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
  have hc : ‖z‖⁻¹ * ‖z‖⁻¹ = (‖z‖ ^ 2)⁻¹ := by rw [← inv_pow, pow_two]
  have hl : HasFDerivAt (fun v : ℂ => Real.log ‖v‖)
      (((‖z‖ ^ 2)⁻¹) • innerSL ℝ z) z := by
    simpa only [smul_smul, hc] using hn.log (norm_ne_zero_iff.mpr hz)
  convert! Complex.ofRealCLM.hasFDerivAt.comp z hl using 1

/-- The Wirtinger derivative retains the actual rational pole. -/
theorem dz_realLogNormKernel {z : ℂ} (hz : z ≠ 0) :
    LiZhongQC.dz realLogNormKernel z = 1 / (2 * z) := by
  have hdz : LiZhongQC.dz realLogNormKernel z = conj z / (2 * (‖z‖ : ℂ) ^ 2) := by
    rw [LiZhongQC.dz, (hasFDerivAt_realLogNormKernel hz).fderiv]
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      innerSL_apply_apply, Complex.ofRealCLM_apply, Complex.inner, smul_eq_mul]
    apply Complex.ext <;>
      simp [div_eq_mul_inv, Complex.mul_re, Complex.mul_im] <;> ring
  have hρ : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hn : z * conj z = (‖z‖ : ℂ) ^ 2 := by
    simpa only [Complex.ofReal_pow] using Complex.mul_conj' z
  have hc : conj z = (‖z‖ : ℂ) ^ 2 / z := by
    apply (eq_div_iff hz).mpr
    simpa only [mul_comm] using hn
  rw [hdz, hc]
  field_simp [hz, hρ]

theorem contDiffAt_shiftedRealLogNormKernel {a z : ℂ} (hz : z ≠ a) :
    ContDiffAt ℝ 1 (fun v : ℂ => realLogNormKernel (v - a)) z := by
  have hshift : ContDiffAt ℝ 1 (fun v : ℂ => v - a) z :=
    contDiffAt_id.sub contDiffAt_const
  exact (contDiffAt_realLogNormKernel (sub_ne_zero.mpr hz)).fun_comp z hshift

theorem differentiableAt_shiftedRealLogNormKernel {a z : ℂ} (hz : z ≠ a) :
    DifferentiableAt ℝ (fun v : ℂ => realLogNormKernel (v - a)) z :=
  (contDiffAt_shiftedRealLogNormKernel hz).differentiableAt one_ne_zero

theorem dz_shiftedRealLogNormKernel {a z : ℂ} (hz : z ≠ a) :
    LiZhongQC.dz (fun v : ℂ => realLogNormKernel (v - a)) z = 1 / (2 * (z - a)) := by
  have hd₀ := hasFDerivAt_realLogNormKernel (sub_ne_zero.mpr hz)
  have hd := hd₀.comp z ((hasFDerivAt_id z).sub_const a)
  simp only [Function.comp_def, id] at hd
  have heq : fderiv ℝ (fun v : ℂ => realLogNormKernel (v - a)) z =
      fderiv ℝ realLogNormKernel (z - a) := by
    rw [hd.fderiv, hd₀.fderiv]
    simp
  simpa only [LiZhongQC.dz, heq] using
    dz_realLogNormKernel (sub_ne_zero.mpr hz)

/-- Compact continuous tests give genuine global logarithmic integrals. -/
theorem integrable_compactTest_mul_realLogNormKernel {ψ : ℂ → ℂ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (a : ℂ) :
    Integrable (fun z : ℂ => ψ z * realLogNormKernel (z - a)) volume := by
  have h := (hc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_realLogNormKernel hψ a).integrable_swap
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [ContinuousLinearMap.mul_apply']
  rw [show realLogNormKernel (a - z) = realLogNormKernel (z - a) by
    simp only [realLogNormKernel, norm_sub_rev]]
  exact mul_comm _ _

/-- The rational integral occurring beside the logarithmic Green term is
also a genuine compact-test integral. -/
theorem integrable_compactTest_div_sub {ψ : ℂ → ℂ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (a : ℂ) :
    Integrable (fun z : ℂ => ψ z / (z - a)) volume := by
  have hi := integrable_inverseNormPotential hψ hc a
  refine Integrable.mono hi
    (hψ.measurable.div (measurable_id.sub_const a)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun z => by
    simp only [norm_mul, norm_inverseNormKernel, div_eq_mul_inv, norm_inv, le_refl]

/-- The factor controlling the actual logarithmic inner-circle integral
tends to zero through positive radii. -/
theorem tendsto_self_mul_abs_log_nhdsGT_zero :
    Tendsto (fun r : ℝ => r * |Real.log r|) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => Real.log r * r) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have ha : Tendsto (fun r : ℝ => |Real.log r * r|) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, abs_zero] using continuous_abs.continuousAt.tendsto.comp h
  apply ha.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [abs_mul, abs_of_pos hr]
  ring

end LowDimensionalTopology.Geometry.Quasiconformal
