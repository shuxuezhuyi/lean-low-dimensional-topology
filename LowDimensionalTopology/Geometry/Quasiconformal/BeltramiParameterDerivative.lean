/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Quasiconformal.LocallyUniformBeltramiVariation
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Locally uniform differentiation of measurable Beltrami families

The coefficients are actual complex L-infinity classes. The parameter may be real
or complex, and differentiability is expressed by a norm-small coefficient
remainder. The difference quotients of the actual canonical normalized maps
converge locally uniformly to the explicit normalized kernel integral.

The kernel estimates used here are due to Wu Xiaobin, from the fixed external
source at commit 1c0d5473c020b66ed5106331a38a61536760b9b2; its author and license
records are retained with the source. No uniform-convergence statement is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric MeasureTheory Filter Topology
open scoped ENNReal
open LowDimensionalTopology.Geometry.Teichmuller

namespace LowDimensionalTopology.Geometry.Quasiconformal

@[simp] theorem firstVariation_zero (w : ℂ) : firstVariation 0 w = 0 := by
  apply norm_le_zero_iff.mp
  simpa only [norm_zero, mul_zero] using firstVariation_norm_le (0 : MeasurableBeltramiSpace) w

/-- Complex scalar multiplication on actual coefficient classes commutes with variation. -/
theorem firstVariation_smul (ν : MeasurableBeltramiSpace) (a w : ℂ) :
    firstVariation (a • ν) w = a * firstVariation ν w := by
  simpa only [add_zero, firstVariation_zero] using firstVariation_smul_add ν 0 a w

/-- Subtraction on actual coefficient classes commutes with variation. -/
theorem firstVariation_sub (ν ρ : MeasurableBeltramiSpace) (w : ℂ) :
    firstVariation (ν - ρ) w = firstVariation ν w - firstVariation ρ w := by
  simpa [sub_eq_add_neg, add_comm] using firstVariation_smul_add ρ ν (-1) w

/-- The integral operator has a common norm bound on each bounded disc. -/
theorem firstVariation_uniform_norm_le (R : ℝ) (_hR : 0 < R) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ν : MeasurableBeltramiSpace, ∀ w : ℂ, ‖w‖ ≤ R →
      ‖firstVariation ν w‖ ≤ D * ‖ν‖ := by
  let B : ℝ := max R 1
  have hB : 1 ≤ B := le_max_right _ _
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  obtain ⟨C, hC, hkernel⟩ := LiZhongQC.ahK_lintegral_sub_le hB
  let L : ℝ := C * Real.sqrt B + (C + 32 * Real.pi) * B
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hkernelBound : ∀ w : ℂ, ‖w‖ ≤ R → ∫ ζ, ‖LiZhongQC.ahKer w ζ‖ ≤ L := by
    intro w hw
    have hwB : ‖w‖ ≤ B := hw.trans (le_max_left _ _)
    by_cases hw0 : w = 0
    · simpa only [hw0, LiZhongQC.ahK_ker_zero, norm_zero, integral_zero] using hL
    · have h := hkernel w 0 hwB (by simpa only [norm_zero] using hB₀) hw0
      simp only [LiZhongQC.ahK_ker_zero, sub_zero] at h
      have hnn : 0 ≤ C * Real.sqrt ‖w‖ + (C + 32 * Real.pi) * ‖w‖ := by positivity
      have hreal := ENNReal.toReal_le_of_le_ofReal hnn h
      rw [integral_norm_eq_lintegral_enorm
        (LiZhongQC.ahK_measurable w).aestronglyMeasurable]
      calc _ ≤ C * Real.sqrt ‖w‖ + (C + 32 * Real.pi) * ‖w‖ := hreal
        _ ≤ L := by dsimp only [L]; gcongr
  refine ⟨(1 / Real.pi) * L, by positivity, ?_⟩
  intro ν w hw
  calc ‖firstVariation ν w‖ ≤ (1 / Real.pi) * (∫ ζ, ‖firstVariationKernel w ζ‖) * ‖ν‖ :=
      firstVariation_norm_le ν w
    _ ≤ ((1 / Real.pi) * L) * ‖ν‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      change (∫ ζ, ‖LiZhongQC.ahKer w ζ‖) ≤ L
      exact hkernelBound w hw

/-- A uniform difference-quotient estimate separates the quadratic solution remainder
from the actual norm error in the coefficient derivative. -/
theorem normalizedSolution_uniform_differenceQuotient_bound (R : ℝ) (hR : 0 < R) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ μ : MeasurableBeltramiBall,
      ‖μ.val‖ < 1 / 4 → ∀ ν : MeasurableBeltramiSpace, ∀ t w : ℂ, ‖w‖ ≤ R →
        ‖(MeasurableBeltramiBall.normalizedSolution μ w - w) / t - firstVariation ν w‖ ≤
          C * ‖μ.val‖ ^ 2 / ‖t‖ + D * ‖t⁻¹ • μ.val - ν‖ := by
  obtain ⟨C, hC, hquad⟩ := normalizedSolution_uniform_quadratic R hR
  obtain ⟨D, hD, hlinear⟩ := firstVariation_uniform_norm_le R hR
  refine ⟨C, D, hC, hD, ?_⟩
  intro μ hμ ν t w hw
  have heq : (MeasurableBeltramiBall.normalizedSolution μ w - w) / t - firstVariation ν w =
      (MeasurableBeltramiBall.normalizedSolution μ w - w - firstVariation μ.val w) / t +
        firstVariation (t⁻¹ • μ.val - ν) w := by
    rw [firstVariation_sub, firstVariation_smul]
    ring
  rw [heq]
  calc _ ≤ ‖(MeasurableBeltramiBall.normalizedSolution μ w - w - firstVariation μ.val w) / t‖ +
      ‖firstVariation (t⁻¹ • μ.val - ν) w‖ := norm_add_le _ _
    _ ≤ C * ‖μ.val‖ ^ 2 / ‖t‖ + D * ‖t⁻¹ • μ.val - ν‖ := by
      apply add_le_add
      · rw [norm_div]
        exact div_le_div_of_nonneg_right (hquad μ hμ w hw) (norm_nonneg _)
      · exact hlinear _ w hw

/-- A norm-differentiable coefficient family yields locally uniform difference quotients.
This filter formulation includes both real and complex parameters without requiring
pointwise differentiability of a chosen representative of an L-infinity class. -/
theorem normalizedSolution_locallyUniform_differenceQuotient
    {ι : Type*} {l : Filter ι} {a : ι → ℂ} (ha : Tendsto a l (𝓝 0))
    (ha₀ : ∀ᶠ t in l, a t ≠ 0) (ν : MeasurableBeltramiSpace)
    {ε : ι → MeasurableBeltramiSpace} (hε : Tendsto ε l (𝓝 0))
    (μ : ι → MeasurableBeltramiBall)
    (hμ : ∀ᶠ t in l, (μ t).val = a t • (ν + ε t)) :
    TendstoLocallyUniformly
      (fun t w => (MeasurableBeltramiBall.normalizedSolution (μ t) w - w) / a t)
      (firstVariation ν) l := by
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro K hK
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨C, D, hC, -, hbound⟩ := normalizedSolution_uniform_differenceQuotient_bound R hR
  let B : ℝ := ‖ν‖ + 1
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hanorm : Tendsto (fun t => ‖a t‖) l (𝓝 0) := by simpa only [norm_zero] using ha.norm
  have hεnorm : Tendsto (fun t => ‖ε t‖) l (𝓝 0) := by simpa only [norm_zero] using hε.norm
  have hμzero : Tendsto (fun t => (μ t).val) l (𝓝 0) := by
    have h := ha.smul ((tendsto_const_nhds (x := ν)).add hε)
    have h' : Tendsto (fun t => a t • (ν + ε t)) l (𝓝 (0 : MeasurableBeltramiSpace)) := by
      simpa only [add_zero, zero_smul] using h
    exact h'.congr' (Filter.EventuallyEq.symm hμ)
  have hμnorm : Tendsto (fun t => ‖(μ t).val‖) l (𝓝 0) := by
    simpa only [norm_zero] using hμzero.norm
  have hsmall : ∀ᶠ t in l, ‖(μ t).val‖ < 1 / 4 :=
    hμnorm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hεle : ∀ᶠ t in l, ‖ε t‖ ≤ 1 :=
    (hεnorm.eventually (gt_mem_nhds zero_lt_one)).mono fun _ ht => ht.le
  have herror : Tendsto (fun t => C * B ^ 2 * ‖a t‖ + D * ‖ε t‖) l (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (hanorm.const_mul (C * B ^ 2)).add (hεnorm.const_mul D)
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [herror.eventually (gt_mem_nhds hη), hsmall, hεle, ha₀, hμ]
    with t htη htμ htε hta htdecomp
  intro w hw
  rw [dist_comm, dist_eq_norm]
  have hscale : (a t)⁻¹ • (μ t).val - ν = ε t := by
    rw [htdecomp, smul_smul, inv_mul_cancel₀ hta, one_smul]
    exact add_sub_cancel_left ν (ε t)
  have hμbound : ‖(μ t).val‖ ≤ ‖a t‖ * B := by
    rw [htdecomp, norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_add_le ν (ε t)).trans (add_le_add (le_refl ‖ν‖) htε)
  have hsq : ‖(μ t).val‖ ^ 2 ≤ (‖a t‖ * B) ^ 2 := by
    have hnonneg := mul_nonneg (sub_nonneg.mpr hμbound)
      (add_nonneg (mul_nonneg (norm_nonneg (a t)) hB) (norm_nonneg (μ t).val))
    nlinarith
  have hrem : C * ‖(μ t).val‖ ^ 2 / ‖a t‖ ≤ C * B ^ 2 * ‖a t‖ := by
    calc _ ≤ C * (‖a t‖ * B) ^ 2 / ‖a t‖ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC) (norm_nonneg _)
      _ = C * B ^ 2 * ‖a t‖ := by
        field_simp [norm_ne_zero_iff.mpr hta]
  calc _ ≤ C * ‖(μ t).val‖ ^ 2 / ‖a t‖ + D * ‖(a t)⁻¹ • (μ t).val - ν‖ :=
      hbound (μ t) htμ ν (a t) w (hKR w hw)
    _ ≤ C * B ^ 2 * ‖a t‖ + D * ‖ε t‖ := by rw [hscale]; exact add_le_add hrem le_rfl
    _ < η := htη

/-- For a complex parameter, the derivative is the actual normalized kernel integral,
and convergence holds locally uniformly throughout the plane. -/
theorem normalizedSolution_complex_parameter_firstVariation
    (ν : MeasurableBeltramiSpace) {ε : ℂ → MeasurableBeltramiSpace}
    (hε : Tendsto ε (𝓝[≠] (0 : ℂ)) (𝓝 0)) (μ : ℂ → MeasurableBeltramiBall)
    (hμ : ∀ᶠ t in 𝓝[≠] (0 : ℂ), (μ t).val = t • (ν + ε t)) :
    TendstoLocallyUniformly
      (fun t w => (MeasurableBeltramiBall.normalizedSolution (μ t) w - w) / t)
      (firstVariation ν) (𝓝[≠] (0 : ℂ)) := by
  apply normalizedSolution_locallyUniform_differenceQuotient
    (tendsto_id.mono_left nhdsWithin_le_nhds) _ ν hε μ hμ
  filter_upwards [self_mem_nhdsWithin] with t ht
  simpa only [id_eq, mem_compl_iff, mem_singleton_iff] using ht

/-- The same integral and locally uniform limit hold for a real parameter. -/
theorem normalizedSolution_real_parameter_firstVariation
    (ν : MeasurableBeltramiSpace) {ε : ℝ → MeasurableBeltramiSpace}
    (hε : Tendsto ε (𝓝[≠] (0 : ℝ)) (𝓝 0)) (μ : ℝ → MeasurableBeltramiBall)
    (hμ : ∀ᶠ t in 𝓝[≠] (0 : ℝ), (μ t).val = (t : ℂ) • (ν + ε t)) :
    TendstoLocallyUniformly
      (fun t w => (MeasurableBeltramiBall.normalizedSolution (μ t) w - w) / (t : ℂ))
      (firstVariation ν) (𝓝[≠] (0 : ℝ)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ha : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [Complex.ofReal_zero, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto 0).comp ht
  apply normalizedSolution_locallyUniform_differenceQuotient ha _ ν hε μ hμ
  filter_upwards [self_mem_nhdsWithin] with t htn
  exact Complex.ofReal_ne_zero.mpr (by simpa only [mem_compl_iff, mem_singleton_iff] using htn)

private theorem normalizedSolution_eq_refl_of_zero (μ : MeasurableBeltramiBall)
    (hμ : μ.val = 0) : MeasurableBeltramiBall.normalizedSolution μ = Homeomorph.refl ℂ := by
  have hae : (μ.val : ℂ → ℂ) =ᵐ[volume] (0 : ℂ → ℂ) := by
    rw [hμ]
    exact Lp.coeFn_zero ℂ (⊤ : ℝ≥0∞) volume
  exact MeasurableBeltramiBall.normalizedSolution_eq_of_ae μ hae (Homeomorph.refl ℂ)
    (LiZhongQC.td_id_normalized (Eventually.of_forall fun _ => rfl))

/-- At a genuinely zero base coefficient, the actual normalized maps are complex
parameter differentiable, with the explicit normalized kernel integral as derivative. -/
theorem normalizedSolution_complex_parameter_hasDerivAt
    (ν : MeasurableBeltramiSpace) {ε : ℂ → MeasurableBeltramiSpace}
    (hε : Tendsto ε (𝓝[≠] (0 : ℂ)) (𝓝 0)) (μ : ℂ → MeasurableBeltramiBall)
    (hμ : ∀ᶠ t in 𝓝[≠] (0 : ℂ), (μ t).val = t • (ν + ε t))
    (hzero : (μ 0).val = 0) (w : ℂ) :
    HasDerivAt (fun t => MeasurableBeltramiBall.normalizedSolution (μ t) w)
      (firstVariation ν w) 0 := by
  have hlimit :=
    (normalizedSolution_complex_parameter_firstVariation ν hε μ hμ).tendstoLocallyUniformlyOn.tendsto_at
      (mem_univ w)
  have hid : MeasurableBeltramiBall.normalizedSolution (μ 0) w = w := by
    rw [normalizedSolution_eq_refl_of_zero (μ 0) hzero]
    rfl
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [zero_add, hid, smul_eq_mul, div_eq_mul_inv, mul_comm] using hlimit

/-- At a genuinely zero base coefficient, the same explicit kernel gives the
ordinary derivative with respect to a real parameter. -/
theorem normalizedSolution_real_parameter_hasDerivAt
    (ν : MeasurableBeltramiSpace) {ε : ℝ → MeasurableBeltramiSpace}
    (hε : Tendsto ε (𝓝[≠] (0 : ℝ)) (𝓝 0)) (μ : ℝ → MeasurableBeltramiBall)
    (hμ : ∀ᶠ t in 𝓝[≠] (0 : ℝ), (μ t).val = (t : ℂ) • (ν + ε t))
    (hzero : (μ 0).val = 0) (w : ℂ) :
    HasDerivAt (fun t => MeasurableBeltramiBall.normalizedSolution (μ t) w)
      (firstVariation ν w) 0 := by
  have hlimit :=
    (normalizedSolution_real_parameter_firstVariation ν hε μ hμ).tendstoLocallyUniformlyOn.tendsto_at
      (mem_univ w)
  have hid : MeasurableBeltramiBall.normalizedSolution (μ 0) w = w := by
    rw [normalizedSolution_eq_refl_of_zero (μ 0) hzero]
    rfl
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [zero_add, hid, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
    using hlimit

end LowDimensionalTopology.Geometry.Quasiconformal
