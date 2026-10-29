/-
Released under Apache 2.0 license as described in the file LICENSE.
The difference-kernel estimates are adapted from Wu Xiaobin's
Li-Zhong-QC-formalization, commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
The fixed external source retains its author and license records.
-/
module
public import LowDimensionalTopology.Geometry.Quasiconformal.NormalizedCauchyPotential
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# The normalized Cauchy potential on planar Lp input

For p greater than two, the difference of Cauchy kernels is genuinely integrable
against every Lp input, without a support hypothesis. Its common Hölder estimate
is obtained from the actual difference-kernel integral. The proof never subtracts
two potentially divergent ordinary Cauchy integrals.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric MeasureTheory Filter Topology Complex
open scoped ENNReal Real

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem exists_cauchy_conjugate {p : ℝ} (hp : 2 < p) :
    ∃ q : ℝ, p.HolderConjugate q ∧ 1 < q ∧ q < 2 ∧ q = p / (p - 1) := by
  have hp1 : 1 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  let q : ℝ := p / (p - 1)
  refine ⟨q, (Real.holderConjugate_iff_eq_conjExponent hp1).2 rfl, ?_, ?_, rfl⟩
  · change 1 < p / (p - 1)
    rw [lt_div_iff₀ hpm]
    linarith
  · change p / (p - 1) < 2
    rw [div_lt_iff₀ hpm]
    linarith

private theorem cauchy_difference_integrable {p : ℝ} (hp : 2 < p)
    {h : ℂ → ℂ} (hh : MemLp h (ENNReal.ofReal p)) (z₁ z₂ : ℂ) :
    Integrable (fun ζ => h ζ / (ζ - z₁) - h ζ / (ζ - z₂)) volume := by
  rcases eq_or_ne z₁ z₂ with rfl | hne
  · apply (integrable_zero ℂ ℂ volume).congr
    exact Eventually.of_forall fun ζ => by simp only [Pi.zero_apply, sub_self]
  · obtain ⟨q, hpq, hq1, hq2, -⟩ := exists_cauchy_conjugate hp
    exact LiZhongQC.integrable_cauchy_kernel_sub hp hpq hq1 hq2 hh hne

/-- The normalized kernel is genuinely integrable for every planar Lp input,
including those with unbounded support. -/
theorem normalizedCauchyPotential_integrand_integrable_of_memLp
    {p : ℝ} (hp : 2 < p) {h : ℂ → ℂ} (hh : MemLp h (ENNReal.ofReal p)) (z : ℂ) :
    Integrable (fun ζ => h ζ * (1 / (ζ - z) - 1 / ζ)) volume := by
  have heq : (fun ζ => h ζ * (1 / (ζ - z) - 1 / ζ)) =
      fun ζ => h ζ / (ζ - z) - h ζ / (ζ - (0 : ℂ)) := by
    funext ζ
    simp only [mul_sub, mul_one_div, sub_zero]
  rw [heq]
  exact cauchy_difference_integrable hp hh z 0

/-- Differences of normalized potentials are integrals of the corresponding
kernel difference. Only integrable normalized kernels are subtracted. -/
theorem normalizedCauchyPotential_sub_eq_integral
    {p : ℝ} (hp : 2 < p) {h : ℂ → ℂ} (hh : MemLp h (ENNReal.ofReal p)) (z₁ z₂ : ℂ) :
    normalizedCauchyPotential h z₁ - normalizedCauchyPotential h z₂ =
      -(1 / (Real.pi : ℂ)) * ∫ ζ, (h ζ / (ζ - z₁) - h ζ / (ζ - z₂)) := by
  have h1 := normalizedCauchyPotential_integrand_integrable_of_memLp hp hh z₁
  have h2 := normalizedCauchyPotential_integrand_integrable_of_memLp hp hh z₂
  unfold normalizedCauchyPotential
  rw [← mul_sub, ← integral_sub h1 h2]
  congr 1
  apply integral_congr_ae
  filter_upwards with ζ
  simp only [mul_sub, mul_one_div]
  ring

/-- The normalized potential has a common global Hölder estimate for every
Lp input, with a constant depending only on p. -/
theorem normalizedCauchyPotential_holder_bound {p : ℝ} (hp : 2 < p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h : ℂ → ℂ, MemLp h (ENNReal.ofReal p) → ∀ z₁ z₂ : ℂ,
      ‖normalizedCauchyPotential h z₁ - normalizedCauchyPotential h z₂‖ ≤
        M * (eLpNorm h (ENNReal.ofReal p)).toReal * ‖z₁ - z₂‖ ^ ((p - 2) / p) := by
  obtain ⟨q, hpq, hq1, hq2, hq⟩ := exists_cauchy_conjugate hp
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have hp0 : 0 < p := by linarith
  have h2q : 0 < 2 - q := by linarith
  have h2q2 : 0 < 2 * q - 2 := by linarith
  let C : ℝ := 2 * (2 * π / (2 - q) * 2 ^ (2 * q - 2)) +
    2 * π / (2 * q - 2) * 4 ^ (3 * q - 2)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hα : 0 < (p - 2) / p := div_pos (by linarith) hp0
  have hM : 0 ≤ 1 / π * C ^ (1 / q) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hC _)
  refine ⟨1 / π * C ^ (1 / q), hM, fun h hh z₁ z₂ => ?_⟩
  rcases eq_or_ne z₁ z₂ with rfl | hne
  · simp only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero, le_refl]
  have hd : 0 < ‖z₁ - z₂‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hcoef : ‖(-(1 / π : ℂ))‖ₑ = ENNReal.ofReal (1 / π) := by
    rw [← ofReal_norm (-(1 / π : ℂ))]
    congr 1
    rw [norm_neg, norm_div, norm_one, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  have hkey : ‖normalizedCauchyPotential h z₁ - normalizedCauchyPotential h z₂‖ₑ ≤
      ENNReal.ofReal (1 / π) * (ENNReal.ofReal ‖z₁ - z₂‖ *
        (eLpNorm h (ENNReal.ofReal p) *
          ENNReal.ofReal (C * ‖z₁ - z₂‖ ^ (2 - 2 * q)) ^ (1 / q))) := by
    rw [normalizedCauchyPotential_sub_eq_integral hp hh z₁ z₂, enorm_mul, hcoef]
    exact mul_le_mul' le_rfl
      (LiZhongQC.enorm_integral_cauchy_sub_le hp hpq hq1 hq2 hh hne)
  have hfin : ENNReal.ofReal (1 / π) * (ENNReal.ofReal ‖z₁ - z₂‖ *
      (eLpNorm h (ENNReal.ofReal p) *
        ENNReal.ofReal (C * ‖z₁ - z₂‖ ^ (2 - 2 * q)) ^ (1 / q))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top hh.eLpNorm_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (div_nonneg zero_le_one hq0.le)
            ENNReal.ofReal_ne_top)))
  have hreal := ENNReal.toReal_mono hfin hkey
  rw [toReal_enorm] at hreal
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / π),
    ENNReal.toReal_ofReal (norm_nonneg _), ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ C * ‖z₁ - z₂‖ ^ (2 - 2 * q))] at hreal
  refine hreal.trans (le_of_eq ?_)
  rw [← LiZhongQC.conj_exponent_sub_div hp hq]
  linear_combination (1 / π * (eLpNorm h (ENNReal.ofReal p)).toReal) *
    LiZhongQC.rpow_collapse_aux hC hd hq0

/-- Every planar Lp input with p greater than two has a continuous actual
normalized potential; no compact-support or initial continuity assumption is added. -/
theorem normalizedCauchyPotential_continuous_of_memLp
    {p : ℝ} (hp : 2 < p) {h : ℂ → ℂ} (hh : MemLp h (ENNReal.ofReal p)) :
    Continuous (normalizedCauchyPotential h) := by
  obtain ⟨M, -, hbound⟩ := normalizedCauchyPotential_holder_bound hp
  have hα : 0 < (p - 2) / p := div_pos (by linarith) (by linarith)
  apply continuous_iff_continuousAt.mpr
  intro z
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hpow : ContinuousAt
      (fun w : ℂ => M * (eLpNorm h (ENNReal.ofReal p)).toReal * ‖w - z‖ ^ ((p - 2) / p)) z :=
    continuousAt_const.mul
      ((continuousAt_id.sub continuousAt_const).norm.rpow_const (Or.inr hα.le))
  have hlim : Tendsto
      (fun w : ℂ => M * (eLpNorm h (ENNReal.ofReal p)).toReal * ‖w - z‖ ^ ((p - 2) / p))
      (𝓝 z) (𝓝 0) := by
    simpa only [ContinuousAt, sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] using hpow
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with w hw
  simpa only [dist_eq_norm] using (hbound h hh w z).trans_lt hw

end LowDimensionalTopology.Geometry.Quasiconformal
