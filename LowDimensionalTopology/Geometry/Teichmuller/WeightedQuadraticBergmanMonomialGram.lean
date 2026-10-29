module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergmanKernelSeries
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The exact monomial Gram matrix in the original weighted disc space

Mapping the true kernel series through the conjugate-linear inner-product
functional gives scalar series for every monomial. Their actual positive
convergence radius and uniqueness identify the Gram coefficients, without any
assumption of orthogonality or completeness of a prescribed monomial basis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ComplexConjugate ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman

private def monomialGramCoefficient (m n : ℕ) : ℂ :=
  (diskKernelSeriesCoefficient n : ℂ) * inner ℂ (monomialElement n) (monomialElement m)

private theorem monomialGramCoefficient_hasSum (m : ℕ) {a : ℂ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) :
    HasSum (fun n => monomialGramCoefficient m n * a ^ n) (a ^ m) := by
  have hs := (innerSLFlip ℂ (monomialElement m)).hasSum
    (diskKernelSeries_hasSum ha)
  change HasSum (fun n => inner ℂ (diskKernelSeriesTerm a n) (monomialElement m))
    (inner ℂ (diskKernelElement ha) (monomialElement m)) at hs
  have he : inner ℂ (diskKernelElement ha) (monomialElement m) = a ^ m := by
    rw [← disk_reproducing_inner (monomialElement m) ha, monomialElement_coefficient m ha]
  rw [he] at hs
  refine hs.congr_fun fun n => ?_
  change ((diskKernelSeriesCoefficient n : ℂ) *
    inner ℂ (monomialElement n) (monomialElement m)) * a ^ n =
      inner ℂ (((diskKernelSeriesCoefficient n : ℂ) * conj a ^ n) • monomialElement n)
        (monomialElement m)
  rw [inner_smul_left (𝕜 := ℂ) (monomialElement n) (monomialElement m)
    ((diskKernelSeriesCoefficient n : ℂ) * conj a ^ n)]
  simp only [map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj]
  ring

private theorem monomialGramCoefficient_norm_le (m n : ℕ) :
    ‖monomialGramCoefficient m n‖ ≤
      diskKernelSeriesCoefficient n * ‖monomialElement 0‖ * ‖monomialElement m‖ := by
  have hi : ‖inner ℂ (monomialElement n) (monomialElement m)‖ ≤
      ‖monomialElement n‖ * ‖monomialElement m‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) (monomialElement n) (monomialElement m)
    rw [← RCLike.sqrt_normSq_eq_norm, RCLike.normSq_apply,
      RCLike.re_eq_complex_re, RCLike.im_eq_complex_im] at h
    simpa only [Complex.norm_def, Complex.normSq_apply] using h
  change ‖(diskKernelSeriesCoefficient n : ℂ) *
    inner ℂ (monomialElement n) (monomialElement m)‖ ≤ _
  rw [norm_mul, Complex.norm_of_nonneg (diskKernelSeriesCoefficient_pos n).le]
  calc
    diskKernelSeriesCoefficient n * ‖inner ℂ (monomialElement n) (monomialElement m)‖ ≤
        diskKernelSeriesCoefficient n * (‖monomialElement n‖ * ‖monomialElement m‖) :=
      mul_le_mul_of_nonneg_left hi (diskKernelSeriesCoefficient_pos n).le
    _ ≤ diskKernelSeriesCoefficient n * (‖monomialElement 0‖ * ‖monomialElement m‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (monomialElement_norm_le n) (norm_nonneg _))
        (diskKernelSeriesCoefficient_pos n).le
    _ = _ := by ring

private theorem monomialGramCoefficient_hasFPowerSeriesAt (m : ℕ) :
    HasFPowerSeriesAt (fun a : ℂ => a ^ m)
      (FormalMultilinearSeries.ofScalars ℂ (monomialGramCoefficient m)) 0 := by
  let r : ℝ≥0 := 1 / 2
  have hr : (r : ℝ) < 1 := by norm_num [r]
  have hrr : ‖(r : ℝ)‖ < 1 := by
    norm_num [r, Real.norm_eq_abs]
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
    (r := (r : ℝ)) 3 hrr).summable
  have hA : Summable (fun n => diskKernelSeriesCoefficient n * (r : ℝ) ^ n) := by
    simpa only [diskKernelSeriesCoefficient, mul_assoc] using hs.mul_left (12 / Real.pi : ℝ)
  have hmajor : Summable (fun n => diskKernelSeriesCoefficient n *
      ‖monomialElement 0‖ * ‖monomialElement m‖ * (r : ℝ) ^ n) := by
    exact (hA.mul_right (‖monomialElement 0‖ * ‖monomialElement m‖)).congr fun n => by ring
  have hnorm : Summable (fun n => ‖monomialGramCoefficient m n‖ * (r : ℝ) ^ n) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg r.property n))
      (fun n => mul_le_mul_of_nonneg_right (monomialGramCoefficient_norm_le m n)
        (pow_nonneg r.property n)) hmajor
  refine ⟨(r : ℝ≥0∞), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · apply (FormalMultilinearSeries.ofScalars ℂ (monomialGramCoefficient m)).le_radius_of_summable_norm
    simpa only [FormalMultilinearSeries.ofScalars_norm] using hnorm
  · norm_num [r]
  · intro a ha
    have haball : a ∈ Metric.ball (0 : ℂ) (r : ℝ) := by
      simpa only [Metric.eball_coe] using ha
    have haD : a ∈ Metric.ball (0 : ℂ) 1 :=
      mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp haball).trans hr)
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using
      monomialGramCoefficient_hasSum m haD

private theorem singleMonomial_hasFPowerSeriesAt (m : ℕ) :
    HasFPowerSeriesAt (fun a : ℂ => a ^ m)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => if n = m then (1 : ℂ) else 0)) 0 := by
  let d : ℕ → ℂ := fun n => if n = m then 1 else 0
  change HasFPowerSeriesAt (fun a : ℂ => a ^ m) (FormalMultilinearSeries.ofScalars ℂ d) 0
  have hz : ∀ᶠ n in atTop, (FormalMultilinearSeries.ofScalars ℂ d) n = 0 := by
    filter_upwards [eventually_gt_atTop m] with n hn
    exact FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero ℂ (by simp [d, ne_of_gt hn])
  have hrad := (FormalMultilinearSeries.ofScalars ℂ d).radius_eq_top_of_eventually_eq_zero hz
  refine ⟨∞, ?_⟩
  refine ⟨?_, by simp, ?_⟩
  · rw [hrad]
  · intro a _
    have hs : HasSum (fun n => d n * a ^ n) (a ^ m) := by
      refine (hasSum_ite_eq m (a ^ m)).congr_fun fun n => ?_
      by_cases hn : n = m
      · simp [d, hn]
      · simp [d, hn]
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using hs

/-- The full Gram matrix of the original monomials, with no basis assumption. -/
theorem monomialElement_gram (n m : ℕ) :
    inner ℂ (monomialElement n) (monomialElement m) =
      if n = m then (diskKernelSeriesCoefficient n : ℂ)⁻¹ else 0 := by
  have hcoef : monomialGramCoefficient m = (fun j => if j = m then (1 : ℂ) else 0) :=
    FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
      ((monomialGramCoefficient_hasFPowerSeriesAt m).eq_formalMultilinearSeries
        (singleMonomial_hasFPowerSeriesAt m))
  have hc : (diskKernelSeriesCoefficient n : ℂ) *
      inner ℂ (monomialElement n) (monomialElement m) = if n = m then 1 else 0 :=
    congrFun hcoef n
  have hA : (diskKernelSeriesCoefficient n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (diskKernelSeriesCoefficient_pos n).ne'
  by_cases hnm : n = m
  · rw [ite_eq_left hnm] at hc ⊢
    exact mul_left_cancel₀ hA (hc.trans (mul_inv_cancel₀ hA).symm)
  · rw [ite_eq_right hnm] at hc ⊢
    exact (mul_eq_zero.mp hc).resolve_left hA

/-- The exact native norm square is the reciprocal of the proved kernel coefficient. -/
theorem monomialElement_norm_sq (n : ℕ) :
    ‖monomialElement n‖ ^ 2 = 1 / diskKernelSeriesCoefficient n := by
  have hn := norm_sq_eq_re_inner (𝕜 := ℂ) (monomialElement n)
  change ‖monomialElement n‖ ^ 2 = (inner ℂ (monomialElement n) (monomialElement n)).re at hn
  rw [monomialElement_gram n n, ite_eq_left rfl] at hn
  simpa only [← Complex.ofReal_inv, Complex.ofReal_re, one_div] using hn

/-- The exact cubic denominator agrees with the original disc weight. -/
theorem monomialElement_norm_sq_explicit (n : ℕ) :
    ‖monomialElement n‖ ^ 2 =
      Real.pi / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  rw [monomialElement_norm_sq, diskKernelSeriesCoefficient_eq_product]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
  ring

/-- The original native monomial norm has the specified positive square-root value. -/
theorem monomialElement_norm (n : ℕ) :
    ‖monomialElement n‖ =
      Real.sqrt (Real.pi / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) := by
  rw [← monomialElement_norm_sq_explicit n, Real.sqrt_sq (norm_nonneg _)]

end LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman
