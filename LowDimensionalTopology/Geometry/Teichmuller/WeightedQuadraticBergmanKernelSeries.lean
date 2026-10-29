module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergmanMonomials
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The monomial kernel series in the original weighted disc space

The actual monomial norm bound gives absolute convergence in the original
complete disc space. Continuous evaluation supplied by the proved reproducing
formula identifies its sum with the literal kernel, without assuming a basis or
orthogonality of the monomials.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ComplexConjugate ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman

/-- The coefficients of the literal fourth-power kernel series. -/
def diskKernelSeriesCoefficient (n : ℕ) : ℝ :=
  (12 / Real.pi) * ((n + 3).choose 3 : ℝ)

theorem diskKernelSeriesCoefficient_pos (n : ℕ) : 0 < diskKernelSeriesCoefficient n := by
  unfold diskKernelSeriesCoefficient
  exact mul_pos (div_pos (by norm_num) Real.pi_pos)
    (Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_add_left 3 n)))

/-- The binomial coefficient is exactly the specified cubic normalization. -/
theorem diskKernelSeriesCoefficient_eq_product (n : ℕ) :
    diskKernelSeriesCoefficient n =
      (2 / Real.pi) * ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by
  have hc : (n + 1) * (n + 2) * (n + 3) = 6 * (n + 3).choose 3 := by
    calc
      (n + 1) * (n + 2) * (n + 3) = (n + 1).ascFactorial 3 := by
        simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
        ring
      _ = 6 * (n + 3).choose 3 := by
        simpa only [Nat.factorial_succ, Nat.factorial_zero] using
          Nat.ascFactorial_eq_factorial_mul_choose n 3
  have hcr : ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) =
      6 * ((n + 3).choose 3 : ℝ) := by exact_mod_cast hc
  unfold diskKernelSeriesCoefficient
  calc
    (12 / Real.pi) * ((n + 3).choose 3 : ℝ) =
        (2 / Real.pi) * (6 * ((n + 3).choose 3 : ℝ)) := by ring
    _ = (2 / Real.pi) * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
      rw [← hcr]
    _ = _ := by ring

/-- Every term lies in the unchanged original weighted L² carrier. -/
def diskKernelSeriesTerm (a : ℂ) (n : ℕ) : Disk :=
  ((diskKernelSeriesCoefficient n : ℂ) * conj a ^ n) • monomialElement n

/-- The native monomial norm bound supplies the summable geometric majorant. -/
theorem diskKernelSeriesTerm_norm_le (a : ℂ) (n : ℕ) :
    ‖diskKernelSeriesTerm a n‖ ≤
      diskKernelSeriesCoefficient n * ‖a‖ ^ n * ‖monomialElement 0‖ := by
  change ‖((diskKernelSeriesCoefficient n : ℂ) * conj a ^ n) • monomialElement n‖ ≤ _
  rw [norm_smul, norm_mul, Complex.norm_of_nonneg (diskKernelSeriesCoefficient_pos n).le,
    norm_pow, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (monomialElement_norm_le n)
    (mul_nonneg (diskKernelSeriesCoefficient_pos n).le (pow_nonneg (norm_nonneg a) n))

private theorem diskKernelSeries_majorant_summable {a : ℂ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) :
    Summable (fun n => diskKernelSeriesCoefficient n * ‖a‖ ^ n * ‖monomialElement 0‖) := by
  have hr : ‖(‖a‖ : ℝ)‖ < 1 := by
    simpa only [norm_norm] using (mem_ball_zero_iff.mp ha)
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 3 hr).summable
  have ht := (hs.mul_left (12 / Real.pi : ℝ)).mul_right ‖monomialElement 0‖
  simpa only [diskKernelSeriesCoefficient, mul_assoc] using ht

/-- The actual original disc-norm series is absolutely summable for every disc point. -/
theorem diskKernelSeries_norm_summable {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1) :
    Summable (fun n => ‖diskKernelSeriesTerm a n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (diskKernelSeriesTerm_norm_le a) (diskKernelSeries_majorant_summable ha)

/-- The scalar monomial series sums to the literal kernel at all original disc points. -/
theorem diskKernelSeries_scalar_hasSum {a b : ℂ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) (hb : b ∈ Metric.ball (0 : ℂ) 1) :
    HasSum (fun n => (diskKernelSeriesCoefficient n : ℂ) * (conj a * b) ^ n)
      (diskQuadraticKernel a b) := by
  have hr : ‖conj a * b‖ < 1 := by
    calc
      ‖conj a * b‖ = ‖a‖ * ‖b‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hb).le (norm_nonneg a)
      _ = ‖a‖ := mul_one _
      _ < 1 := mem_ball_zero_iff.mp ha
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℂ) 3 hr).mul_left
    (12 / Real.pi : ℂ)
  have ht : HasSum (fun n => (diskKernelSeriesCoefficient n : ℂ) * (conj a * b) ^ n)
      ((12 / Real.pi : ℂ) * (1 / (1 - conj a * b) ^ (3 + 1))) := by
    exact hs.congr_fun fun n => by
      simp only [diskKernelSeriesCoefficient, Complex.ofReal_mul, Complex.ofReal_div,
        Complex.ofReal_ofNat, Complex.ofReal_natCast, mul_assoc]
  simpa only [diskQuadraticKernel, mul_one_div] using ht

/-- The term retains the exact conjugate-first scalar coefficient at every disc point. -/
theorem diskKernelSeriesTerm_coefficient (a : ℂ) (n : ℕ) {b : ℂ}
    (hb : b ∈ Metric.ball (0 : ℂ) 1) :
    coefficient (diskKernelSeriesTerm a n) b =
      (diskKernelSeriesCoefficient n : ℂ) * (conj a * b) ^ n := by
  rw [disk_reproducing_inner (diskKernelSeriesTerm a n) hb]
  change inner ℂ (diskKernelElement hb)
    (((diskKernelSeriesCoefficient n : ℂ) * conj a ^ n) • monomialElement n) = _
  rw [inner_smul_right (𝕜 := ℂ) (diskKernelElement hb) (monomialElement n)
    ((diskKernelSeriesCoefficient n : ℂ) * conj a ^ n),
    ← disk_reproducing_inner (monomialElement n) hb,
    monomialElement_coefficient n hb, mul_pow, mul_assoc]

/-- The absolutely convergent series sums to the actual original disc kernel element. -/
theorem diskKernelSeries_hasSum {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1) :
    HasSum (diskKernelSeriesTerm a) (diskKernelElement ha) := by
  have hs : Summable (diskKernelSeriesTerm a) := (diskKernelSeries_norm_summable ha).of_norm
  have he : (∑' n, diskKernelSeriesTerm a n) = diskKernelElement ha := by
    apply disk_coefficient_ext
    intro b hb
    have hm := (innerSL ℂ (diskKernelElement hb)).hasSum hs.hasSum
    have hv : HasSum (fun n => (diskKernelSeriesCoefficient n : ℂ) * (conj a * b) ^ n)
        (coefficient (∑' n, diskKernelSeriesTerm a n) b) := by
      rw [disk_reproducing_inner _ hb]
      exact hm.congr_fun fun n => by
        change (diskKernelSeriesCoefficient n : ℂ) * (conj a * b) ^ n =
          inner ℂ (diskKernelElement hb) (diskKernelSeriesTerm a n)
        rw [← disk_reproducing_inner (diskKernelSeriesTerm a n) hb,
          diskKernelSeriesTerm_coefficient a n hb]
    rw [diskKernelElement_coefficient ha hb]
    exact hv.unique (diskKernelSeries_scalar_hasSum ha hb)
  exact he ▸ hs.hasSum

end LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman
