/-
The Lp tail estimate is reused from Wu Xiaobin's
Li-Zhong-QC-formalization, commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.External.LiZhongQC.Ch02.S11_IntegralOperators
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Smooth compact cutoffs in the original planar Lp

For a smooth Lp function, ordinary smooth cutoffs preserve its values on
growing balls and converge in the same Lp. This supplies local agreement
as well as norm convergence for the noncompact intermediate transform.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The actual smooth cutoff has inner radius `n + 1` and outer radius `n + 2`. -/
def circularSmoothLpCutoff (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := (n : ℝ) + 1
  rOut := (n : ℝ) + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The literal smooth compact cutoff of the original planar function. -/
def circularSmoothLpCutoffApprox (φ : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  circularSmoothLpCutoff n z • φ z

private theorem circularSmoothLpCutoffApprox_eq_smul (φ : ℂ → ℂ) (n : ℕ) :
    circularSmoothLpCutoffApprox φ n = (circularSmoothLpCutoff n : ℂ → ℝ) • φ := by
  funext z
  rfl

/-- Smoothness is preserved by the actual smooth scalar cutoff. -/
theorem contDiff_circularSmoothLpCutoffApprox {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (circularSmoothLpCutoffApprox φ n) := by
  rw [circularSmoothLpCutoffApprox_eq_smul]
  exact (circularSmoothLpCutoff n).contDiff.smul hφ

/-- The cutoff output has compact support even for a noncompact input. -/
theorem hasCompactSupport_circularSmoothLpCutoffApprox (φ : ℂ → ℂ) (n : ℕ) :
    HasCompactSupport (circularSmoothLpCutoffApprox φ n) := by
  rw [circularSmoothLpCutoffApprox_eq_smul]
  exact (circularSmoothLpCutoff n).hasCompactSupport.smul_right

/-- The actual approximation retains every value in the indicated growing ball. -/
theorem circularSmoothLpCutoffApprox_eq {φ : ℂ → ℂ} {n : ℕ} {z : ℂ}
    (hz : ‖z‖ ≤ (n : ℝ)) : circularSmoothLpCutoffApprox φ n z = φ z := by
  have hχ : circularSmoothLpCutoff n z = 1 :=
    (circularSmoothLpCutoff n).one_of_mem_closedBall (by
      rw [mem_closedBall_zero_iff]
      change ‖z‖ ≤ (n : ℝ) + 1
      linarith)
  simp only [circularSmoothLpCutoffApprox, hχ, one_smul]

/-- Each fixed point eventually has exactly its original value. -/
theorem circularSmoothLpCutoffApprox_eventually_eq (φ : ℂ → ℂ) (z : ℂ) :
    (fun n : ℕ => circularSmoothLpCutoffApprox φ n z) =ᶠ[atTop] fun _ => φ z := by
  filter_upwards [eventually_gt_atTop ⌈‖z‖⌉₊] with n hn
  apply circularSmoothLpCutoffApprox_eq
  calc
    ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn.le

private theorem norm_circularSmoothLpCutoffApprox_sub_le_tail (φ : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    ‖circularSmoothLpCutoffApprox φ n z - φ z‖ ≤
      ‖(closedBall (0 : ℂ) (n : ℝ))ᶜ.indicator φ z‖ := by
  by_cases hz : z ∈ closedBall (0 : ℂ) (n : ℝ)
  · have hlocal := circularSmoothLpCutoffApprox_eq (φ := φ) (mem_closedBall_zero_iff.mp hz)
    rw [hlocal, sub_self, norm_zero, indicator_of_notMem (notMem_compl_iff.mpr hz)]
    simp only [norm_zero, le_refl]
  · rw [indicator_of_mem hz]
    have hχ0 : 0 ≤ circularSmoothLpCutoff n z := (circularSmoothLpCutoff n).nonneg
    have hχ1 : circularSmoothLpCutoff n z ≤ 1 := (circularSmoothLpCutoff n).le_one
    have heq : circularSmoothLpCutoffApprox φ n z - φ z =
        (circularSmoothLpCutoff n z - 1) • φ z := by
      simp only [circularSmoothLpCutoffApprox, sub_smul, one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hχ1)]
    calc
      -(circularSmoothLpCutoff n z - 1) * ‖φ z‖ ≤ 1 * ‖φ z‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ = ‖φ z‖ := one_mul _

/-- The cutoff error is dominated pointwise by the original function. -/
theorem norm_circularSmoothLpCutoffApprox_sub_le (φ : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    ‖circularSmoothLpCutoffApprox φ n z - φ z‖ ≤ ‖φ z‖ :=
  (norm_circularSmoothLpCutoffApprox_sub_le_tail φ n z).trans
    (norm_indicator_le_norm_self φ z)

/-- The same planar Lp seminorm of the cutoff error tends to zero. -/
theorem eLpNorm_circularSmoothLpCutoffApprox_sub_tendsto {p : ℝ} (hp : 0 < p)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hmem : MemLp φ (ENNReal.ofReal p) (volume : Measure ℂ)) :
    Tendsto (fun n : ℕ => eLpNorm (fun z => circularSmoothLpCutoffApprox φ n z - φ z)
      (ENNReal.ofReal p) (volume : Measure ℂ)) atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun z => circularSmoothLpCutoffApprox φ n z - φ z) (volume : Measure ℂ) :=
    ((contDiff_circularSmoothLpCutoffApprox hφ n).continuous.sub
      hφ.continuous).aestronglyMeasurable
  have hle (n : ℕ) :
      eLpNorm (fun z => circularSmoothLpCutoffApprox φ n z - φ z)
          (ENNReal.ofReal p) (volume : Measure ℂ) ≤
        eLpNorm ((closedBall (0 : ℂ) (n : ℝ))ᶜ.indicator φ)
          (ENNReal.ofReal p) (volume : Measure ℂ) :=
    eLpNorm_mono (hm n) (norm_circularSmoothLpCutoffApprox_sub_le_tail φ n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (LiZhongQC.eLpNorm_indicator_compl_closedBall_tendsto_zero hp hmem)
    (fun _ => zero_le) hle

/-- The actual compact smooth classes converge to the original class in the
same planar Lp, with no change of exponent or underlying measure. -/
theorem circularSmoothLpCutoffApprox_tendsto {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hmem : MemLp φ (ENNReal.ofReal p) (volume : Measure ℂ)) :
    Tendsto (fun n : ℕ =>
      ((contDiff_circularSmoothLpCutoffApprox hφ n).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_circularSmoothLpCutoffApprox φ n)).toLp
          (circularSmoothLpCutoffApprox φ n)) atTop (𝓝 (hmem.toLp φ)) := by
  have ha (n : ℕ) : MemLp (circularSmoothLpCutoffApprox φ n)
      (ENNReal.ofReal p) (volume : Measure ℂ) :=
    (contDiff_circularSmoothLpCutoffApprox hφ n).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_circularSmoothLpCutoffApprox φ n)
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (circularSmoothLpCutoffApprox φ) ha φ hmem).mpr
  exact eLpNorm_circularSmoothLpCutoffApprox_sub_tendsto hp hφ hmem

end LowDimensionalTopology.Geometry.Quasiconformal
