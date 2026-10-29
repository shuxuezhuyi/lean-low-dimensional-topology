/-
The smooth compact approximation API is due to Wu Xiaobin,
Li-Zhong-QC-formalization commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Unproved.Quasiconformal.RealDirectionalHilbert
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Uniqueness of the circular Hilbert extension in the same planar Lp

Smooth compact tests determine a bounded operator on the original planar Lp.
The actual truncation-and-mollification sequence is used, so the conclusion
applies to noncompact intermediate values as well.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Unproved.Quasiconformal

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

private def circularSmoothLpApprox (hp : 1 ≤ p)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) (n : ℕ) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) :=
  ((LiZhongQC.hilbertHApprox_contDiff hp (Lp.memLp f) n).continuous.memLp_of_hasCompactSupport
    (LiZhongQC.hilbertHApprox_hasCompactSupport (f : ℂ → ℂ) n)).toLp
      (LiZhongQC.hilbertHApprox (f : ℂ → ℂ) n)

private theorem circularSmoothLpApprox_tendsto (hp : 1 ≤ p)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) :
    Tendsto (circularSmoothLpApprox hp f) atTop (𝓝 f) := by
  have hmem (n : ℕ) :
      MemLp (LiZhongQC.hilbertHApprox (f : ℂ → ℂ) n)
        (ENNReal.ofReal p) (volume : Measure ℂ) :=
    (LiZhongQC.hilbertHApprox_contDiff hp (Lp.memLp f) n).continuous.memLp_of_hasCompactSupport
      (LiZhongQC.hilbertHApprox_hasCompactSupport (f : ℂ → ℂ) n)
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => LiZhongQC.hilbertHApprox (f : ℂ → ℂ) n) hmem
    (f : ℂ → ℂ) (Lp.memLp f)).2
      (LiZhongQC.hilbertHApprox_tendsto hp (Lp.memLp f))
  unfold circularSmoothLpApprox
  simpa only [Lp.toLp_coeFn] using ht

/-- Two bounded extensions agreeing with the circular transform on every smooth
compact test agree on the entire original planar Lp space. -/
theorem isCircularHilbertLpExtension_unique (hp : 1 ≤ p)
    {S₁ S₂ : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)}
    (h₁ : IsCircularHilbertLpExtension p S₁)
    (h₂ : IsCircularHilbertLpExtension p S₂) : S₁ = S₂ := by
  apply ContinuousLinearMap.ext
  intro f
  have heq (n : ℕ) : S₁ (circularSmoothLpApprox hp f n) =
      S₂ (circularSmoothLpApprox hp f n) := by
    apply Lp.ext
    exact (h₁ _ (LiZhongQC.hilbertHApprox_contDiff hp (Lp.memLp f) n)
      (LiZhongQC.hilbertHApprox_hasCompactSupport (f : ℂ → ℂ) n)).trans
        (h₂ _ (LiZhongQC.hilbertHApprox_contDiff hp (Lp.memLp f) n)
          (LiZhongQC.hilbertHApprox_hasCompactSupport (f : ℂ → ℂ) n)).symm
  have ht := circularSmoothLpApprox_tendsto hp f
  exact tendsto_nhds_unique
    (S₁.continuous.tendsto f |>.comp ht)
    ((S₂.continuous.tendsto f |>.comp ht).congr (fun n => (heq n).symm))

end LowDimensionalTopology.Geometry.Quasiconformal
