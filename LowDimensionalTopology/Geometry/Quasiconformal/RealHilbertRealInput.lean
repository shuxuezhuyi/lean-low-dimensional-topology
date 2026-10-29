module

public import LowDimensionalTopology.Geometry.Quasiconformal.RealCauchySliceLp
public import LowDimensionalTopology.Geometry.Quasiconformal.RealCauchyBoundary
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Positivity

/-!
# Real-input Hilbert estimates by Fatou

The actual Cauchy slices at the positive heights1/(n+1) converge pointwise
to the original principal-value transform. Native lower semicontinuity of
eLpNorm gives its finite Lp bound with coefficient D(p)^(-1/2). No Riesz
estimate, boundary convergence, measurability or operator extension is
assumed. The original complex-test reduction is a subsequent calculation.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The actual real compact C1 test has the Riesz bound, with its original
complex-codomain principal value and explicit MemLp before any toReal use. -/
theorem realHilbert_ofReal_memLp_and_eLpNorm_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) {p : ℝ} (hp : 2 ≤ p) :
    MemLp (realHilbertTransform (fun x => (φ x : ℂ))) (ENNReal.ofReal p) volume ∧
      eLpNorm (realHilbertTransform (fun x => (φ x : ℂ))) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ((rieszBookDenominator p) ^ (-(1 / 2 : ℝ))) *
          eLpNorm φ (ENNReal.ofReal p) volume := by
  let η : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let f (n : ℕ) (ξ : ℝ) : ℂ :=
    ((realCauchyFunction φ ((ξ : ℂ) + (η n : ℂ) * I)).re : ℂ)
  let g : ℝ → ℂ := realHilbertTransform (fun x => (φ x : ℂ))
  let C : ℝ≥0∞ := ENNReal.ofReal ((rieszBookDenominator p) ^ (-(1 / 2 : ℝ))) *
    eLpNorm φ (ENNReal.ofReal p) volume
  have hη (n : ℕ) : 0 < η n := by dsimp [η]; positivity
  have hηlim : Tendsto η atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · simpa only [η] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)))
    · exact Eventually.of_forall fun n => hη n
  have hreal (n : ℕ) :
      MemLp (fun ξ : ℝ => (realCauchyFunction φ ((ξ : ℂ) + (η n : ℂ) * I)).re)
        (ENNReal.ofReal p) volume := by
    have hF := realCauchyFunction_slice_memLp hφ.continuous hc hp (hη n)
    simpa only [RCLike.re_eq_complex_re] using! hF.re
  have hf (n : ℕ) : MemLp (f n) (ENNReal.ofReal p) volume := by
    simpa only [f] using! (hreal n).ofReal (K := ℂ)
  have hbound (n : ℕ) : eLpNorm (f n) (ENNReal.ofReal p) volume ≤ C := by
    have heq : eLpNorm (f n) (ENNReal.ofReal p) volume =
        eLpNorm (fun ξ : ℝ => (realCauchyFunction φ ((ξ : ℂ) + (η n : ℂ) * I)).re)
          (ENNReal.ofReal p) volume := by
      apply eLpNorm_congr_norm_ae (hf n).aestronglyMeasurable (hreal n).aestronglyMeasurable
      exact Eventually.of_forall fun ξ => Complex.norm_real _
    rw [heq]
    exact realCauchyFunction_re_slice_eLpNorm_le hφ.continuous hc hp (hη n)
  have hpoint (ξ : ℝ) : Tendsto (fun n : ℕ => f n ξ) atTop (𝓝 (g ξ)) :=
    (tendsto_realCauchy_re_ofReal hφ hc ξ).comp hηlim
  have hpointAE : ∀ᵐ ξ : ℝ ∂volume, Tendsto (fun n : ℕ => f n ξ) atTop (𝓝 (g ξ)) :=
    Eventually.of_forall hpoint
  have hgae : AEStronglyMeasurable g volume :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hf n).aestronglyMeasurable) hpointAE
  have hnorm : eLpNorm g (ENNReal.ofReal p) volume ≤ C :=
    MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
      (Eventually.of_forall hbound) (fun n => (hf n).aestronglyMeasurable) hgae hpointAE
  have hφp : MemLp φ (ENNReal.ofReal p) volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hC : C < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφp.eLpNorm_lt_top
  have hg : MemLp g (ENNReal.ofReal p) volume := by
    rw [memLp_iff]
    exact hnorm.trans_lt hC
  exact ⟨hg, hnorm⟩

/-- The same actual real-input estimate in the original finite real norm. -/
theorem realHilbert_ofReal_norm_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) {p : ℝ} (hp : 2 ≤ p) :
    (eLpNorm (realHilbertTransform (fun x => (φ x : ℂ))) (ENNReal.ofReal p) volume).toReal ≤
      (rieszBookDenominator p) ^ (-(1 / 2 : ℝ)) *
        (eLpNorm φ (ENNReal.ofReal p) volume).toReal := by
  have hbound := (realHilbert_ofReal_memLp_and_eLpNorm_le hφ hc hp).2
  have hφp : MemLp φ (ENNReal.ofReal p) volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hRhs : ENNReal.ofReal ((rieszBookDenominator p) ^ (-(1 / 2 : ℝ))) *
      eLpNorm φ (ENNReal.ofReal p) volume < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφp.eLpNorm_lt_top
  have hB : 0 ≤ (rieszBookDenominator p) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (rieszBookDenominator_bounds hp).1.le _
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB] using
    ENNReal.toReal_mono hRhs.ne hbound

end LowDimensionalTopology.Geometry.Quasiconformal
