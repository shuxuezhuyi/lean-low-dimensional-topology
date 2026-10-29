/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.NormalizedSolutionContinuity
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S27_TeichmullerExistence

/-!
# Continuity of the original symmetric normalized solution at zero

Actual upper-half-plane coefficients with bounds tending to zero have their
original symmetric normalized maps tending locally uniformly to the identity.
The proof encodes the actual symmetric extension in the existing measurable
coefficient ball and identifies its canonical solution by actual uniqueness.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory Topology

namespace LowDimensionalTopology.Geometry.Teichmuller

open LiZhongQC

/-- Shrinking genuine coefficient bounds force the same original symmetric
solutions to converge to the identity on every compact subset of the plane. -/
theorem symmetricSolution_tendstoLocallyUniformly_zero
    (μ : ℕ → ℂ → ℂ) (k : ℕ → ℝ)
    (hk₀ : ∀ n, 0 ≤ k n) (hk : ∀ n, k n < 1)
    (hμ : ∀ n, IsBeltramiCoeff (μ n) upperHalf (k n))
    (hzero : Tendsto k atTop (𝓝 0)) :
    TendstoLocallyUniformly (fun n z => s27u_fSym (μ n) z) (id : ℂ → ℂ) atTop := by
  have hsym (n : ℕ) : IsBeltramiCoeff (s27u_symExt (μ n)) univ (k n) :=
    s27u_b_s_beltrami (hμ n)
  let B : ℕ → MeasurableBeltramiBall := fun n =>
    MeasurableBeltramiBall.ofCoefficient (hk₀ n) (hk n) (hsym n)
  have hAE (n : ℕ) : ((B n).val : ℂ → ℂ) =ᵐ[volume] s27u_symExt (μ n) :=
    MeasurableBeltramiBall.ofCoefficient_coe_ae (hk₀ n) (hk n) (hsym n)
  have hbound (n : ℕ) : ‖(B n).val‖ ≤ k n := by
    apply lpInfinity_norm_le_of_ae_bound _ (hk₀ n)
    have hb : ∀ᵐ z ∂volume, ‖s27u_symExt (μ n) z‖ ≤ k n := by
      simpa only [Measure.restrict_univ] using (hsym n).2
    filter_upwards [hAE n, hb] with z hz hzb
    rw [hz]
    exact hzb
  have hnorm : Tendsto (fun n => ‖(B n).val‖) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun _ => norm_nonneg _) hbound hzero
  have hB : Tendsto (fun n => (B n).val) atTop (𝓝 (0 : MeasurableBeltramiSpace)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hmaps (n : ℕ) :
      (fun z => MeasurableBeltramiBall.normalizedSolution (B n) z) = s27u_fSym (μ n) := by
    apply (s27u_sym_spec (hk₀ n) (hk n) (hμ n)).2.2.2
    exact MeasurableBeltramiBall.normalizedSolution_isNormalized_of_ae (B n) (hAE n)
  exact (Quasiconformal.normalizedSolution_tendstoLocallyUniformly_zero B hB).congr
    (fun n z => congrFun (hmaps n) z)

end LowDimensionalTopology.Geometry.Teichmuller
