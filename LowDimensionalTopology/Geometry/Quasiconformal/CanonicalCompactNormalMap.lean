module

public import LowDimensionalTopology.Geometry.Quasiconformal.NormalBeltramiQuasiconformal

/-!
# Same-exponent normal maps underlying actual compact canonical maps

The normal solution is genuinely derived from the original coefficient and
prescribed exponent. Its affine normalization is the actual selected
canonical homeomorphism; no representation or normalizing value is supplied.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open scoped ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

/-- The actual compact canonical map is the affine normalization of a
genuine normal Lp solution at the same originally prescribed exponent. -/
theorem canonicalCompact_exists_normalLp_normalization
    {p : ℝ} (hp : 2 < p) (μ : MeasurableBeltramiBall)
    (hsupp : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ ball 0 4 → μ.val z = 0)
    (hsmall : ‖μ.val‖ * smoothHilbertNorm p < 1) :
    ∃ N : ℂ → ℂ, IsNormalLpSolution (μ.val : ℂ → ℂ) N p ∧ N 1 ≠ 0 ∧
      ∀ z : ℂ, MeasurableBeltramiBall.normalizedSolution μ z = N z / N 1 := by
  let k := ‖μ.val‖
  let ν : ℂ → ℂ := (ball (0 : ℂ) 4).indicator (μ.val : ℂ → ℂ)
  have hk0 : 0 ≤ k := norm_nonneg _
  have hk1 : k < 1 := MeasurableBeltramiBall.norm_lt_one μ
  have hp1 : 1 < p := lt_trans one_lt_two hp
  have hμ : IsBeltramiCoeff (μ.val : ℂ → ℂ) univ k :=
    MeasurableBeltramiSpace.isBeltramiCoeff μ.val
  have hνae : ν =ᵐ[volume] (μ.val : ℂ → ℂ) := by
    filter_upwards [hsupp] with z hz
    change (ball (0 : ℂ) 4).indicator (μ.val : ℂ → ℂ) z = μ.val z
    by_cases hzin : z ∈ ball (0 : ℂ) 4
    · exact indicator_of_mem hzin _
    · rw [indicator_of_notMem hzin, hz hzin]
  have hν : IsBeltramiCoeff ν univ k := (planar_isBeltramiCoeff_congr_ae hνae).mpr hμ
  have hνsupp : ∀ z : ℂ, 4 < ‖z‖ → ν z = 0 := by
    intro z hz
    exact indicator_of_notMem (by simpa only [mem_ball_zero_iff] using (not_lt_of_ge hz.le)) _
  have hcomp : HasCompactEssentialSupport (μ.val : ℂ → ℂ) := by
    refine ⟨closedBall 0 4, isCompact_closedBall _ _, ?_⟩
    filter_upwards [hsupp] with z hz
    exact fun hzc => hz (fun hzb => hzc (ball_subset_closedBall hzb))
  have hμLp := measurableBeltrami_memLp_of_compactEssentialSupport μ.val hcomp (ENNReal.ofReal p)
  have hνLp : MemLp ν (ENNReal.ofReal p) (volume : Measure ℂ) :=
    MemLp.ae_eq hνae.symm hμLp
  have hsmall' : k * hilbertNorm p < 1 := by
    simpa only [smoothHilbertNorm_eq_hilbertNorm hp1] using hsmall
  obtain ⟨ω, hω, hfixed, _⟩ := eq12_1_solution hk0 hν hp hsmall' hνLp
  let N : ℂ → ℂ := fun z => z + normalizedCauchyPotential ω z
  have hN : IsNormalLpSolution (μ.val : ℂ → ℂ) N p :=
    (isNormalLpSolution_congr_coefficient_ae hνae).mp
      (normalLpSolution_of_fixedPoint hp hω hfixed)
  have hG := MeasurableBeltramiBall.normalizedSolution_isNormalized_of_ae μ hνae.symm
  obtain ⟨ha, hrepr⟩ := ahC_normalized_eq hk0 hk1 hν hνsupp hp hsmall' hω hfixed hG
  have hP := normalizedCauchyPotential_eq_cauchyT_sub_of_fixedPoint hp hω hνsupp hfixed
  have hN1 : N 1 = 1 + cauchyT ω 1 - cauchyT ω 0 := by
    dsimp only [N]
    rw [hP]
    dsimp only
    ring
  have hne : N 1 ≠ 0 := by rw [hN1]; exact ha
  refine ⟨N, hN, hne, ?_⟩
  intro z
  rw [hrepr z, hN1]
  apply congrArg (fun a : ℂ => a / (1 + cauchyT ω 1 - cauchyT ω 0))
  dsimp only [N]
  rw [hP]
  dsimp only
  ring

end LowDimensionalTopology.Geometry.Quasiconformal
