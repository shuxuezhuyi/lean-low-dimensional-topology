module

public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalCompactNormalMap
public import LowDimensionalTopology.Geometry.Quasiconformal.NormalBeltramiInverseEstimates
public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalCutoffInverseLocalBound
public import LowDimensionalTopology.Geometry.Quasiconformal.HolderPowerLowerBound

/-!
# The original canonical map has a same-exponent lower power near zero

The compact normal solution supplies the inverse Holder estimate at the
prescribed p. The actual conformal cutoff factor transfers that estimate
back to the original full-plane canonical map. Only the internally produced
coefficient has compact support.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open scoped ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

/-- The actual compact canonical normalization preserves the original
inverse Holder exponent, including the zero coefficient. -/
theorem canonicalCompact_lower_power_near_zero
    {p : ℝ} (hp : 2 < p) (μ : MeasurableBeltramiBall)
    (hsupp : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ ball 0 4 → μ.val z = 0)
    (hsmall : ‖μ.val‖ * smoothHilbertNorm p < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball (0 : ℂ) δ,
      c * ‖z‖ ^ (p / (p - 2)) ≤ ‖MeasurableBeltramiBall.normalizedSolution μ z‖ := by
  obtain ⟨N, hN, hN1, hrepr⟩ := canonicalCompact_exists_normalLp_normalization hp μ hsupp hsmall
  have hcomp : HasCompactEssentialSupport (μ.val : ℂ → ℂ) := by
    refine ⟨closedBall 0 4, isCompact_closedBall _ _, ?_⟩
    filter_upwards [hsupp] with z hz
    exact fun hzc => hz (fun hzb => hzc (ball_subset_closedBall hzb))
  obtain ⟨Kp, hKp, hsep⟩ := exists_normalLpSolution_lower_separation_constant hp
  let β : ℝ := 1 - 2 / p
  let A : ℝ := Kp / (1 - ‖μ.val‖ * smoothHilbertNorm p) ^ (1 + 2 / p) *
    (eLpNorm (μ.val : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal
  have hp0 : 0 < p := lt_trans zero_lt_two hp
  have hβ : 0 < β := sub_pos.mpr ((div_lt_one hp0).mpr hp)
  have hβ1 : β ≤ 1 := by
    dsimp only [β]
    exact sub_le_self _ (div_nonneg zero_le_two hp0.le)
  have hd : 0 < 1 - ‖μ.val‖ * smoothHilbertNorm p := sub_pos.mpr hsmall
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hα : 1 / β = p / (p - 2) := by
    have hb : β = (p - 2) / p := by
      dsimp only [β]
      rw [sub_div, div_self hp0.ne']
    rw [hb, one_div_div]
  have hnear : N ⁻¹' ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) :=
    hN.1.continuousAt.preimage_mem_nhds (by
      simpa only [hN.2.1] using ball_mem_nhds (0 : ℂ) zero_lt_one)
  obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhds_iff.mp hnear
  let c : ℝ := (A + 1) ^ (-(1 / β))
  have hc : 0 < c := Real.rpow_pos_of_pos (by linarith : 0 < A + 1) _
  refine ⟨c / ‖N 1‖, div_pos hc (norm_pos_iff.mpr hN1), δ, hδ, ?_⟩
  intro z hz
  have hs : ‖z‖ ≤ A * ‖N z‖ ^ β + ‖N z‖ := by
    simpa only [sub_zero, hN.2.1, A, β] using
      hsep μ.val ‖μ.val‖ N ⟨norm_nonneg _, MeasurableBeltramiBall.norm_lt_one μ⟩
        le_rfl hcomp hsmall hN z 0
  have hr1 : ‖N z‖ ≤ 1 := (mem_ball_zero_iff.mp (hδN hz)).le
  have hbound := (power_lower_bound_of_holder_upper_bound hβ hβ1 hA
    (norm_nonneg (N z)) hr1 (norm_nonneg z) hs).2
  calc
    (c / ‖N 1‖) * ‖z‖ ^ (p / (p - 2)) = (c * ‖z‖ ^ (1 / β)) / ‖N 1‖ := by
      rw [hα]
      ring
    _ ≤ ‖N z‖ / ‖N 1‖ := div_le_div_of_nonneg_right hbound (norm_nonneg _)
    _ = ‖MeasurableBeltramiBall.normalizedSolution μ z‖ := by rw [hrepr z, norm_div]

/-- Every original full-plane canonical map has the lower power required
by the same originally prescribed p. The coefficient need not have compact
support; only the internal cutoff does. -/
theorem normalizedSolution_lower_power_near_zero
    {p : ℝ} (hp : 2 < p) (μ : MeasurableBeltramiBall)
    (hsmall : ‖μ.val‖ * smoothHilbertNorm p < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball (0 : ℂ) δ,
      c * ‖z‖ ^ (p / (p - 2)) ≤ ‖MeasurableBeltramiBall.normalizedSolution μ z‖ := by
  let ν := canonicalBallFourCutoff μ
  let F := MeasurableBeltramiBall.normalizedSolution μ
  have hCp : 0 ≤ smoothHilbertNorm p := by
    rw [smoothHilbertNorm_eq_hilbertNorm (lt_trans one_lt_two hp)]
    exact hilbertNorm_nonneg p
  have hνsmall : ‖ν.val‖ * smoothHilbertNorm p < 1 :=
    (mul_le_mul_of_nonneg_right
      (canonicalCoefficientCutoff_norm_le μ _ measurableSet_ball) hCp).trans_lt hsmall
  have hsupp : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ ball 0 4 → ν.val z = 0 := by
    filter_upwards [canonicalCoefficientCutoff_coe_ae μ (ball 0 4) measurableSet_ball]
      with z hz
    intro hzin
    rw [hz, indicator_of_notMem hzin]
  obtain ⟨c, hc, δ, hδ, hG⟩ := canonicalCompact_lower_power_near_zero hp ν hsupp hνsmall
  obtain ⟨L, hL, η, hη, hFG⟩ := canonical_cutoff_norm_le_original_near_zero μ
  have hL1 : 0 < L + 1 := by linarith
  refine ⟨c / (L + 1), div_pos hc hL1, min δ η, lt_min hδ hη, ?_⟩
  intro z hz
  have hzδ : z ∈ ball (0 : ℂ) δ := (ball_subset_ball (min_le_left _ _)) hz
  have hzη : z ∈ ball (0 : ℂ) η := (ball_subset_ball (min_le_right _ _)) hz
  have hbound : c * ‖z‖ ^ (p / (p - 2)) ≤ (L + 1) * ‖F z‖ :=
    (hG z hzδ).trans ((hFG z hzη).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)))
  calc
    (c / (L + 1)) * ‖z‖ ^ (p / (p - 2)) = (c * ‖z‖ ^ (p / (p - 2))) / (L + 1) := by ring
    _ ≤ ((L + 1) * ‖F z‖) / (L + 1) := div_le_div_of_nonneg_right hbound hL1.le
    _ = ‖F z‖ := mul_div_cancel_left₀ _ hL1.ne'

end LowDimensionalTopology.Geometry.Quasiconformal
