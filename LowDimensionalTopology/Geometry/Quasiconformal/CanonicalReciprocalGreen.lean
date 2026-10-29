module

public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalReciprocalAreaIntegrability
public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalReciprocalWeakKernel
public import LowDimensionalTopology.Geometry.Quasiconformal.WeakWirtingerPuncturedGreen

/-!
# The literal reciprocal area identity for the actual canonical map

The same original exponent supplies both absolute area integrability and
the inner-circle growth bound. The actual punctured weak chain is used
with its true continuous boundary trace; no Green identity or vanishing
inner-circle contribution is an input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

private theorem reciprocal_kernel_norm_le
    {z ζ A : ℂ} {c α : ℝ} (hc : 0 < c) (hz : 0 < ‖z‖)
    (hA : c * ‖z‖ ^ α ≤ ‖A‖) (hd : 1 / 2 ≤ ‖1 - z * ζ‖) :
    ‖z / (A * (1 - z * ζ))‖ ≤ (2 / c) * ‖z‖ ^ (1 - α) := by
  let w : ℝ := ‖z‖ ^ (1 - α)
  have hw : 0 ≤ w := Real.rpow_nonneg (norm_nonneg z) _
  have hpow : w * ‖z‖ ^ α = ‖z‖ := by
    dsimp only [w]
    rw [← Real.rpow_add hz, sub_add_cancel, Real.rpow_one]
  have hAn : 0 < ‖A‖ := (mul_pos hc (Real.rpow_pos_of_pos hz α)).trans_le hA
  have hden : 0 < ‖A‖ * ‖1 - z * ζ‖ :=
    mul_pos hAn (lt_of_lt_of_le (by norm_num) hd)
  have hlower : c * ‖z‖ ^ α * (1 / 2) ≤ ‖A‖ * ‖1 - z * ζ‖ :=
    mul_le_mul hA hd (by norm_num) (norm_nonneg A)
  have hcoef : (2 / c) * c * (1 / 2) = 1 := by
    rw [div_mul_cancel₀ _ hc.ne']
    norm_num
  have hident : ((2 / c) * w) * (c * ‖z‖ ^ α * (1 / 2)) = ‖z‖ := by
    calc
      _ = ((2 / c) * c * (1 / 2)) * (w * ‖z‖ ^ α) := by ring
      _ = _ := by rw [hcoef, one_mul, hpow]
  rw [norm_div, norm_mul]
  apply (div_le_iff₀ hden).mpr
  exact hident.symm.le.trans (mul_le_mul_of_nonneg_left hlower
    (mul_nonneg (div_nonneg (by norm_num) hc.le) hw))

/-- The original continuous reciprocal kernel has the literal clockwise-free
Green identity with its true antiholomorphic area term. The coefficient is
arbitrary on the whole plane, and the prescribed p and C_p are unchanged. -/
theorem normalizedSolution_reciprocal_green
    {p : ℝ} (hp : 8 < p) (μ : MeasurableBeltramiBall)
    (hsmall : ‖μ.val‖ * smoothHilbertNorm p < 1)
    {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) :
    CircleIntegrable (canonicalReciprocalKernel μ ζ) 0 1 ∧
      (∮ z in C(0, 1), canonicalReciprocalKernel μ ζ z) =
        -(2 * I) * ∫ z in ball (0 : ℂ) 1,
          z * dzbar (MeasurableBeltramiBall.normalizedSolution μ) z /
            ((MeasurableBeltramiBall.normalizedSolution μ z) ^ 2 * (1 - z * ζ)) := by
  let F := MeasurableBeltramiBall.normalizedSolution μ
  let T : ℂ → ℂ := fun z => z * dzbar F z / ((F z) ^ 2 * (1 - z * ζ))
  let α : ℝ := p / (p - 2)
  have hp2 : 2 < p := lt_trans (by norm_num) hp
  have hα : α < 2 := by
    dsimp only [α]
    rw [div_lt_iff₀ (sub_pos.mpr hp2)]
    linarith
  obtain ⟨r, hr, g, h, hf, hw, hbar⟩ := canonicalReciprocalKernel_weak μ hζ
  let V : Set ℂ := ball (0 : ℂ) r \ {0}
  have hV : IsOpen V := isOpen_ball.sdiff isClosed_singleton
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 r := by
    intro z hz
    rw [mem_ball_zero_iff]
    exact (mem_closedBall_zero_iff.mp hz).trans_lt hr
  have hiT : IntegrableOn T (ball (0 : ℂ) 1) :=
    normalizedSolution_reciprocal_area_integrable hp μ hsmall (ball_subset_closedBall hζ)
  have hglobal : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ V → h z = -T z := by
    apply (ae_restrict_iff' hV.measurableSet).mp
    filter_upwards [hbar] with z hz
    simpa only [T, F, neg_div] using hz
  have hAE : h =ᵐ[volume.restrict (ball (0 : ℂ) 1)] (fun z => -T z) := by
    filter_upwards [ae_restrict_of_ae hglobal, ae_restrict_mem measurableSet_ball,
      (volume.restrict (ball (0 : ℂ) 1)).ae_ne 0] with z hz hzin hz0
    exact hz ⟨hsub (ball_subset_closedBall hzin), by simpa only [mem_singleton_iff] using hz0⟩
  have hi : IntegrableOn h (ball (0 : ℂ) 1) := hiT.neg.congr hAE.symm
  obtain ⟨c, hc, δ, hδ, hbound⟩ := normalizedSolution_lower_power_near_zero hp2 μ hsmall
  let ρ : ℝ := min δ (1 / 2)
  have hρ : 0 < ρ := lt_min hδ (by norm_num)
  have hζn : ‖ζ‖ ≤ 1 := (mem_ball_zero_iff.mp hζ).le
  have hu : ∀ z ∈ ball (0 : ℂ) ρ \ {0},
      ‖canonicalReciprocalKernel μ ζ z‖ ≤ (2 / c) * ‖z‖ ^ (1 - α) := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa only [mem_singleton_iff] using hz.2
    have hprod : ‖z * ζ‖ ≤ 1 / 2 := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left hζn (norm_nonneg z)).trans
        (by simpa only [mul_one] using
          (mem_ball_zero_iff.mp hz.1).le.trans (min_le_right δ (1 / 2)))
    have hd : 1 / 2 ≤ ‖1 - z * ζ‖ := by
      have hh := norm_sub_norm_le (1 : ℂ) (z * ζ)
      rw [norm_one] at hh
      linarith
    have hl : c * ‖z‖ ^ α ≤ ‖F z‖ :=
      hbound z ((ball_subset_ball (min_le_left δ (1 / 2))) hz.1)
    exact reciprocal_kernel_norm_le hc (norm_pos_iff.mpr hz0) hl hd
  obtain ⟨hcircle, hgreen⟩ := green_of_distributional_wirtinger_puncture
    isOpen_ball hf hw zero_lt_one hsub hi (by linarith : -1 < 1 - α) hρ hu
  refine ⟨hcircle, ?_⟩
  rw [hgreen, integral_congr_ae hAE, integral_neg]
  ring

end LowDimensionalTopology.Geometry.Quasiconformal
