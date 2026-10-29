module

public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalLocalLpRegularity
public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalLowerPower
public import LowDimensionalTopology.Geometry.Quasiconformal.PlanarRadialWeightLp

/-!
# Absolute integrability of the original reciprocal area kernel

The prescribed exponent p>8 controls the true origin singularity by Holder's
inequality. On the complementary annulus the original canonical map has a
strictly nonzero compact image, and the existing Cauchy-kernel Lp theorem
also covers poles on the unit circle. Thus the parameter may lie on the
entire closed unit disc, including the normalization point one.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open scoped ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

theorem reciprocal_area_kernel_norm_le
    {z ζ A B : ℂ} {c α : ℝ} (hc : 0 < c) (hz : 0 < ‖z‖)
    (hA : c * ‖z‖ ^ α ≤ ‖A‖) (hd : 1 / 2 ≤ ‖1 - z * ζ‖) :
    ‖z * B / (A ^ 2 * (1 - z * ζ))‖ ≤
      (2 / c ^ 2) * ‖B‖ * ‖z‖ ^ (-(2 * α - 1)) := by
  let w : ℝ := ‖z‖ ^ (-(2 * α - 1))
  have hw : 0 ≤ w := Real.rpow_nonneg (norm_nonneg z) _
  have hpow : w * (‖z‖ ^ α) ^ 2 = ‖z‖ := by
    dsimp only [w]
    rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg z), ← Real.rpow_add hz]
    rw [show -(2 * α - 1) + α * 2 = 1 by ring, Real.rpow_one]
  have hAn : 0 < ‖A‖ := (mul_pos hc (Real.rpow_pos_of_pos hz α)).trans_le hA
  have hsq : c ^ 2 * (‖z‖ ^ α) ^ 2 ≤ ‖A‖ ^ 2 := by
    rw [← mul_pow]
    exact (sq_le_sq₀ (mul_nonneg hc.le (Real.rpow_nonneg (norm_nonneg z) _))
      (norm_nonneg A)).mpr hA
  have hden : 0 < ‖A‖ ^ 2 * ‖1 - z * ζ‖ :=
    mul_pos (sq_pos_of_pos hAn) (lt_of_lt_of_le (by norm_num) hd)
  have hlower : c ^ 2 * (‖z‖ ^ α) ^ 2 * (1 / 2) ≤ ‖A‖ ^ 2 * ‖1 - z * ζ‖ :=
    mul_le_mul hsq hd (by norm_num) (sq_nonneg _)
  let W : ℝ := (2 / c ^ 2) * ‖B‖ * w
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hcoef : (2 / c ^ 2) * c ^ 2 * (1 / 2) = 1 := by
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 hc.ne')]
    norm_num
  have hident : W * (c ^ 2 * (‖z‖ ^ α) ^ 2 * (1 / 2)) = ‖z‖ * ‖B‖ := by
    calc
      _ = ((2 / c ^ 2) * c ^ 2 * (1 / 2)) * ‖B‖ * (w * (‖z‖ ^ α) ^ 2) := by
        dsimp only [W]
        ring
      _ = _ := by rw [hcoef, one_mul, hpow, mul_comm]
  rw [norm_div, norm_mul, norm_mul, norm_pow]
  apply (div_le_iff₀ hden).mpr
  exact hident.symm.le.trans (mul_le_mul_of_nonneg_left hlower hW)

/-- The literal reciprocal area integrand of the SAME canonical map is
absolutely integrable for every parameter in the closed unit disc, including
one. The original full-plane coefficient has no support hypothesis. -/
theorem normalizedSolution_reciprocal_area_integrable
    {p : ℝ} (hp : 8 < p) (μ : MeasurableBeltramiBall)
    (hsmall : ‖μ.val‖ * smoothHilbertNorm p < 1)
    {ζ : ℂ} (hζ : ζ ∈ closedBall (0 : ℂ) 1) :
    IntegrableOn (fun z => z * dzbar (MeasurableBeltramiBall.normalizedSolution μ) z /
      ((MeasurableBeltramiBall.normalizedSolution μ z) ^ 2 * (1 - z * ζ)))
      (ball (0 : ℂ) 1) := by
  let F := MeasurableBeltramiBall.normalizedSolution μ
  let T : ℂ → ℂ := fun z => z * dzbar F z / ((F z) ^ 2 * (1 - z * ζ))
  let α : ℝ := p / (p - 2)
  let a : ℝ := 2 * α - 1
  let q : ℝ := p / (p - 1)
  have hp2 : 2 < p := lt_trans (by norm_num) hp
  have hp1 : 1 < p := lt_trans one_lt_two hp2
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hpq : p.HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent hp1).mpr rfl
  have ha : a = (p + 2) / (p - 2) := by
    calc
      a = (2 * p - (p - 2)) / (p - 2) := by
        dsimp only [a, α]
        rw [sub_div, div_self (sub_pos.mpr hp2).ne', mul_div_assoc]
      _ = _ := by congr 1; ring
  have haq : a * q < 2 := by
    rw [ha]
    dsimp only [q]
    rw [div_mul_div_comm, div_lt_iff₀ (mul_pos (sub_pos.mpr hp2) (sub_pos.mpr hp1))]
    nlinarith [mul_pos hp0 (sub_pos.mpr hp)]
  obtain ⟨c, hc, δ, hδ, hFbound⟩ := normalizedSolution_lower_power_near_zero hp2 μ hsmall
  let ρ : ℝ := min δ (1 / 2)
  have hρ : 0 < ρ := lt_min hδ (by norm_num)
  have hρδ : ρ ≤ δ := min_le_left _ _
  have hρhalf : ρ ≤ 1 / 2 := min_le_right _ _
  have hρ1 : ρ ≤ 1 := hρhalf.trans (by norm_num)
  obtain ⟨_, hbar, _⟩ := normalizedSolution_sameExponent_localLp hp2 μ hsmall
  have hsubρ : ball (0 : ℂ) ρ ⊆ closedBall 0 3 := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    have hn := mem_ball_zero_iff.mp hz
    linarith
  have hbarρ : MemLp (dzbar F) (ENNReal.ofReal p) (volume.restrict (ball 0 ρ)) :=
    hbar.mono_measure (Measure.restrict_mono hsubρ le_rfl)
  have hweight := integrable_norm_rpow_smul_ball hpq haq hbarρ
  have hTm : Measurable T :=
    (measurable_id.mul (measurable_dzbar F)).div
      ((F.continuous.measurable.pow_const (2 : ℕ)).mul
        (measurable_const.sub (measurable_id.mul_const ζ)))
  have hζn : ‖ζ‖ ≤ 1 := mem_closedBall_zero_iff.mp hζ
  have hinner : IntegrableOn T (ball (0 : ℂ) ρ) := by
    apply (hweight.norm.const_mul (2 / c ^ 2)).mono' hTm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball,
      (volume.restrict (ball (0 : ℂ) ρ)).ae_ne 0] with z hz hz0
    have hn : ‖z * ζ‖ ≤ 1 / 2 := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left hζn (norm_nonneg z)).trans
        (by simpa only [mul_one] using (mem_ball_zero_iff.mp hz).le.trans hρhalf)
    have hd : 1 / 2 ≤ ‖1 - z * ζ‖ := by
      have hh := norm_sub_norm_le (1 : ℂ) (z * ζ)
      rw [norm_one] at hh
      linarith
    have hlow : c * ‖z‖ ^ α ≤ ‖F z‖ :=
      hFbound z ((ball_subset_ball hρδ) hz)
    have hb := reciprocal_area_kernel_norm_le (B := dzbar F z) hc (norm_pos_iff.mpr hz0) hlow hd
    simpa only [T, a, norm_smul, Real.norm_of_nonneg
      (Real.rpow_nonneg (norm_nonneg z) (-a)), mul_assoc, mul_comm, mul_left_comm] using hb
  let K : Set ℂ := closedBall (0 : ℂ) 1 \ ball 0 ρ
  let b : ℂ → ℂ := fun z => z / (F z) ^ 2
  have hF0 : F 0 = 0 := (MeasurableBeltramiBall.normalizedSolution_spec μ).1.2.2.1
  have hFn : ∀ z ∈ K, F z ≠ 0 := by
    intro z hz heq
    have hz0 : z = 0 := F.injective (heq.trans hF0.symm)
    exact hz.2 (hz0 ▸ mem_ball_self hρ)
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).diff isOpen_ball
  have hb : ContinuousOn b K :=
    continuousOn_id.div (F.continuous.continuousOn.pow 2)
      (fun z hz => pow_ne_zero 2 (hFn z hz))
  obtain ⟨M, _, hM⟩ :=
    (hK.image_of_continuousOn hb).isBounded.exists_pos_norm_le
  let E : Set ℂ := ball (0 : ℂ) 1 \ ball 0 ρ
  have hEK : E ⊆ K := fun _ hz => ⟨ball_subset_closedBall hz.1, hz.2⟩
  have hB : ∀ z ∈ E, ‖b z‖ ≤ M := fun z hz => hM _ ⟨z, hEK hz, rfl⟩
  have hbar1 : MemLp (dzbar F) (ENNReal.ofReal p) (volume.restrict (ball 0 1)) :=
    hbar.mono_measure (Measure.restrict_mono
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))) le_rfl)
  have houter : IntegrableOn T E := by
    by_cases hz0 : ζ = 0
    · let : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) 1)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
      have hi1 : IntegrableOn (dzbar F) (ball (0 : ℂ) 1) :=
        MemLp.integrable (by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hp1.le) hbar1
      have hi : IntegrableOn (dzbar F) E := hi1.mono_set sdiff_subset
      apply (hi.norm.const_mul M).mono' hTm.aestronglyMeasurable.restrict
      filter_upwards [ae_restrict_mem (measurableSet_ball.diff measurableSet_ball)] with z hz
      have heq : T z = b z * dzbar F z := by
        simp only [T, b, hz0, mul_zero, sub_zero, mul_one, div_eq_mul_inv]
        ring
      rw [heq, norm_mul]
      exact mul_le_mul_of_nonneg_right (hB z hz) (norm_nonneg _)
    · have hloc : ∀ C ⊆ closedBall (0 : ℂ) 3, IsCompact C →
          MemLp (dzbar F) (ENNReal.ofReal p) (volume.restrict C) := by
        intro C hC _
        exact hbar.mono_measure (Measure.restrict_mono hC le_rfl)
      have hi := (pompeiu_area_integrable_of_local_memLp hp2
        (closedBall_subset_closedBall (by norm_num)) hloc (z₀ := ζ⁻¹)).mono_set (s := E) sdiff_subset
      apply (hi.norm.const_mul (M * ‖ζ⁻¹‖)).mono' hTm.aestronglyMeasurable.restrict
      filter_upwards [ae_restrict_mem (measurableSet_ball.diff measurableSet_ball)] with z hz
      have hfac : 1 - z * ζ = -ζ * (z - ζ⁻¹) := by
        rw [mul_sub, neg_mul, neg_mul, mul_inv_cancel₀ hz0]
        ring
      have heq : T z = b z * (-ζ⁻¹) * (dzbar F z / (z - ζ⁻¹)) := by
        dsimp only [T, b]
        rw [hfac]
        simp only [div_eq_mul_inv, mul_inv_rev, inv_neg]
        ring
      rw [heq, norm_mul, norm_mul, norm_neg]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hB z hz) (norm_nonneg _)) (norm_nonneg _)
  have hcover : ball (0 : ℂ) ρ ∪ E = ball 0 1 :=
    union_sdiff_cancel (ball_subset_ball hρ1)
  simpa only [hcover] using hinner.union houter

end LowDimensionalTopology.Geometry.Quasiconformal
