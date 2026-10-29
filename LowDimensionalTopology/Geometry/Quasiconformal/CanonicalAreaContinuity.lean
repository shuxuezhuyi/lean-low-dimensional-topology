module

public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalReciprocalAreaIntegrability
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Continuity of the original canonical area integrals

The ordinary Cauchy integral is normalized explicitly before applying its
Lp estimate. For the reciprocal kernel, the true origin singularity has a
parameter-independent integrable majorant. On the complementary annulus,
the same prescribed Lp derivative gives a continuous Cauchy integral even
when its pole lies on the unit circle.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open scoped ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

/-- The literal ordinary Cauchy integral is continuous for the actual Lp
input. Its normalization is exactly the fixed source operator's factor. -/
theorem continuous_cauchyIntegral_of_memLp {p : ℝ} (hp : 2 < p)
    {w : ℂ → ℂ} (hw : MemLp w (ENNReal.ofReal p)) :
    Continuous (fun ζ => ∫ z, w z / (z - ζ)) := by
  obtain ⟨M, hM⟩ := LiZhongQC.lemma11_2 hp
  have hα : 0 < (p - 2) / p := div_pos (by linarith) (by linarith)
  have hT : Continuous (cauchyT w) := by
    apply continuous_iff_continuousAt.mpr
    intro ζ
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hpow : ContinuousAt
        (fun η : ℂ => M * (eLpNorm w (ENNReal.ofReal p)).toReal *
          ‖η - ζ‖ ^ ((p - 2) / p)) ζ :=
      continuousAt_const.mul
        ((continuousAt_id.sub continuousAt_const).norm.rpow_const (Or.inr hα.le))
    have hlim : Tendsto
        (fun η : ℂ => M * (eLpNorm w (ENNReal.ofReal p)).toReal *
          ‖η - ζ‖ ^ ((p - 2) / p)) (𝓝 ζ) (𝓝 0) := by
      simpa only [ContinuousAt, sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] using hpow
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with η hη
    simpa only [dist_eq_norm] using (hM w hw η ζ).trans_lt hη
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply ((continuous_const : Continuous (fun _ : ℂ => -(Real.pi : ℂ))).mul hT).congr
  intro ζ
  change -(Real.pi : ℂ) * (-(1 / (Real.pi : ℂ)) * _) = _
  rw [← mul_assoc]
  simp [hπ]

/-- The ordinary area term of the original canonical map. -/
def canonicalFirstArea (μ : MeasurableBeltramiBall) (ζ : ℂ) : ℂ :=
  ∫ z in ball (0 : ℂ) 1,
    dzbar (MeasurableBeltramiBall.normalizedSolution μ) z / (z - ζ)

/-- The actual same-p derivative makes the first area term continuous on
the whole plane, without a support condition on the original coefficient. -/
theorem continuous_canonicalFirstArea {p : ℝ} (hp : 2 < p)
    (μ : MeasurableBeltramiBall) (hsmall : ‖μ.val‖ * smoothHilbertNorm p < 1) :
    Continuous (canonicalFirstArea μ) := by
  let F := MeasurableBeltramiBall.normalizedSolution μ
  let w : ℂ → ℂ := (ball (0 : ℂ) 1).indicator (dzbar F)
  obtain ⟨_, hbar, _⟩ := normalizedSolution_sameExponent_localLp hp μ hsmall
  have hw : MemLp w (ENNReal.ofReal p) := by
    apply (memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet).mpr
    exact hbar.mono_measure (Measure.restrict_mono
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))) le_rfl)
  have heq : canonicalFirstArea μ = fun ζ => ∫ z, w z / (z - ζ) := by
    funext ζ
    rw [canonicalFirstArea, ← integral_indicator measurableSet_ball]
    congr 1
    funext z
    by_cases hz : z ∈ ball (0 : ℂ) 1 <;> simp [w, F, hz]
  rw [heq]
  exact continuous_cauchyIntegral_of_memLp hp hw

/-- The literal reciprocal area term, with the original canonical map and
its actual antiholomorphic derivative. -/
def canonicalReciprocalArea (μ : MeasurableBeltramiBall) (ζ : ℂ) : ℂ :=
  ∫ z in ball (0 : ℂ) 1,
    z * dzbar (MeasurableBeltramiBall.normalizedSolution μ) z /
      ((MeasurableBeltramiBall.normalizedSolution μ z) ^ 2 * (1 - z * ζ))

/-- Continuity on the entire closed parameter disc, including one. The same
prescribed exponent and norm bound control the original arbitrary coefficient. -/
theorem continuousOn_canonicalReciprocalArea {p : ℝ} (hp : 8 < p)
    (μ : MeasurableBeltramiBall) (hsmall : ‖μ.val‖ * smoothHilbertNorm p < 1) :
    ContinuousOn (canonicalReciprocalArea μ) (closedBall (0 : ℂ) 1) := by
  let F := MeasurableBeltramiBall.normalizedSolution μ
  let T : ℂ → ℂ → ℂ := fun ζ z => z * dzbar F z / ((F z) ^ 2 * (1 - z * ζ))
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
  have hbar1 : MemLp (dzbar F) (ENNReal.ofReal p) (volume.restrict (ball 0 1)) :=
    hbar.mono_measure (Measure.restrict_mono
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))) le_rfl)
  have hbarρ : MemLp (dzbar F) (ENNReal.ofReal p) (volume.restrict (ball 0 ρ)) :=
    hbar1.mono_measure (Measure.restrict_mono (ball_subset_ball hρ1) le_rfl)
  have hweight := integrable_norm_rpow_smul_ball hpq haq hbarρ
  have hTm (ζ : ℂ) : Measurable (T ζ) :=
    (measurable_id.mul (measurable_dzbar F)).div
      ((F.continuous.measurable.pow_const (2 : ℕ)).mul
        (measurable_const.sub (measurable_id.mul_const ζ)))
  have hF0 : F 0 = 0 := (MeasurableBeltramiBall.normalizedSolution_spec μ).1.2.2.1
  have hFn (z : ℂ) (hz : z ≠ 0) : F z ≠ 0 := fun heq =>
    hz (F.injective (heq.trans hF0.symm))
  have hden : ∀ z ∈ ball (0 : ℂ) ρ, ∀ ζ ∈ closedBall (0 : ℂ) 1,
      1 / 2 ≤ ‖1 - z * ζ‖ := by
    intro z hz ζ hζ
    have hn : ‖z * ζ‖ ≤ 1 / 2 := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hζ) (norm_nonneg z)).trans
        (by simpa only [mul_one] using (mem_ball_zero_iff.mp hz).le.trans hρhalf)
    have hh := norm_sub_norm_le (1 : ℂ) (z * ζ)
    rw [norm_one] at hh
    linarith
  have hinner : ContinuousOn (fun ζ => ∫ z in ball (0 : ℂ) ρ, T ζ z)
      (closedBall (0 : ℂ) 1) := by
    apply continuousOn_of_dominated
      (bound := fun z => (2 / c ^ 2) * ‖‖z‖ ^ (-a) • dzbar F z‖)
      (fun ζ _ => (hTm ζ).aestronglyMeasurable.restrict) ?_
      (hweight.norm.const_mul (2 / c ^ 2)) ?_
    · intro ζ hζ
      filter_upwards [ae_restrict_mem measurableSet_ball,
        (volume.restrict (ball (0 : ℂ) ρ)).ae_ne 0] with z hz hz0
      have hlow : c * ‖z‖ ^ α ≤ ‖F z‖ := hFbound z ((ball_subset_ball hρδ) hz)
      have hb := reciprocal_area_kernel_norm_le (B := dzbar F z) hc
        (norm_pos_iff.mpr hz0) hlow (hden z hz ζ hζ)
      simpa only [T, a, norm_smul, Real.norm_of_nonneg
        (Real.rpow_nonneg (norm_nonneg z) (-a)), mul_assoc, mul_comm, mul_left_comm] using hb
    · filter_upwards [ae_restrict_mem measurableSet_ball,
        (volume.restrict (ball (0 : ℂ) ρ)).ae_ne 0] with z hz hz0
      refine continuousOn_const.div
        (continuousOn_const.mul (continuousOn_const.sub
          (continuousOn_const.mul continuousOn_id))) ?_
      intro ζ hζ
      exact mul_ne_zero (pow_ne_zero 2 (hFn z hz0))
        (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hden z hz ζ hζ)))
  let K : Set ℂ := closedBall (0 : ℂ) 1 \ ball 0 ρ
  let b : ℂ → ℂ := fun z => z / (F z) ^ 2
  have hKn : ∀ z ∈ K, F z ≠ 0 := by
    intro z hz
    apply hFn
    intro hz0
    exact hz.2 (hz0 ▸ mem_ball_self hρ)
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).diff isOpen_ball
  have hb : ContinuousOn b K := continuousOn_id.div (F.continuous.continuousOn.pow 2)
    (fun z hz => pow_ne_zero 2 (hKn z hz))
  obtain ⟨M, hMpos, hM⟩ := (hK.image_of_continuousOn hb).isBounded.exists_pos_norm_le
  let E : Set ℂ := ball (0 : ℂ) 1 \ ball 0 ρ
  have hE : MeasurableSet E := measurableSet_ball.diff measurableSet_ball
  have hEK : E ⊆ K := fun _ hz => ⟨ball_subset_closedBall hz.1, hz.2⟩
  have hB : ∀ z ∈ E, ‖b z‖ ≤ M := fun z hz => hM _ ⟨z, hEK hz, rfl⟩
  have hbm : Measurable b := measurable_id.div (F.continuous.measurable.pow_const (2 : ℕ))
  let w : ℂ → ℂ := E.indicator (fun z => b z * dzbar F z)
  have hw : MemLp w (ENNReal.ofReal p) := by
    apply (memLp_indicator_iff_restrict hE.nullMeasurableSet).mpr
    apply (hbar1.mono_measure (Measure.restrict_mono sdiff_subset le_rfl)).of_le_mul
      (hbm.mul (measurable_dzbar F)).aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem hE] with z hz
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hB z hz) (norm_nonneg _)
  have hJ : Continuous (fun η => ∫ z, w z / (z - η)) :=
    continuous_cauchyIntegral_of_memLp hp2 hw
  have hrewrite (ζ z : ℂ) : T ζ z = b z * dzbar F z / (1 - z * ζ) := by
    dsimp only [T, b]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have houter0 : ContinuousAt (fun ζ => ∫ z in E, T ζ z) 0 := by
    let : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have hi1 : IntegrableOn (dzbar F) (ball (0 : ℂ) 1) :=
      MemLp.integrable (by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hp1.le) hbar1
    have hi : IntegrableOn (dzbar F) E := hi1.mono_set sdiff_subset
    apply continuousAt_of_dominated
      (bound := fun z => (2 * M) * ‖dzbar F z‖)
      (Eventually.of_forall fun ζ => (hTm ζ).aestronglyMeasurable.restrict) ?_
      (hi.norm.const_mul (2 * M)) ?_
    · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with ζ hζ
      filter_upwards [ae_restrict_mem hE] with z hz
      have hn : ‖z * ζ‖ ≤ 1 / 2 := by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hζ).le (norm_nonneg z)).trans
          (by nlinarith [mem_ball_zero_iff.mp hz.1])
      have hd : 1 / 2 ≤ ‖1 - z * ζ‖ := by
        have hh := norm_sub_norm_le (1 : ℂ) (z * ζ)
        rw [norm_one] at hh
        linarith
      rw [hrewrite, norm_div, norm_mul]
      apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hd)).mpr
      calc
        ‖b z‖ * ‖dzbar F z‖ ≤ M * ‖dzbar F z‖ :=
          mul_le_mul_of_nonneg_right (hB z hz) (norm_nonneg _)
        _ = ((2 * M) * ‖dzbar F z‖) * (1 / 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
    · filter_upwards [ae_restrict_mem hE] with z hz
      apply continuousAt_const.div
        (continuousAt_const.mul (continuousAt_const.sub
          (continuousAt_const.mul continuousAt_id)))
      simpa only [Pi.mul_apply, Pi.sub_apply, id_eq, mul_zero, sub_zero, mul_one] using
        pow_ne_zero 2 (hKn z (hEK hz))
  have heq : ∀ ζ : ℂ, ζ ≠ 0 → (∫ z in E, T ζ z) =
      -ζ⁻¹ * (∫ z, w z / (z - ζ⁻¹)) := by
    intro ζ hζ
    calc
      _ = ∫ z in E, -ζ⁻¹ * (b z * dzbar F z / (z - ζ⁻¹)) := by
        apply setIntegral_congr_fun hE
        intro z _
        have hfac : 1 - z * ζ = -ζ * (z - ζ⁻¹) := by
          rw [mul_sub, neg_mul, neg_mul, mul_inv_cancel₀ hζ]
          ring
        rw [hrewrite, hfac]
        simp only [div_eq_mul_inv, mul_inv_rev, inv_neg]
        ring
      _ = -ζ⁻¹ * (∫ z in E, b z * dzbar F z / (z - ζ⁻¹)) := integral_const_mul _ _
      _ = _ := by
        congr 1
        rw [← integral_indicator hE]
        congr 1
        funext z
        by_cases hz : z ∈ E <;> simp [w, hz]
  have houter : ContinuousOn (fun ζ => ∫ z in E, T ζ z) (closedBall (0 : ℂ) 1) := by
    intro ζ _
    by_cases hζ : ζ = 0
    · subst ζ
      exact houter0.continuousWithinAt
    · have hi : ContinuousAt (fun η : ℂ => η⁻¹) ζ := continuousAt_id.inv₀ hζ
      have hcont := hi.neg.mul (hJ.continuousAt.comp hi)
      apply (hcont.congr_of_eventuallyEq ?_).continuousWithinAt
      filter_upwards [isOpen_ne.mem_nhds hζ] with η hη
      exact heq η hη
  apply (hinner.add houter).congr
  intro ζ hζ
  have hi := normalizedSolution_reciprocal_area_integrable hp μ hsmall hζ
  have hcover : ball (0 : ℂ) ρ ∪ E = ball 0 1 :=
    union_sdiff_cancel (ball_subset_ball hρ1)
  change (∫ z in ball (0 : ℂ) 1, T ζ z) = _
  rw [← hcover]
  exact setIntegral_union (disjoint_left.mpr fun z hz hzE => hzE.2 hz) hE
    (hi.mono_set (ball_subset_ball hρ1)) (hi.mono_set sdiff_subset)

end LowDimensionalTopology.Geometry.Quasiconformal
