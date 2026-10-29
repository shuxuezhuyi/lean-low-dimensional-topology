/-
The cutoff, punctured-disc, and small-circle proof pattern is adapted from
Wu Xiaobin's Li-Zhong-QC-formalization, commit
1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertGreen
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertRenormalizedKernel
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertLpTails
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The compact-test Green limit for the circular transform

The inner boundary integral tends to zero by opposite angular cancellation.
The remaining inverse-norm area integral is genuinely integrable, so its
small-disc contribution tends to zero by absolute continuity of integration.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ComplexConjugate ENNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem tendsto_inverseNorm_innerBoundary {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (z : ℂ) :
    Tendsto (fun r : ℝ => ∫ θ in (0 : ℝ)..2 * Real.pi,
      (inverseNormKernel (circleMap z r θ - z) * φ (circleMap z r θ)) *
        conj (deriv (circleMap z r) θ)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hφ one_ne_zero
  let S : ℝ → ℂ := fun r => ∫ θ in (0 : ℝ)..2 * Real.pi,
    (inverseNormKernel (circleMap z r θ - z) * φ (circleMap z r θ)) *
      conj (deriv (circleMap z r) θ)
  have hK (r : ℝ) (hr : 0 < r) (θ : ℝ) :
      inverseNormKernel (circleMap z r θ - z) * conj (deriv (circleMap z r) θ) =
        -I * exp (((-θ : ℝ) : ℂ) * I) := by
    have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
    rw [inverseNormKernel, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr,
      deriv_circleMap, circleMap_zero, map_mul, map_mul, conj_ofReal, conj_I,
      ← exp_conj, map_mul, conj_ofReal, conj_I,
      show (θ : ℂ) * -I = ((-θ : ℝ) : ℂ) * I by push_cast; ring]
    field_simp
  have hexpc : Continuous fun θ : ℝ => -I * exp (((-θ : ℝ) : ℂ) * I) := by
    fun_prop
  have hKint : ∫ θ in (0 : ℝ)..2 * Real.pi,
      -I * exp (((-θ : ℝ) : ℂ) * I) = 0 := by
    have he (θ : ℝ) : exp (((-θ : ℝ) : ℂ) * I) = exp ((-I) * θ) := by
      congr 1
      push_cast
      ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex (by simp)]
    have he2 : exp ((-I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show (-I) * ((2 * Real.pi : ℝ) : ℂ) =
          ((-1 : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring]
      exact exp_int_mul_two_pi_mul_I (-1)
    rw [he2]
    simp
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ), ‖S r‖ ≤ (L : ℝ) * r * (2 * Real.pi) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : 0 < r := hr
    have hφcirc : Continuous fun θ => φ (circleMap z r θ) :=
      hφ.continuous.comp (continuous_circleMap z r)
    have hSr : S r = ∫ θ in (0 : ℝ)..2 * Real.pi,
        (φ (circleMap z r θ) - φ z) * (-I * exp (((-θ : ℝ) : ℂ) * I)) := by
      change (∫ θ in (0 : ℝ)..2 * Real.pi, _) = _
      calc
        _ = ∫ θ in (0 : ℝ)..2 * Real.pi,
            φ (circleMap z r θ) * (-I * exp (((-θ : ℝ) : ℂ) * I)) := by
          apply intervalIntegral.integral_congr
          intro θ _
          change (inverseNormKernel (circleMap z r θ - z) * φ (circleMap z r θ)) *
            conj (deriv (circleMap z r) θ) =
              φ (circleMap z r θ) * (-I * exp (((-θ : ℝ) : ℂ) * I))
          rw [show (inverseNormKernel (circleMap z r θ - z) * φ (circleMap z r θ)) *
              conj (deriv (circleMap z r) θ) = φ (circleMap z r θ) *
                (inverseNormKernel (circleMap z r θ - z) *
                  conj (deriv (circleMap z r) θ)) by ring, hK r hr0 θ]
        _ = ∫ θ in (0 : ℝ)..2 * Real.pi,
            ((φ (circleMap z r θ) - φ z) * (-I * exp (((-θ : ℝ) : ℂ) * I)) +
              φ z * (-I * exp (((-θ : ℝ) : ℂ) * I))) := by
          apply intervalIntegral.integral_congr
          intro θ _
          ring
        _ = _ := by
          have hc3 : Continuous fun θ : ℝ => (φ (circleMap z r θ) - φ z) *
              (-I * exp (((-θ : ℝ) : ℂ) * I)) :=
            (hφcirc.sub continuous_const).mul hexpc
          have hc4 : Continuous fun θ : ℝ => φ z * (-I * exp (((-θ : ℝ) : ℂ) * I)) :=
            continuous_const.mul hexpc
          rw [intervalIntegral.integral_add (hc3.intervalIntegrable _ _)
            (hc4.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
            hKint, mul_zero, add_zero]
    rw [hSr]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := (L : ℝ) * r)
      fun θ _ => ?_).trans (le_of_eq ?_)
    · rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      have h := hL.dist_le_mul (circleMap z r θ) z
      rwa [dist_eq_norm, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
        abs_of_pos hr0] at h
    · rw [sub_zero, abs_of_pos (by positivity)]
  have h' : Tendsto (fun r : ℝ => (L : ℝ) * r * (2 * Real.pi))
      (𝓝[>] 0) (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := (L : ℝ))).mul
      (tendsto_id (x := 𝓝 (0 : ℝ)))).mul_const (2 * Real.pi)
    simp only [id, mul_zero, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact squeeze_zero_norm' hbound h'

/-- The actual radial truncations converge to the inverse-norm potential
of the test's Wirtinger derivative. -/
theorem tendsto_circularHilbertTruncation_inverseNormPotential {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) (z : ℂ) :
    Tendsto (circularHilbertTruncation φ z) (𝓝[>] (0 : ℝ))
      (𝓝 ((1 / (Real.pi : ℂ)) * inverseNormPotential (LiZhongQC.dz φ) z)) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  let G : ℂ → ℂ := fun w => inverseNormKernel (w - z) * LiZhongQC.dz φ w
  have hGint : Integrable G (volume : Measure ℂ) := by
    have hi := integrable_inverseNormPotential (LiZhongQC.dz_contDiff hφ).continuous
      (LiZhongQC.dz_hasCompactSupport hc) z
    simpa only [G, mul_comm] using hi
  obtain ⟨M, hM⟩ := hc.isCompact.isBounded.subset_closedBall z
  let R : ℝ := max M 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hout (w : ℂ) (hw : R ≤ ‖w - z‖) : w ∉ tsupport φ := by
    intro hmem
    have h := mem_closedBall.mp (hM hmem)
    rw [dist_eq_norm] at h
    have hMR : M < R := by dsimp [R]; linarith [le_max_left M 0]
    linarith
  have hvan (w : ℂ) (hw : R ≤ ‖w - z‖) : φ w = 0 :=
    image_eq_zero_of_notMem_tsupport (hout w hw)
  have hdzvan (w : ℂ) (hw : R ≤ ‖w - z‖) : LiZhongQC.dz φ w = 0 := by
    simp [LiZhongQC.dz, fderiv_of_notMem_tsupport ℝ (hout w hw)]
  have hAfull : ∫ w in ball z R, G w = ∫ w, G w := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    rw [mem_ball, dist_eq_norm, not_lt] at hw
    simp only [G, hdzvan w hw, mul_zero]
  let B : ℝ → ℂ := fun r => ∫ θ in (0 : ℝ)..2 * Real.pi,
    (inverseNormKernel (circleMap z r θ - z) * φ (circleMap z r θ)) *
      conj (deriv (circleMap z r) θ)
  have hkey (r : ℝ) (hr : 0 < r) (hrR : r < R) :
      (∫ w in {w : ℂ | r < ‖w - z‖}, φ w / ((w - z) * (‖w - z‖ : ℂ))) =
        2 * (∫ w in ball z R \ ball z r, G w) - B r / I := by
    have hsub : LiZhongQC.annulusAt z r R ⊆ {w : ℂ | r < ‖w - z‖} :=
      fun w hw => hw.1
    have hmeas : MeasurableSet {w : ℂ | r < ‖w - z‖} :=
      measurableSet_lt measurable_const (measurable_id.sub_const z).norm
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hsub fun w hw => ?_,
      ← setIntegral_congr_set (LiZhongQC.ball_diff_ball_ae_eq_annulusAt z r R)]
    · have hBint : IntegrableOn
          (fun w : ℂ => φ w / ((w - z) * (‖w - z‖ : ℂ)))
          (ball z R \ ball z r) := by
        have hK : IsCompact (closedBall z R ∩ {w : ℂ | r ≤ ‖w - z‖}) :=
          (isCompact_closedBall z R).inter_right
            (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
        have hcont : ContinuousOn
            (fun w : ℂ => φ w / ((w - z) * (‖w - z‖ : ℂ)))
            (closedBall z R ∩ {w : ℂ | r ≤ ‖w - z‖}) := by
          refine hφ.continuous.continuousOn.div
            ((continuousOn_id.sub continuousOn_const).mul
              (Complex.continuous_ofReal.comp
                (continuous_id.sub continuous_const).norm).continuousOn) ?_
          intro w hw
          have hn : w - z ≠ 0 := by
            intro h
            have hw' : r ≤ ‖w - z‖ := hw.2
            rw [h, norm_zero] at hw'
            linarith
          exact mul_ne_zero hn (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hn))
        refine (hcont.integrableOn_compact hK).mono_set fun w hw =>
          ⟨ball_subset_closedBall hw.1, ?_⟩
        have h := hw.2
        rwa [mem_ball, dist_eq_norm, not_lt] at h
      have hid := integral_ball_diff_inverseNorm_dz hφ1 hr hrR fun θ => hvan _ (by
        rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR])
      have heq :
          (fun w : ℂ => inverseNormKernel (w - z) * LiZhongQC.dz φ w -
            (1 / 2 : ℂ) * φ w / ((w - z) * (‖w - z‖ : ℂ))) =
          fun w : ℂ => G w - (1 / 2 : ℂ) *
            (φ w / ((w - z) * (‖w - z‖ : ℂ))) := by
        funext w
        dsimp [G]
        ring
      rw [heq, integral_sub (hGint.integrableOn.mono_set sdiff_subset)
        (hBint.const_mul _), integral_const_mul] at hid
      change _ = B r / (2 * I) at hid
      linear_combination (-2 : ℂ) * hid
    · have hwR : R ≤ ‖w - z‖ := by
        by_contra h
        exact hw.2 ⟨hw.1, not_le.mp h⟩
      rw [hvan w hwR, zero_div]
  have hvol : Tendsto (fun r : ℝ => volume (ball z r)) (𝓝[>] 0) (𝓝 0) := by
    have hzero : Tendsto (fun r : ℝ => ENNReal.ofReal r)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
      simpa only [id, ENNReal.ofReal_zero] using
        (ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ)))).mono_left
          nhdsWithin_le_nhds
    have hpow := ((ENNReal.continuous_pow 2).tendsto (0 : ℝ≥0∞)).comp hzero
    have h := ENNReal.Tendsto.mul_const (b := (NNReal.pi : ℝ≥0∞)) hpow
      (Or.inr ENNReal.coe_ne_top)
    simpa only [Function.comp_def, Complex.volume_ball, id, ENNReal.ofReal_zero,
      zero_pow (by decide : 2 ≠ 0), zero_mul] using h
  have hsmall := hGint.tendsto_setIntegral_nhds_zero hvol
  have hAlim : Tendsto (fun r : ℝ => ∫ w in ball z R \ ball z r, G w)
      (𝓝[>] 0) (𝓝 (∫ w, G w)) := by
    have h := (tendsto_const_nhds (x := ∫ w, G w)).sub hsmall
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr
    rw [setIntegral_sdiff measurableSet_ball hGint.integrableOn
      (ball_subset_ball hr.2.le), hAfull]
  have hSlim : Tendsto B (𝓝[>] 0) (𝓝 0) :=
    tendsto_inverseNorm_innerBoundary hφ1 hc z
  have hlim := ((hAlim.const_mul (2 : ℂ)).sub (hSlim.div_const I)).const_mul
    (1 / (2 * (Real.pi : ℂ)))
  have hval : (1 / (2 * (Real.pi : ℂ))) * (2 * (∫ w, G w) - 0 / I) =
      (1 / (Real.pi : ℂ)) * inverseNormPotential (LiZhongQC.dz φ) z := by
    rw [inverseNormPotential_eq_integral]
    have hi : (∫ w, G w) = ∫ w : ℂ,
        LiZhongQC.dz φ w * inverseNormKernel (w - z) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun w => mul_comm _ _
    rw [hi, zero_div, sub_zero]
    ring
  rw [hval] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  rw [circularHilbertTruncation_eq_original_integral, hkey r hr.1 hr.2]

end LowDimensionalTopology.Geometry.Quasiconformal
