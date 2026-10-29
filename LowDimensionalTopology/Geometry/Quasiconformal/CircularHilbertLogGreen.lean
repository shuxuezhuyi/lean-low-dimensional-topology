/-
The cutoff and two-disc Green proof pattern is adapted from Wu Xiaobin's
Li-Zhong-QC-formalization, commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertLogKernel
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The compact-test Green identity for the real logarithmic kernel

A cutoff permits ordinary Green's formula on two concentric discs. Its
contribution cancels on their difference. The remaining inner circle
is bounded by a continuous test bound times `r * |log r|` and tends to
zero. Actual local integrability controls the omitted inner area integral.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ComplexConjugate ENNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem exists_realLogNorm_cutoff (a : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ χ : ℂ → ℂ, ContDiff ℝ 1 χ ∧
      (∀ z ∈ ball a (r / 2), χ z = 0) ∧
      (∀ z : ℂ, r ≤ ‖z - a‖ → χ z = 1) ∧
      ContDiff ℝ 1 (fun z => χ z * realLogNormKernel (z - a)) := by
  obtain ⟨χ, hχ, hzero, hone, _⟩ := LiZhongQC.exists_kernel_cutoff a hr
  refine ⟨χ, hχ, hzero, hone, ?_⟩
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = a
  · subst z
    have hevent : (fun v : ℂ => χ v * realLogNormKernel (v - a)) =ᶠ[𝓝 a]
        fun _ => (0 : ℂ) := by
      filter_upwards [ball_mem_nhds a (by positivity : (0 : ℝ) < r / 2)] with v hv
      rw [hzero v hv, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hevent
  · exact hχ.contDiffAt.mul (contDiffAt_shiftedRealLogNormKernel hz)

/-- Green's identity on an actual annulus, retaining its logarithmic
inner-circle integral and assuming the test vanishes on the outer circle. -/
theorem integral_ball_diff_realLogNorm_dz {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {a : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hvan : ∀ θ : ℝ, φ (circleMap a R θ) = 0) :
    (∫ z in ball a R \ ball a r,
      realLogNormKernel (z - a) * LiZhongQC.dz φ z +
        (1 / 2 : ℂ) * (φ z / (z - a))) =
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        (realLogNormKernel (circleMap a r θ - a) * φ (circleMap a r θ)) *
          conj (deriv (circleMap a r) θ)) / (2 * I) := by
  have hR : 0 < R := hr.trans hrR
  obtain ⟨χ, _, _, hχ1, hχK⟩ := exists_realLogNorm_cutoff a hr
  let u : ℂ → ℂ := fun z => (χ z * realLogNormKernel (z - a)) * φ z
  have hu : ContDiff ℝ 1 u := hχK.mul hφ
  have hG₁ := LiZhongQC.green_disc_dz_closedBall (c := a) hR hu.contDiffOn
  have hG₂ := LiZhongQC.green_disc_dz_closedBall (c := a) hr hu.contDiffOn
  have hc₁ (θ : ℝ) : u (circleMap a R θ) = 0 := by
    simp only [u, hvan θ, mul_zero]
  have hc₂ (θ : ℝ) : u (circleMap a r θ) =
      realLogNormKernel (circleMap a r θ - a) * φ (circleMap a r θ) := by
    have h₁ : r ≤ ‖circleMap a r θ - a‖ := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
    simp only [u, hχ1 _ h₁, one_mul]
  simp only [hc₁, zero_mul, intervalIntegral.integral_zero] at hG₁
  simp only [hc₂] at hG₂
  have hint : IntegrableOn (LiZhongQC.dz u) (ball a R) :=
    ((LiZhongQC.continuous_dz hu).continuousOn.integrableOn_compact
      (isCompact_closedBall a R)).mono_set ball_subset_closedBall
  have hsplit := setIntegral_sdiff (μ := volume) measurableSet_ball hint
    (ball_subset_ball hrR.le)
  have h₀ : ∫ z in ball a R, LiZhongQC.dz u z = 0 :=
    (mul_eq_zero.mp hG₁.symm).resolve_left (by simp)
  have heq : (∫ z in ball a R \ ball a r, LiZhongQC.dz u z) =
      ∫ z in ball a R \ ball a r,
        realLogNormKernel (z - a) * LiZhongQC.dz φ z +
          (1 / 2 : ℂ) * (φ z / (z - a)) := by
    apply setIntegral_congr_ae (measurableSet_ball.diff measurableSet_ball)
    have hsphere : ∀ᵐ z : ℂ, z ∉ sphere a r := by
      rw [ae_iff]
      exact measure_mono_null (fun z hz => not_not.mp hz)
        (Measure.addHaar_sphere (volume : Measure ℂ) a r)
    filter_upwards [hsphere] with z hzs hz
    have hge : r ≤ ‖z - a‖ := by
      have h := hz.2
      rwa [mem_ball, dist_eq_norm, not_lt] at h
    have hgt : r < ‖z - a‖ :=
      lt_of_le_of_ne hge fun h => hzs (by rw [mem_sphere, dist_eq_norm]; exact h.symm)
    have hne : z ≠ a := by
      intro h
      rw [h, sub_self, norm_zero] at hgt
      linarith
    have hevent : u =ᶠ[𝓝 z] fun v => realLogNormKernel (v - a) * φ v := by
      have hopen : IsOpen {v : ℂ | r < ‖v - a‖} :=
        isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
      filter_upwards [hopen.mem_nhds hgt] with v hv
      simp only [u, hχ1 v hv.le, one_mul]
    rw [show LiZhongQC.dz u z =
        LiZhongQC.dz (fun v => realLogNormKernel (v - a) * φ v) z by
          simp only [LiZhongQC.dz, hevent.fderiv_eq],
      LiZhongQC.dz_mul (differentiableAt_shiftedRealLogNormKernel hne)
        ((hφ.differentiable one_ne_zero) z), dz_shiftedRealLogNormKernel hne]
    field_simp [sub_ne_zero.mpr hne]
  rw [← heq, hsplit, h₀, zero_sub, hG₂,
    show (-2 * I * ∫ z in ball a r, LiZhongQC.dz u z) =
      -((∫ z in ball a r, LiZhongQC.dz u z) * (2 * I)) by ring,
    neg_div, mul_div_cancel_right₀ _ (by simp : (2 * I : ℂ) ≠ 0)]

/-- The actual logarithmic inner-circle term vanishes through positive
radii. No pointwise boundedness at the pole is used. -/
theorem tendsto_realLogNorm_innerBoundary {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (a : ℂ) :
    Tendsto (fun r : ℝ => ∫ θ in (0 : ℝ)..2 * Real.pi,
      (realLogNormKernel (circleMap a r θ - a) * φ (circleMap a r θ)) *
        conj (deriv (circleMap a r) θ)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hφ one_ne_zero
  let B : ℝ → ℂ := fun r => ∫ θ in (0 : ℝ)..2 * Real.pi,
    (realLogNormKernel (circleMap a r θ - a) * φ (circleMap a r θ)) *
      conj (deriv (circleMap a r) θ)
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ‖B r‖ ≤ (‖φ a‖ + (L : ℝ) * r) * (r * |Real.log r|) * (2 * Real.pi) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr₀ : 0 < r := hr
    have hφbound (θ : ℝ) : ‖φ (circleMap a r θ)‖ ≤ ‖φ a‖ + (L : ℝ) * r := by
      have hdist := hL.dist_le_mul (circleMap a r θ) a
      rw [dist_eq_norm, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
        abs_of_pos hr₀] at hdist
      calc
        ‖φ (circleMap a r θ)‖ ≤
            ‖φ (circleMap a r θ) - φ a‖ + ‖φ a‖ := by
          simpa only [sub_add_cancel] using
            norm_add_le (φ (circleMap a r θ) - φ a) (φ a)
        _ ≤ ‖φ a‖ + (L : ℝ) * r := by linarith
    have hnorm (θ : ℝ) :
        ‖(realLogNormKernel (circleMap a r θ - a) * φ (circleMap a r θ)) *
          conj (deriv (circleMap a r) θ)‖ ≤
            (‖φ a‖ + (L : ℝ) * r) * (r * |Real.log r|) := by
      rw [norm_mul, norm_mul, Complex.norm_conj, deriv_circleMap, norm_mul,
        Complex.norm_I, mul_one]
      simp only [realLogNormKernel, Complex.norm_real, Real.norm_eq_abs,
        circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr₀]
      calc
        |Real.log r| * ‖φ (circleMap a r θ)‖ * r ≤
            |Real.log r| * (‖φ a‖ + (L : ℝ) * r) * r := by
          gcongr
          exact hφbound θ
        _ = _ := by ring
    change ‖∫ θ in (0 : ℝ)..2 * Real.pi, _‖ ≤ _
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := (‖φ a‖ + (L : ℝ) * r) * (r * |Real.log r|))
      (fun θ _ => hnorm θ)).trans (le_of_eq ?_)
    rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hM : Tendsto (fun r : ℝ => ‖φ a‖ + (L : ℝ) * r)
      (𝓝[>] 0) (𝓝 ‖φ a‖) := by
    have h : Tendsto (fun r : ℝ => ‖φ a‖ + (L : ℝ) * r)
        (𝓝 (0 : ℝ)) (𝓝 (‖φ a‖ + (L : ℝ) * 0)) := by
      simpa only [id] using (tendsto_const_nhds (x := ‖φ a‖)).add
        ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (L : ℝ))
    simpa only [mul_zero, add_zero] using h.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun r : ℝ =>
      (‖φ a‖ + (L : ℝ) * r) * (r * |Real.log r|) * (2 * Real.pi))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (hM.mul tendsto_self_mul_abs_log_nhdsGT_zero).mul_const (2 * Real.pi)
  exact squeeze_zero_norm' hbound hlim

/-- The actual compact-test logarithmic Green identity, with its rational
integral and both pole limits justified separately. -/
theorem integral_dz_mul_realLogNormKernel {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (a : ℂ) :
    (∫ z : ℂ, LiZhongQC.dz φ z * realLogNormKernel (z - a)) =
      -(1 / 2 : ℂ) * (∫ z : ℂ, φ z / (z - a)) := by
  have hlog : Integrable
      (fun z : ℂ => realLogNormKernel (z - a) * LiZhongQC.dz φ z) volume := by
    simpa only [mul_comm] using
      integrable_compactTest_mul_realLogNormKernel (LiZhongQC.continuous_dz hφ)
        (LiZhongQC.dz_hasCompactSupport hc) a
  have hrat := integrable_compactTest_div_sub hφ.continuous hc a
  let G : ℂ → ℂ := fun z => realLogNormKernel (z - a) * LiZhongQC.dz φ z +
    (1 / 2 : ℂ) * (φ z / (z - a))
  have hGint : Integrable G volume := hlog.add (hrat.const_mul _)
  obtain ⟨M, hM⟩ := hc.isCompact.isBounded.subset_closedBall a
  let R : ℝ := max M 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hout (z : ℂ) (hz : R ≤ ‖z - a‖) : z ∉ tsupport φ := by
    intro hmem
    have h := mem_closedBall.mp (hM hmem)
    rw [dist_eq_norm] at h
    have hMR : M < R := by dsimp [R]; linarith [le_max_left M 0]
    linarith
  have hvan (z : ℂ) (hz : R ≤ ‖z - a‖) : φ z = 0 :=
    image_eq_zero_of_notMem_tsupport (hout z hz)
  have hdzvan (z : ℂ) (hz : R ≤ ‖z - a‖) : LiZhongQC.dz φ z = 0 := by
    simp [LiZhongQC.dz, fderiv_of_notMem_tsupport ℝ (hout z hz)]
  have hAfull : ∫ z in ball a R, G z = ∫ z, G z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [mem_ball, dist_eq_norm, not_lt] at hz
    simp only [G, hdzvan z hz, hvan z hz, mul_zero, zero_div, add_zero]
  let B : ℝ → ℂ := fun r => ∫ θ in (0 : ℝ)..2 * Real.pi,
    (realLogNormKernel (circleMap a r θ - a) * φ (circleMap a r θ)) *
      conj (deriv (circleMap a r) θ)
  have hkey (r : ℝ) (hr : 0 < r) (hrR : r < R) :
      (∫ z in ball a R \ ball a r, G z) = B r / (2 * I) := by
    exact integral_ball_diff_realLogNorm_dz hφ hr hrR fun θ => hvan _ (by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR])
  have hvol : Tendsto (fun r : ℝ => volume (ball a r)) (𝓝[>] 0) (𝓝 0) := by
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
  have hAlim : Tendsto (fun r : ℝ => ∫ z in ball a R \ ball a r, G z)
      (𝓝[>] 0) (𝓝 (∫ z, G z)) := by
    have h := (tendsto_const_nhds (x := ∫ z, G z)).sub hsmall
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr
    rw [setIntegral_sdiff measurableSet_ball hGint.integrableOn
      (ball_subset_ball hr.2.le), hAfull]
  have hBlim : Tendsto B (𝓝[>] 0) (𝓝 0) :=
    tendsto_realLogNorm_innerBoundary hφ hc a
  have hAzero : Tendsto (fun r : ℝ => ∫ z in ball a R \ ball a r, G z)
      (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => B r / (2 * I)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [zero_div] using hBlim.div_const (2 * I)
    apply h.congr'
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr
    exact (hkey r hr.1 hr.2).symm
  have hzero : (∫ z, G z) = 0 := tendsto_nhds_unique hAlim hAzero
  have hsplit : (∫ z, G z) =
      (∫ z : ℂ, realLogNormKernel (z - a) * LiZhongQC.dz φ z) +
        (1 / 2 : ℂ) * (∫ z : ℂ, φ z / (z - a)) := by
    rw [show G = fun z : ℂ => realLogNormKernel (z - a) * LiZhongQC.dz φ z +
      (1 / 2 : ℂ) * (φ z / (z - a)) from rfl,
      integral_add hlog (hrat.const_mul _), integral_const_mul]
  rw [hsplit] at hzero
  calc
    (∫ z : ℂ, LiZhongQC.dz φ z * realLogNormKernel (z - a)) =
        ∫ z : ℂ, realLogNormKernel (z - a) * LiZhongQC.dz φ z := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => mul_comm _ _
    _ = _ := by linear_combination hzero

end LowDimensionalTopology.Geometry.Quasiconformal
