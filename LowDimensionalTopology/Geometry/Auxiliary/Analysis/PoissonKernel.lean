/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Topology.Compactification.OnePoint.Basic


/-!
# Poisson kernels and fractional-linear covariance

The disc and half-plane Poisson kernels are related by boundary Cayley maps.
Their positive level sets are circles tangent to the ideal boundary, and
fractional-linear disc automorphisms transform the kernels by a derivative factor.
-/

@[expose] public section

open InnerProductSpace

namespace LowDimensionalTopology.Geometry.Auxiliary.Analysis


noncomputable def discPoissonKernel (z ζ : ℂ) : ℝ :=
  (1 - ‖z‖ ^ 2) / ‖z - ζ‖ ^ 2


theorem discPoissonKernel_eq_poissonKernel (z : ℂ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    discPoissonKernel z ζ = poissonKernel 0 z ζ := by
  simp only [discPoissonKernel, poissonKernel_def, sub_zero, hζ, one_pow,
    norm_sub_rev ζ z]


noncomputable def boundaryCayley (ζ z : ℂ) : ℂ := (ζ + z) / (ζ - z)


theorem discPoissonKernel_eq_re_boundaryCayley (z : ℂ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    discPoissonKernel z ζ = (boundaryCayley ζ z).re := by
  rw [discPoissonKernel_eq_poissonKernel z hζ]
  simpa [boundaryCayley, herglotzRieszKernel_def] using
    congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := z)) ζ


theorem unitBoundary_sub_ne_zero {z ζ : ℂ} (hz : ‖z‖ < 1) (hζ : ‖ζ‖ = 1) :
    ζ - z ≠ 0 := by
  intro heq
  have heq' : ζ = z := sub_eq_zero.mp heq
  have : ‖z‖ = 1 := heq' ▸ hζ
  exact (ne_of_lt hz) this


theorem discPoissonKernel_pos {z ζ : ℂ} (hz : ‖z‖ < 1) (hζ : ‖ζ‖ = 1) :
    0 < discPoissonKernel z ζ := by
  have hsq : ‖z‖ ^ 2 < (1 : ℝ) ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg z) zero_le_one).mpr hz
  have hden : 0 < ‖z - ζ‖ ^ 2 := by
    apply sq_pos_of_pos
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => unitBoundary_sub_ne_zero hz hζ (by simp [h])
  exact div_pos (by nlinarith) hden


theorem discPoissonKernel_boundary_formula_zero {z ζ : ℂ} (hz : ‖z‖ = 1) :
    discPoissonKernel z ζ = 0 := by
  simp [discPoissonKernel, hz]

theorem discPoissonKernel_totalized_at_pole (ζ : ℂ) : discPoissonKernel ζ ζ = 0 := by
  simp [discPoissonKernel]


theorem boundaryCayley_analyticAt {z ζ : ℂ} (hz : ‖z‖ < 1) (hζ : ‖ζ‖ = 1) :
    AnalyticAt ℂ (boundaryCayley ζ) z := by
  unfold boundaryCayley
  exact (analyticAt_const.add analyticAt_id).div
    (analyticAt_const.sub analyticAt_id) (unitBoundary_sub_ne_zero hz hζ)


theorem discPoissonKernel_harmonic {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    HarmonicOnNhd (fun z => discPoissonKernel z ζ) {z | ‖z‖ < 1} := by
  have heq : (fun z => discPoissonKernel z ζ) = fun z => (boundaryCayley ζ z).re :=
    funext fun z => discPoissonKernel_eq_re_boundaryCayley z hζ
  rw [heq]
  exact fun z hz => (boundaryCayley_analyticAt hz hζ).harmonicAt_re


noncomputable def halfPlanePoissonKernel (z : ℂ) (boundary : Option ℝ) : ℝ :=
  match boundary with
  | none => z.im
  | some ξ => z.im / ‖z - (ξ : ℂ)‖ ^ 2


theorem halfPlanePoissonKernel_infinity (z : ℂ) : halfPlanePoissonKernel z none = z.im := rfl


theorem halfPlanePoissonKernel_finite (z : ℂ) (ξ : ℝ) :
    halfPlanePoissonKernel z (some ξ) = z.im / ‖z - (ξ : ℂ)‖ ^ 2 := rfl


theorem halfPlanePoissonKernel_pos {z : ℂ} (hz : 0 < z.im) (boundary : Option ℝ) :
    0 < halfPlanePoissonKernel z boundary := by
  cases boundary with
  | none => exact hz
  | some ξ =>
    have hne : z - (ξ : ℂ) ≠ 0 := by
      intro heq
      have him : z.im = 0 := by simpa using congrArg Complex.im (sub_eq_zero.mp heq)
      exact (ne_of_gt hz) him
    exact div_pos hz (sq_pos_of_pos (norm_pos_iff.mpr hne))


theorem boundaryCayley_mapsTo {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    Set.MapsTo (boundaryCayley ζ) {z | ‖z‖ < 1} {w | 0 < w.re} := by
  intro z hz
  change 0 < (boundaryCayley ζ z).re
  rw [← discPoissonKernel_eq_re_boundaryCayley z hζ]
  exact discPoissonKernel_pos hz hζ


noncomputable def inverseBoundaryCayley (ζ w : ℂ) : ℂ := ζ * (w - 1) / (w + 1)

theorem rightHalfPlane_add_one_ne_zero {w : ℂ} (hw : 0 < w.re) : w + 1 ≠ 0 := by
  intro heq
  have hre := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
  linarith


theorem inverseBoundaryCayley_mem_disc {ζ w : ℂ} (hζ : ‖ζ‖ = 1) (hw : 0 < w.re) :
    ‖inverseBoundaryCayley ζ w‖ < 1 := by
  have hlt : ‖w - 1‖ < ‖w + 1‖ := by
    rw [← sq_lt_sq₀ (norm_nonneg (w - 1)) (norm_nonneg (w + 1))]
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    nlinarith
  rw [inverseBoundaryCayley, norm_div, norm_mul, hζ, one_mul]
  exact (div_lt_one (norm_pos_iff.mpr (rightHalfPlane_add_one_ne_zero hw))).mpr hlt


theorem boundaryCayley_inverse {ζ w : ℂ} (hζ : ‖ζ‖ = 1) (hw : 0 < w.re) :
    boundaryCayley ζ (inverseBoundaryCayley ζ w) = w := by
  have hz := inverseBoundaryCayley_mem_disc hζ hw
  unfold boundaryCayley
  apply (div_eq_iff (unitBoundary_sub_ne_zero hz hζ)).mpr
  unfold inverseBoundaryCayley
  field_simp [rightHalfPlane_add_one_ne_zero hw]
  ring


theorem boundaryCayley_injOn {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    Set.InjOn (boundaryCayley ζ) {z | ‖z‖ < 1} := by
  intro z₁ hz₁ z₂ hz₂ heq
  have hζ0 : ζ ≠ 0 := by
    intro h
    simp [h] at hζ
  have hcross := (div_eq_div_iff (unitBoundary_sub_ne_zero hz₁ hζ)
    (unitBoundary_sub_ne_zero hz₂ hζ)).mp heq
  have hzero : (2 * ζ) * (z₁ - z₂) = 0 := by
    linear_combination hcross
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (by norm_num) hζ0))


theorem boundaryCayley_bijOn {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    Set.BijOn (boundaryCayley ζ) {z | ‖z‖ < 1} {w | 0 < w.re} := by
  refine ⟨boundaryCayley_mapsTo hζ, boundaryCayley_injOn hζ, ?_⟩
  intro w hw
  exact ⟨inverseBoundaryCayley ζ w, inverseBoundaryCayley_mem_disc hζ hw,
    boundaryCayley_inverse hζ hw⟩

open scoped OnePoint


noncomputable def extendedBoundaryCayley (ζ : ℂ) (z : OnePoint ℂ) : OnePoint ℂ :=
  z.elim ((-1 : ℂ) : OnePoint ℂ)
    (fun w => if w = ζ then ∞ else (boundaryCayley ζ w : OnePoint ℂ))


theorem extendedBoundaryCayley_pole (ζ : ℂ) : extendedBoundaryCayley ζ ζ = ∞ := by
  simp [extendedBoundaryCayley]


theorem extendedBoundaryCayley_of_mem_disc {ζ z : ℂ} (hζ : ‖ζ‖ = 1) (hz : ‖z‖ < 1) :
    extendedBoundaryCayley ζ z = (boundaryCayley ζ z : OnePoint ℂ) := by
  have hne : z ≠ ζ := by
    intro h
    exact unitBoundary_sub_ne_zero hz hζ (by simp [h])
  simp [extendedBoundaryCayley, hne]


noncomputable def poissonLevelCenter (ζ : ℂ) (t : ℝ) : ℂ := (t / (t + 1)) • ζ


noncomputable def poissonLevelRadius (t : ℝ) : ℝ := 1 / (t + 1)

theorem poissonLevel_square_identity (z : ℂ) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    {t : ℝ} (ht : t + 1 ≠ 0) :
    (t + 1) ^ 2 * ‖z - poissonLevelCenter ζ t‖ ^ 2 =
      (t + 1) * (t * ‖z - ζ‖ ^ 2 + ‖z‖ ^ 2 - 1) + 1 := by
  simp only [poissonLevelCenter, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, sq_abs, hζ, one_pow, mul_one]
  field_simp [ht]
  ring


theorem discPoissonKernel_level_iff {ζ z : ℂ} (hζ : ‖ζ‖ = 1) (hz : ‖z‖ < 1)
    {t : ℝ} (ht : 0 < t) :
    discPoissonKernel z ζ = t ↔
      ‖z - poissonLevelCenter ζ t‖ = poissonLevelRadius t := by
  have ht1 : 0 < t + 1 := by linarith
  have hden : ‖z - ζ‖ ^ 2 ≠ 0 := by
    apply ne_of_gt
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    rw [sub_ne_zero]
    exact fun h => unitBoundary_sub_ne_zero hz hζ (by simp [h])
  have hid := poissonLevel_square_identity z hζ ht1.ne'
  have hr : (t + 1) ^ 2 * (1 / (t + 1)) ^ 2 = 1 := by
    field_simp
  constructor
  · intro h
    have hm : 1 - ‖z‖ ^ 2 = t * ‖z - ζ‖ ^ 2 :=
      (div_eq_iff hden).mp h
    have hzero : t * ‖z - ζ‖ ^ 2 + ‖z‖ ^ 2 - 1 = 0 := by linarith
    rw [hzero, mul_zero, zero_add] at hid
    unfold poissonLevelRadius
    apply (eq_div_iff ht1.ne').mpr
    apply (sq_eq_sq₀ (mul_nonneg (norm_nonneg _) ht1.le) zero_le_one).mp
    nlinarith [hid]
  · intro h
    change (1 - ‖z‖ ^ 2) / ‖z - ζ‖ ^ 2 = t
    apply (div_eq_iff hden).mpr
    change ‖z - poissonLevelCenter ζ t‖ = 1 / (t + 1) at h
    rw [h, hr] at hid
    have hmul : (t + 1) * (t * ‖z - ζ‖ ^ 2 + ‖z‖ ^ 2 - 1) = 0 := by linarith
    have hzero := (mul_eq_zero.mp hmul).resolve_left ht1.ne'
    linarith


theorem poissonLevelRadius_pos {t : ℝ} (ht : 0 < t) : 0 < poissonLevelRadius t := by
  unfold poissonLevelRadius
  positivity


theorem poissonLevelCenter_norm {ζ : ℂ} (hζ : ‖ζ‖ = 1) {t : ℝ} (ht : 0 < t) :
    ‖poissonLevelCenter ζ t‖ = t / (t + 1) := by
  rw [poissonLevelCenter, norm_smul, hζ, mul_one, Real.norm_eq_abs]
  exact abs_of_pos (div_pos ht (by linarith : 0 < t + 1))


theorem poissonLevelCenter_add_radius {ζ : ℂ} (hζ : ‖ζ‖ = 1) {t : ℝ} (ht : 0 < t) :
    ‖poissonLevelCenter ζ t‖ + poissonLevelRadius t = 1 := by
  rw [poissonLevelCenter_norm hζ ht, poissonLevelRadius]
  field_simp


theorem unitBoundary_mem_poissonLevelCircle {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    {t : ℝ} (ht : 0 < t) :
    ‖ζ - poissonLevelCenter ζ t‖ = poissonLevelRadius t := by
  have heq : 1 - t / (t + 1) = 1 / (t + 1) := by
    field_simp
    ring
  have hv : ζ - (t / (t + 1)) • ζ = (1 - t / (t + 1)) • ζ := by
    rw [sub_smul, one_smul]
  rw [poissonLevelCenter, hv, heq, norm_smul, hζ, mul_one, Real.norm_eq_abs]
  exact abs_of_pos (poissonLevelRadius_pos ht)


theorem discPoissonKernel_level_set {ζ : ℂ} (hζ : ‖ζ‖ = 1) {t : ℝ} (ht : 0 < t) :
    {z : ℂ | ‖z‖ < 1 ∧ discPoissonKernel z ζ = t} =
      {z : ℂ | ‖z‖ < 1} ∩ Metric.sphere (poissonLevelCenter ζ t) (poissonLevelRadius t) := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_sphere, dist_eq_norm]
  exact and_congr_right fun hz => discPoissonKernel_level_iff hζ hz ht


theorem poissonLevelCircle_inter_unitCircle {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    {t : ℝ} (ht : 0 < t) :
    Metric.sphere (poissonLevelCenter ζ t) (poissonLevelRadius t) ∩
      Metric.sphere (0 : ℂ) 1 = {ζ} := by
  have ht1 : 0 < t + 1 := by linarith
  have hr : (t + 1) ^ 2 * (1 / (t + 1)) ^ 2 = 1 := by field_simp
  ext z
  constructor
  · rintro ⟨hc, hu⟩
    have hc' : ‖z - poissonLevelCenter ζ t‖ = 1 / (t + 1) := by
      simpa only [Metric.mem_sphere, dist_eq_norm, poissonLevelRadius] using hc
    have hu' : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu
    have hid := poissonLevel_square_identity z hζ ht1.ne'
    rw [hc', hr, hu'] at hid
    have hmul : (t + 1) * (t * ‖z - ζ‖ ^ 2) = 0 := by nlinarith [hid]
    have hmul' := (mul_eq_zero.mp hmul).resolve_left ht1.ne'
    have hsquare := (mul_eq_zero.mp hmul').resolve_left ht.ne'
    exact Set.mem_singleton_iff.mpr
      (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsquare)))
  · intro h
    rcases Set.mem_singleton_iff.mp h with rfl
    constructor
    · simpa only [Metric.mem_sphere, dist_eq_norm] using
        unitBoundary_mem_poissonLevelCircle hζ ht
    · simpa only [Metric.mem_sphere, dist_zero_right] using hζ


theorem poissonLevelCircle_subset_closedDisc {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    {t : ℝ} (ht : 0 < t) :
    Metric.sphere (poissonLevelCenter ζ t) (poissonLevelRadius t) ⊆ {z : ℂ | ‖z‖ ≤ 1} := by
  intro z hz
  have hz' : ‖z - poissonLevelCenter ζ t‖ = poissonLevelRadius t := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using hz
  calc
    ‖z‖ = ‖(z - poissonLevelCenter ζ t) + poissonLevelCenter ζ t‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖z - poissonLevelCenter ζ t‖ + ‖poissonLevelCenter ζ t‖ := norm_add_le _ _
    _ = 1 := by rw [hz', add_comm, poissonLevelCenter_add_radius hζ ht]

open scoped Topology

noncomputable def poissonRadialSequence (ζ : ℂ) (n : ℕ) : ℂ :=
  ((n : ℝ) / ((n : ℝ) + 2)) • ζ

theorem poissonRadialSequence_eq_inverse (ζ : ℂ) (n : ℕ) :
    poissonRadialSequence ζ n = inverseBoundaryCayley ζ ((n : ℂ) + 1) := by
  unfold poissonRadialSequence inverseBoundaryCayley
  rw [Complex.real_smul]
  push_cast
  ring


theorem poissonRadialSequence_mem_disc {ζ : ℂ} (hζ : ‖ζ‖ = 1) (n : ℕ) :
    ‖poissonRadialSequence ζ n‖ < 1 := by
  rw [poissonRadialSequence_eq_inverse]
  apply inverseBoundaryCayley_mem_disc hζ
  simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
  positivity


theorem poissonRadialSequence_kernel {ζ : ℂ} (hζ : ‖ζ‖ = 1) (n : ℕ) :
    discPoissonKernel (poissonRadialSequence ζ n) ζ = (n : ℝ) + 1 := by
  have hn : 0 < ((n : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity
  rw [poissonRadialSequence_eq_inverse,
    discPoissonKernel_eq_re_boundaryCayley _ hζ, boundaryCayley_inverse hζ hn]
  simp


theorem poissonRadialSequence_tendsto (ζ : ℂ) :
    Filter.Tendsto (poissonRadialSequence ζ) Filter.atTop (𝓝 ζ) := by
  have hzero : Filter.Tendsto (fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 2))
      Filter.atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (Filter.tendsto_add_atTop_iff_nat 2).2
        (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (2 : ℝ))
  have hcoef : Filter.Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 2))
      Filter.atTop (𝓝 1) := by
    have h := (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 1)).sub hzero
    simp only [sub_zero] at h
    convert h using 1
    funext n
    field_simp
    ring
  change Filter.Tendsto (fun n : ℕ => ((n : ℝ) / ((n : ℝ) + 2)) • ζ)
    Filter.atTop (𝓝 ζ)
  simpa only [one_smul] using hcoef.smul_const ζ


theorem discPoissonKernel_unbounded_near_pole {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (U : Set ℂ) (hU : U ∈ 𝓝 ζ) (M : ℝ) :
    ∃ z ∈ U, ‖z‖ < 1 ∧ M < discPoissonKernel z ζ := by
  have hU' := (poissonRadialSequence_tendsto ζ).eventually_mem hU
  obtain ⟨N, hN⟩ := exists_nat_gt M
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop, M < (n : ℝ) + 1 := by
    apply Filter.eventually_atTop.mpr
    refine ⟨N, fun n hn => ?_⟩
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  obtain ⟨n, hnU, hnM⟩ := (hU'.and hlarge).exists
  refine ⟨poissonRadialSequence ζ n, hnU, poissonRadialSequence_mem_disc hζ n, ?_⟩
  simpa only [poissonRadialSequence_kernel hζ n] using hnM


noncomputable def fractionalLinearMap (a b c d z : ℂ) : ℂ := (a * z + b) / (c * z + d)

noncomputable def fractionalLinearDerivative (a b c d z : ℂ) : ℂ :=
  (a * d - b * c) / (c * z + d) ^ 2


theorem fractionalLinearMap_hasDerivAt (a b c d z : ℂ) (hz : c * z + d ≠ 0) :
    HasDerivAt (fractionalLinearMap a b c d) (fractionalLinearDerivative a b c d z) z := by
  unfold fractionalLinearMap fractionalLinearDerivative
  have h := (((hasDerivAt_id' z).const_mul a).add_const b).div
    (((hasDerivAt_id' z).const_mul c).add_const d) hz
  convert h using 1
  ring


theorem deriv_fractionalLinearMap (a b c d z : ℂ) (hz : c * z + d ≠ 0) :
    deriv (fractionalLinearMap a b c d) z = fractionalLinearDerivative a b c d z :=
  (fractionalLinearMap_hasDerivAt a b c d z hz).deriv


theorem fractionalLinearMap_sub (a b c d z w : ℂ)
    (hz : c * z + d ≠ 0) (hw : c * w + d ≠ 0) :
    fractionalLinearMap a b c d z - fractionalLinearMap a b c d w =
      (a * d - b * c) * (z - w) / ((c * z + d) * (c * w + d)) := by
  unfold fractionalLinearMap
  rw [div_sub_div _ _ hz hw]
  congr 1
  ring


theorem fractionalLinearMap_norm_sub_sq (a b c d z w : ℂ)
    (hz : c * z + d ≠ 0) (hw : c * w + d ≠ 0) :
    ‖fractionalLinearMap a b c d z - fractionalLinearMap a b c d w‖ ^ 2 =
      ‖z - w‖ ^ 2 * ‖deriv (fractionalLinearMap a b c d) z‖ *
        ‖deriv (fractionalLinearMap a b c d) w‖ := by
  rw [fractionalLinearMap_sub a b c d z w hz hw,
    deriv_fractionalLinearMap a b c d z hz, deriv_fractionalLinearMap a b c d w hw]
  simp only [fractionalLinearDerivative, norm_div, norm_mul, norm_pow]
  simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
  ring


noncomputable def discFractionalMap (a c z : ℂ) : ℂ :=
  fractionalLinearMap a ((starRingEnd ℂ) c) c ((starRingEnd ℂ) a) z

theorem discFractional_determinant {a c : ℂ} (hdet : Complex.normSq a - Complex.normSq c = 1) :
    a * (starRingEnd ℂ) a - (starRingEnd ℂ) c * c = 1 := by
  rw [mul_comm ((starRingEnd ℂ) c) c, Complex.mul_conj, Complex.mul_conj,
    ← Complex.ofReal_sub, hdet, Complex.ofReal_one]

theorem discFractional_norm_difference (z : ℂ) {a c : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1) :
    ‖c * z + (starRingEnd ℂ) a‖ ^ 2 - ‖a * z + (starRingEnd ℂ) c‖ ^ 2 =
      1 - ‖z‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_mul,
    Complex.normSq_conj, starRingEnd_self_apply]
  have hcross : (c * z * a).re = (a * z * c).re := by
    congr 1
    ring
  rw [hcross]
  have ha : Complex.normSq a = 1 + Complex.normSq c := by linarith
  rw [ha]
  ring

theorem discFractional_den_ne_zero {a c z : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1) (hz : ‖z‖ ≤ 1) :
    c * z + (starRingEnd ℂ) a ≠ 0 := by
  have hnorm : ‖c‖ < ‖a‖ := by
    apply (sq_lt_sq₀ (norm_nonneg c) (norm_nonneg a)).mp
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    linarith
  have hmul : ‖c * z‖ < ‖(starRingEnd ℂ) a‖ := by
    rw [norm_mul, Complex.norm_conj]
    calc
      ‖c‖ * ‖z‖ ≤ ‖c‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg c)
      _ < ‖a‖ := by simpa using hnorm
  intro heq
  have heq' : c * z = -(starRingEnd ℂ) a := eq_neg_of_add_eq_zero_left heq
  have hnorm' := congrArg norm heq'
  simp only [norm_neg] at hnorm'
  exact (ne_of_lt hmul) hnorm'


theorem discFractional_defect {a c z : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1)
    (hz : c * z + (starRingEnd ℂ) a ≠ 0) :
    1 - ‖discFractionalMap a c z‖ ^ 2 =
      (1 - ‖z‖ ^ 2) / ‖c * z + (starRingEnd ℂ) a‖ ^ 2 := by
  have hid := discFractional_norm_difference z hdet
  unfold discFractionalMap fractionalLinearMap
  rw [norm_div, div_pow]
  have hn : ‖c * z + (starRingEnd ℂ) a‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  rw [one_sub_div hn, hid]


theorem discFractional_deriv_norm {a c z : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1)
    (hz : c * z + (starRingEnd ℂ) a ≠ 0) :
    ‖deriv (discFractionalMap a c) z‖ = 1 / ‖c * z + (starRingEnd ℂ) a‖ ^ 2 := by
  unfold discFractionalMap
  rw [deriv_fractionalLinearMap _ _ _ _ _ hz, fractionalLinearDerivative,
    discFractional_determinant hdet, norm_div, norm_one, norm_pow]


theorem discFractional_defect_deriv {a c z : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1)
    (hz : c * z + (starRingEnd ℂ) a ≠ 0) :
    1 - ‖discFractionalMap a c z‖ ^ 2 =
      ‖deriv (discFractionalMap a c) z‖ * (1 - ‖z‖ ^ 2) := by
  rw [discFractional_defect hdet hz, discFractional_deriv_norm hdet hz]
  ring


theorem discFractional_maps_disc {a c z : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1) (hz : ‖z‖ < 1) :
    ‖discFractionalMap a c z‖ < 1 := by
  have hd := discFractional_den_ne_zero hdet hz.le
  have hsq : ‖z‖ ^ 2 < (1 : ℝ) ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg z) zero_le_one).mpr hz
  have hp : 0 < (1 - ‖z‖ ^ 2) / ‖c * z + (starRingEnd ℂ) a‖ ^ 2 :=
    div_pos (by nlinarith) (sq_pos_of_pos (norm_pos_iff.mpr hd))
  have hid := discFractional_defect hdet hd
  apply (sq_lt_sq₀ (norm_nonneg (discFractionalMap a c z)) zero_le_one).mp
  nlinarith [hid]


theorem discFractional_maps_circle {a c ζ : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1) (hζ : ‖ζ‖ = 1) :
    ‖discFractionalMap a c ζ‖ = 1 := by
  have hid := discFractional_defect hdet (discFractional_den_ne_zero hdet hζ.le)
  rw [hζ] at hid
  simp only [one_pow, sub_self, zero_div] at hid
  apply (sq_eq_sq₀ (norm_nonneg (discFractionalMap a c ζ)) zero_le_one).mp
  nlinarith [hid]

theorem discFractional_deriv_norm_pos {a c z : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1)
    (hz : c * z + (starRingEnd ℂ) a ≠ 0) :
    0 < ‖deriv (discFractionalMap a c) z‖ := by
  rw [discFractional_deriv_norm hdet hz]
  exact div_pos zero_lt_one (sq_pos_of_pos (norm_pos_iff.mpr hz))


theorem discPoissonKernel_covariance {a c z ζ : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1) (hz : ‖z‖ < 1) (hζ : ‖ζ‖ = 1) :
    discPoissonKernel (discFractionalMap a c z) (discFractionalMap a c ζ) *
        ‖deriv (discFractionalMap a c) ζ‖ = discPoissonKernel z ζ := by
  have hdz := discFractional_den_ne_zero hdet hz.le
  have hdζ := discFractional_den_ne_zero hdet hζ.le
  have hdz' := (discFractional_deriv_norm_pos hdet hdz).ne'
  have hdζ' := (discFractional_deriv_norm_pos hdet hdζ).ne'
  have hdifference := fractionalLinearMap_norm_sub_sq
    a ((starRingEnd ℂ) c) c ((starRingEnd ℂ) a) z ζ hdz hdζ
  change ‖discFractionalMap a c z - discFractionalMap a c ζ‖ ^ 2 =
    ‖z - ζ‖ ^ 2 * ‖deriv (discFractionalMap a c) z‖ *
      ‖deriv (discFractionalMap a c) ζ‖ at hdifference
  have hnorm : ‖z - ζ‖ ≠ 0 := by
    rw [norm_ne_zero_iff, sub_ne_zero]
    exact fun h => unitBoundary_sub_ne_zero hz hζ (by simp [h])
  unfold discPoissonKernel
  rw [discFractional_defect_deriv hdet hdz, hdifference]
  field_simp [hdz', hdζ', hnorm]

end LowDimensionalTopology.Geometry.Auxiliary.Analysis
