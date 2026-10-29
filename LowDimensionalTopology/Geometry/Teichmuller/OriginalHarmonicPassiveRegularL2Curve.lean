module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicPassiveRegularL2Input
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite Cauchy control of the actual regular-kernel L2 curve

A fixed parameter circle supplies the same actual regular input, its
measurable linear coefficient, and the genuine L2 difference-quotient
remainder. The source kernel and its diagonal value remain unchanged.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter MeasureTheory Topology Metric
open scoped ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami LiZhongQC

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

open scoped ENNReal

private theorem regularInput_holomorphic_and_jointly_measurable
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : ℍ) :
    ∃ E : ℝ, 0 < E ∧
      (∀ y : ℂ, DifferentiableOn ℂ
        (fun t => canonicalPassiveRegularKernelInput R p q x t y) (ball 0 E)) ∧
      (∀ t : ℂ, ‖t‖ < E → Measurable (canonicalPassiveRegularKernelInput R p q x t)) ∧
      Measurable (fun v : ball (0 : ℂ) E × ℂ =>
        canonicalPassiveRegularKernelInput R p q x v.1 v.2) := by
  classical
  obtain ⟨εP, hεP, hC1, _, hsecond, _⟩ :=
    canonicalBiparameterFamily_first_spatial_parameter_control R p hp q
  obtain ⟨εV, hεV, hspec, _, hvalue⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp q
  let E := min εP εV
  have hE : 0 < E := lt_min hεP hεV
  have heP : E ≤ εP := min_le_left _ _
  have heV : E ≤ εV := min_le_right _ _
  have hzP : ‖(0 : ℂ)‖ < εP := by simpa only [norm_zero] using hεP
  have hzV : ‖(0 : ℂ)‖ < εV := by simpa only [norm_zero] using hεV
  let : NormedSpace ℂ ℂ := NormedField.toNormedSpace
  have hhol (y : ℂ) : DifferentiableOn ℂ
      (fun t => canonicalPassiveRegularKernelInput R p q x t y) (ball 0 E) := by
    by_cases hy : y ∈ upperHalf
    · by_cases hyx : y = (x : ℂ)
      · subst y
        have hxU : (x : ℂ) ∈ upperHalf := x.im_pos
        have hz (t : ℂ) : canonicalPassiveRegularKernelInput R p q x t (x : ℂ) = 0 := by
          rw [canonicalPassiveRegularKernelInput, indicator_of_mem hxU]
          simp only [sub_self, zero_pow two_ne_zero, div_zero]
        simpa only [hz] using
          (differentiableOn_const (𝕜 := ℂ) (c := (0 : ℂ)) (s := ball (0 : ℂ) E))
      · have hx := ((hsecond 0 hzP x (Or.inl x.im_pos)).1).mono (ball_subset_ball heP)
        have hy' := ((hsecond 0 hzP y (Or.inl hy)).1).mono (ball_subset_ball heP)
        have hvx := (hvalue 0 hzV (x : ℂ)).mono (ball_subset_ball heV)
        have hvy := (hvalue 0 hzV y).mono (ball_subset_ball heV)
        have hden (t : ℂ) (ht : t ∈ ball (0 : ℂ) E) :
            canonicalBiparameterFamily R p q 0 t x -
              canonicalBiparameterFamily R p q 0 t y ≠ 0 := by
          obtain ⟨K, hK⟩ := (hspec 0 t hzV ((mem_ball_zero_iff.mp ht).trans_le heV)).2.1
          apply sub_ne_zero.mpr
          exact fun h => hyx (hK.2.2.1.2.1 (mem_univ _) (mem_univ _) h).symm
        simpa only [canonicalPassiveRegularKernelInput, indicator_of_mem hy] using
          (((hx.fun_mul hy').fun_div ((hvx.fun_sub hvy).fun_pow 2)
            (fun t ht => pow_ne_zero 2 (hden t ht))).sub_const
              ((1 : ℂ) / ((x : ℂ) - y) ^ 2))
    · simpa only [canonicalPassiveRegularKernelInput, indicator_of_notMem hy] using
        (differentiableOn_const (𝕜 := ℂ) (c := (0 : ℂ)) (s := ball (0 : ℂ) E))
  have hmeas (t : ℂ) (ht : ‖t‖ < E) :
      Measurable (canonicalPassiveRegularKernelInput R p q x t) := by
    let F := canonicalBiparameterFamily R p q 0 t
    have hF : Continuous (fun y : ℍ => F y) :=
      (hC1 0 t hzP (ht.trans_le heP)).continuousOn.comp_continuous
        UpperHalfPlane.continuous_coe (fun y => Or.inl y.im_pos)
    have hdm : Measurable (fun y : ℍ => dz F y) :=
      (measurable_dz F).comp UpperHalfPlane.continuous_coe.measurable
    have hSm : Measurable (fun y : ℍ => dz F x * dz F y / (F x - F y) ^ 2 -
        1 / ((x : ℂ) - y) ^ 2) :=
      ((hdm.const_mul (dz F x)).div
        ((measurable_const.fun_sub hF.measurable).pow_const 2)).fun_sub
        (measurable_const.div ((measurable_const.fun_sub
          UpperHalfPlane.continuous_coe.measurable).pow_const 2))
    have hcoe : Measurable (fun y : upperHalf => (⟨y.val, y.property⟩ : ℍ)) := by
      apply UpperHalfPlane.measurableEmbedding_coe.measurable_comp_iff.mp
      exact measurable_subtype_coe
    change Measurable (fun y : ℂ => if hy : y ∈ upperHalf then
      dz F x * dz F y / (F x - F y) ^ 2 - 1 / ((x : ℂ) - y) ^ 2 else 0)
    exact (hSm.comp hcoe).dite measurable_const isOpen_upperHalf.measurableSet
  refine ⟨E, hE, hhol, hmeas, ?_⟩
  refine measurable_uncurry_of_continuous_of_measurable
    (u := fun t : ball (0 : ℂ) E => fun y : ℂ =>
      canonicalPassiveRegularKernelInput R p q x t y) ?_ ?_
  · intro y
    exact (hhol y).continuousOn.domRestrict
  · intro t
    exact hmeas t (mem_ball_zero_iff.mp t.property)

private theorem norm_cauchy_factor_le_two (u : ℂ) (hu : ‖u‖ ≤ 1 / 2) :
    1 - u ≠ 0 ∧ ‖(1 - u)⁻¹‖ ≤ 2 := by
  have hden : 1 / 2 ≤ ‖1 - u‖ := by
    have h := norm_sub_norm_le (1 : ℂ) u
    rw [norm_one] at h
    linarith
  have hpos : 0 < ‖1 - u‖ := lt_of_lt_of_le (by norm_num) hden
  refine ⟨norm_pos_iff.mp hpos, ?_⟩
  rw [norm_inv, inv_le_iff_one_le_mul₀ hpos]
  linarith


private def parameterCircleMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Ioc 0 (2 * Real.pi))

private theorem parameterCircleMeasure_univ : parameterCircleMeasure univ = 1 := by
  rw [parameterCircleMeasure, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Ioc, sub_zero]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr Real.two_pi_pos).ne'
    ENNReal.ofReal_ne_top

private instance parameterCircleMeasure_probability : IsProbabilityMeasure parameterCircleMeasure :=
  ⟨parameterCircleMeasure_univ⟩

private theorem parameterCircle_integral_eq_average (f : ℂ → ℂ) (r : ℝ) :
    (∫ θ : ℝ, f (circleMap 0 r θ) ∂parameterCircleMeasure) =
      Real.circleAverage f 0 r := by
  rw [parameterCircleMeasure, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal Real.two_pi_pos.le, Real.circleAverage_def,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]

private theorem parameterCircle_cauchy_formula
    {f : ℂ → ℂ} {E r : ℝ} (hr : 0 < r) (hrE : r < E)
    (hf : DifferentiableOn ℂ f (ball 0 E))
    {s : ℂ} (hs : ‖s‖ < r) :
    (∫ θ : ℝ, f (circleMap 0 r θ) *
      (1 - s / circleMap 0 r θ)⁻¹ ∂parameterCircleMeasure) = f s := by
  have hdisc : DiffContOnCl ℂ f (ball 0 |r|) := by
    rw [abs_of_pos hr]
    exact hf.diffContOnCl_ball (closedBall_subset_ball hrE)
  have hmean := hdisc.circleAverage_smul_div
    (by simpa only [mem_ball_zero_iff, abs_of_pos hr] using hs)
  calc
    (∫ θ : ℝ, f (circleMap 0 r θ) *
        (1 - s / circleMap 0 r θ)⁻¹ ∂parameterCircleMeasure) =
        ∫ θ : ℝ, ((circleMap 0 r θ - 0) / (circleMap 0 r θ - s)) *
          f (circleMap 0 r θ) ∂parameterCircleMeasure := by
      apply integral_congr_ae
      filter_upwards with θ
      have hα : circleMap 0 r θ ≠ 0 := by
        apply norm_ne_zero_iff.mp
        simpa only [norm_circleMap_zero, abs_of_pos hr] using hr.ne'
      have hfactor : (1 - s / circleMap 0 r θ)⁻¹ =
          circleMap 0 r θ / (circleMap 0 r θ - s) := by
        rw [← div_self hα, ← sub_div, inv_div]
      rw [hfactor, sub_zero]
      ring
    _ = f s := by
      rw [parameterCircle_integral_eq_average
        (fun z : ℂ => ((z - 0) / (z - s)) * f z) r]
      simpa only [smul_eq_mul] using hmean

private theorem parameterCircle_factor_bound
    {r : ℝ} (hr : 0 < r) {s : ℂ} (hs : ‖s‖ ≤ r / 2) (θ : ℝ) :
    ‖s / circleMap 0 r θ‖ ≤ 1 / 2 ∧
      ‖(1 - s / circleMap 0 r θ)⁻¹‖ ≤ 2 := by
  have hu : ‖s / circleMap 0 r θ‖ ≤ 1 / 2 := by
    rw [norm_div, norm_circleMap_zero, abs_of_pos hr, div_le_iff₀ hr]
    linarith
  exact ⟨hu, (norm_cauchy_factor_le_two _ hu).2⟩



private theorem passive_circle_real_norm_sq (g : ℝ → ℝ)
    (hg : MemLp g 2 parameterCircleMeasure) :
    ‖hg.toLp g‖ ^ 2 = ∫ θ, g θ ^ 2 ∂parameterCircleMeasure := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with θ hθ
  simp only [hθ, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

private theorem passive_circle_norm_integral_sq_le {B : ℝ → ℂ}
    (hB : MemLp B 2 parameterCircleMeasure) :
    ‖∫ θ, B θ ∂parameterCircleMeasure‖ ^ 2 ≤
      ∫ θ, ‖B θ‖ ^ 2 ∂parameterCircleMeasure := by
  let F := hB.norm.toLp (fun θ => ‖B θ‖)
  have hOne : MemLp (fun _θ : ℝ => (1 : ℝ)) 2 parameterCircleMeasure := memLp_const 1
  let U := hOne.toLp (fun _θ : ℝ => (1 : ℝ))
  have hU : ‖U‖ = 1 := by
    have hs : ‖U‖ ^ 2 = 1 := by
      simpa only [U, one_pow, integral_const, probReal_univ, smul_eq_mul, one_mul] using
        passive_circle_real_norm_sq (fun _θ : ℝ => (1 : ℝ)) hOne
    nlinarith [norm_nonneg U]
  have hinner : inner ℝ U F = ∫ θ, ‖B θ‖ ∂parameterCircleMeasure := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hOne.coeFn_toLp, hB.norm.coeFn_toLp] with θ hθU hθF
    simp only [U, F, hθU, hθF, Real.inner_apply, one_mul]
  have hcs : (∫ θ, ‖B θ‖ ∂parameterCircleMeasure) ≤ ‖F‖ := by
    simpa only [hinner, hU, one_mul] using real_inner_le_norm U F
  have hnorm := (norm_integral_le_integral_norm B).trans hcs
  calc
    ‖∫ θ, B θ ∂parameterCircleMeasure‖ ^ 2 ≤ ‖F‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = ∫ θ, ‖B θ‖ ^ 2 ∂parameterCircleMeasure :=
      passive_circle_real_norm_sq (fun θ => ‖B θ‖) hB.norm

private theorem passive_circle_weighted_sq_bound {B W : ℝ → ℂ} {A : ℝ}
    (hB : MemLp B 2 parameterCircleMeasure) (hW : Measurable W)
    (hbound : ∀ θ, ‖W θ‖ ≤ A) :
    Integrable (fun θ => B θ * W θ) parameterCircleMeasure ∧
      ‖∫ θ, B θ * W θ ∂parameterCircleMeasure‖ ^ 2 ≤
        A ^ 2 * ∫ θ, ‖B θ‖ ^ 2 ∂parameterCircleMeasure := by
  have hnorm (θ : ℝ) : ‖B θ * W θ‖ ≤ A * ‖B θ‖ := by
    rw [norm_mul, mul_comm A]
    exact mul_le_mul_of_nonneg_left (hbound θ) (norm_nonneg _)
  have hBW : MemLp (fun θ => B θ * W θ) 2 parameterCircleMeasure :=
    hB.of_le_mul (hB.aestronglyMeasurable.mul hW.aestronglyMeasurable)
      (Eventually.of_forall hnorm)
  have hsqB := (memLp_two_iff_integrable_sq_norm hB.aestronglyMeasurable).1 hB
  have hsqBW := (memLp_two_iff_integrable_sq_norm hBW.aestronglyMeasurable).1 hBW
  refine ⟨hBW.integrable (by norm_num), ?_⟩
  calc
    _ ≤ ∫ θ, ‖B θ * W θ‖ ^ 2 ∂parameterCircleMeasure :=
      passive_circle_norm_integral_sq_le hBW
    _ ≤ ∫ θ, A ^ 2 * ‖B θ‖ ^ 2 ∂parameterCircleMeasure := by
      apply integral_mono_ae hsqBW (hsqB.const_mul (A ^ 2))
      exact Eventually.of_forall fun θ => by
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hnorm θ) 2
    _ = _ := integral_const_mul _ _

private theorem passive_circle_linear_square_control
    {f : ℂ → ℂ} {E r : ℝ} (hr : 0 < r) (hrE : r < E)
    (hf : DifferentiableOn ℂ f (ball 0 E))
    (hB : MemLp (fun θ : ℝ => f (circleMap 0 r θ)) 2 parameterCircleMeasure) :
    let A := ∫ θ : ℝ, f (circleMap 0 r θ) / circleMap 0 r θ ∂parameterCircleMeasure
    let m := ∫ θ : ℝ, ‖f (circleMap 0 r θ)‖ ^ 2 ∂parameterCircleMeasure
    ‖A‖ ^ 2 ≤ r⁻¹ ^ 2 * m ∧
      ∀ t : ℂ, ‖t‖ ≤ r / 2 →
        ‖f t‖ ^ 2 ≤ 4 * m ∧
          ‖f t - f 0 - A * t‖ ^ 2 ≤
            ((2 / r ^ 2) * ‖t‖ ^ 2) ^ 2 * m := by
  dsimp only
  let B := fun θ : ℝ => f (circleMap 0 r θ)
  let A := ∫ θ : ℝ, B θ / circleMap 0 r θ ∂parameterCircleMeasure
  have hαm : Measurable (circleMap 0 r) := (continuous_circleMap 0 r).measurable
  have hαnorm (θ : ℝ) : ‖circleMap 0 r θ‖ = r := by
    rw [norm_circleMap_zero, abs_of_pos hr]
  have hn (θ : ℝ) : ‖(circleMap 0 r θ)⁻¹‖ ≤ r⁻¹ := by
    rw [norm_inv, hαnorm]
  obtain ⟨hAi, hAq⟩ := passive_circle_weighted_sq_bound hB hαm.inv hn
  have hA : Integrable (fun θ : ℝ => B θ / circleMap 0 r θ) parameterCircleMeasure := by
    simpa only [B, div_eq_mul_inv, Pi.inv_apply] using hAi
  have hbase : (∫ θ : ℝ, B θ ∂parameterCircleMeasure) = f 0 := by
    simpa only [B, zero_div, sub_zero, inv_one, mul_one] using
      parameterCircle_cauchy_formula hr hrE hf (s := 0) (by simpa only [norm_zero] using hr)
  refine ⟨by simpa only [B, div_eq_mul_inv, Pi.inv_apply] using hAq, ?_⟩
  intro t ht
  let u := fun θ : ℝ => t / circleMap 0 r θ
  let W := fun θ : ℝ => (1 - u θ)⁻¹
  have hum : Measurable u := measurable_const.div hαm
  have hWm : Measurable W := (measurable_const.fun_sub hum).inv
  have huf (θ : ℝ) : ‖u θ‖ ≤ 1 / 2 := (parameterCircle_factor_bound hr ht θ).1
  have hWb (θ : ℝ) : ‖W θ‖ ≤ 2 := (parameterCircle_factor_bound hr ht θ).2
  obtain ⟨hiW, hWq⟩ := passive_circle_weighted_sq_bound hB hWm hWb
  have hrep : (∫ θ : ℝ, B θ * W θ ∂parameterCircleMeasure) = f t :=
    parameterCircle_cauchy_formula hr hrE hf (ht.trans_lt (by linarith))
  have hlin : A * t = ∫ θ : ℝ, B θ * u θ ∂parameterCircleMeasure := by
    dsimp only [A]
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with θ
    dsimp only [u]
    ring
  have hiu : Integrable (fun θ : ℝ => B θ * u θ) parameterCircleMeasure := by
    convert hA.mul_const t using 1
    ext θ
    dsimp only [u]
    ring
  have hrem : f t - f 0 - A * t =
      ∫ θ : ℝ, B θ * (W θ - 1 - u θ) ∂parameterCircleMeasure := by
    rw [← hrep, ← hbase, hlin, ← integral_sub hiW (hB.integrable (by norm_num)),
      ← integral_sub (hiW.sub' (hB.integrable (by norm_num))) hiu]
    apply integral_congr_ae
    filter_upwards with θ
    ring
  have hremb (θ : ℝ) : ‖W θ - 1 - u θ‖ ≤ (2 / r ^ 2) * ‖t‖ ^ 2 := by
    have hden := (norm_cauchy_factor_le_two _ (huf θ)).1
    have hid : W θ - 1 - u θ = u θ ^ 2 * (1 - u θ)⁻¹ := by
      dsimp only [W]
      field_simp [hden]
      ring
    calc
      _ = ‖u θ‖ ^ 2 * ‖(1 - u θ)⁻¹‖ := by rw [hid, norm_mul, norm_pow]
      _ ≤ ‖u θ‖ ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left (hWb θ) (sq_nonneg _)
      _ = (2 / r ^ 2) * ‖t‖ ^ 2 := by
        dsimp only [u]
        rw [norm_div, hαnorm, div_pow]
        ring
  refine ⟨?_, ?_⟩
  · rw [← hrep]
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hWq
  · rw [hrem]
    exact (passive_circle_weighted_sq_bound hB
      ((hWm.fun_sub measurable_const).fun_sub hum) hremb).2

private theorem passive_hasDerivAt_of_square_remainder
    {f : ℂ → ℂ} {A : ℂ} {r m : ℝ} (hr : 0 < r) (hm : 0 ≤ m)
    (hrem : ∀ t : ℂ, ‖t‖ ≤ r / 2 →
      ‖f t - f 0 - A * t‖ ^ 2 ≤ ((2 / r ^ 2) * ‖t‖ ^ 2) ^ 2 * m) :
    HasDerivAt f A 0 := by
  let D : ℝ := (2 / r ^ 2) * Real.sqrt m
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hbound (t : ℂ) (ht : ‖t‖ < r / 2) : ‖f t - f 0 - A * t‖ ≤ D * ‖t‖ ^ 2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD (sq_nonneg _))).mp
    calc
      _ ≤ ((2 / r ^ 2) * ‖t‖ ^ 2) ^ 2 * m := hrem t ht.le
      _ = (D * ‖t‖ ^ 2) ^ 2 := by
        dsimp only [D]
        simp only [mul_pow, Real.sq_sqrt hm]
        ring
  have hbig : (fun t : ℂ => f t - f 0 - A * t) =O[𝓝 0] fun t => ‖t‖ ^ 2 := by
    apply Asymptotics.IsBigO.of_bound D
    filter_upwards [ball_mem_nhds (0 : ℂ) (by positivity : 0 < r / 2)] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖t‖ : ℝ))] using
      hbound t (mem_ball_zero_iff.mp ht)
  have hsmall := hbig.trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := ℂ) (by norm_num : 1 < 2))
  apply HasDerivAt.of_isLittleO
  simpa only [sub_zero, smul_eq_mul, mul_comm] using hsmall

set_option maxHeartbeats 2000000 in
/-- A fixed parameter circle controls the same planar input and its actual
linear coefficient on one common almost-everywhere set. The square remainder
also gives an actual L² difference-quotient bound, without point evaluation
of an L² representative. -/
theorem canonicalPassiveRegularKernelInput_finite_cauchy_control
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : ℍ) :
    ∃ (r C : ℝ) (D : ℂ → ℂ) (m : ℂ → ℝ),
      0 < r ∧ 0 ≤ C ∧ Measurable D ∧ MemLp D 2 (volume : Measure ℂ) ∧
      Measurable m ∧ (∀ η, 0 ≤ m η) ∧ Integrable m ∧ (∫ η, m η) ≤ C ∧
      (∀ᵐ η : ℂ,
        HasDerivAt (fun t => canonicalPassiveRegularKernelInput R p q x t η) (D η) 0 ∧
        ‖D η‖ ^ 2 ≤ r⁻¹ ^ 2 * m η ∧
        ∀ t : ℂ, ‖t‖ ≤ r / 2 →
          ‖canonicalPassiveRegularKernelInput R p q x t η‖ ^ 2 ≤ 4 * m η ∧
          ‖canonicalPassiveRegularKernelInput R p q x t η -
            canonicalPassiveRegularKernelInput R p q x 0 η - D η * t‖ ^ 2 ≤
              ((2 / r ^ 2) * ‖t‖ ^ 2) ^ 2 * m η) ∧
      ∀ t : ℂ, ‖t‖ ≤ r / 2 →
        MemLp (fun η : ℂ => canonicalPassiveRegularKernelInput R p q x t η -
          canonicalPassiveRegularKernelInput R p q x 0 η - D η * t) 2 volume ∧
        (∫ η : ℂ, ‖canonicalPassiveRegularKernelInput R p q x t η -
          canonicalPassiveRegularKernelInput R p q x 0 η - D η * t‖ ^ 2) ≤
            (2 / r ^ 2) ^ 2 * C * ‖t‖ ^ 4 := by
  obtain ⟨ε₁, C, hε₁, hC, hinput⟩ :=
    canonicalPassiveRegularKernelInput_uniform_memLp_two R p hp q x
  obtain ⟨ε₂, hε₂, hhol, hmeas, hjoint⟩ :=
    regularInput_holomorphic_and_jointly_measurable R p hp q x
  generalize hactual : canonicalPassiveRegularKernelInput R p q x = f at hinput hhol hmeas hjoint ⊢
  clear hactual
  let r : ℝ := min ε₁ ε₂ / 2
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr₁ : r < ε₁ := by
    have hmin := min_le_left ε₁ ε₂
    dsimp only [r]
    linarith [lt_min hε₁ hε₂]
  have hr₂ : r < ε₂ := by
    have hmin := min_le_right ε₁ ε₂
    dsimp only [r]
    linarith [lt_min hε₁ hε₂]
  let H : ℝ × ℂ → ℂ := fun a =>
    f (circleMap 0 r a.1) a.2
  let M : ℂ → ℝ≥0∞ := fun η => ∫⁻ θ : ℝ, ‖H (θ, η)‖ₑ ^ 2 ∂parameterCircleMeasure
  let m : ℂ → ℝ := fun η => (M η).toReal
  let D : ℂ → ℂ := fun η =>
    ∫ θ : ℝ, H (θ, η) / circleMap 0 r θ ∂parameterCircleMeasure
  have hα₂ (θ : ℝ) : ‖circleMap 0 r θ‖ < ε₂ := by
    simpa only [norm_circleMap_zero, abs_of_pos hr] using hr₂
  have hαm : Measurable (fun θ : ℝ =>
      (⟨circleMap 0 r θ, mem_ball_zero_iff.mpr (hα₂ θ)⟩ : ball (0 : ℂ) ε₂)) :=
    (continuous_circleMap 0 r).measurable.subtype_mk
  have hHm : Measurable H := hjoint.comp
    ((hαm.comp measurable_fst).prodMk measurable_snd)
  have hMm : Measurable M := (hHm.enorm.pow_const 2).lintegral_prod_left'
  have hDsm :=
    (hHm.div ((continuous_circleMap 0 r).measurable.comp measurable_fst)).stronglyMeasurable
  have hDm : Measurable D := hDsm.integral_prod_left'.measurable
  have hL2 (θ : ℝ) : MemLp (fun η : ℂ => H (θ, η)) 2 volume ∧
      (∫ η : ℂ, ‖H (θ, η)‖ ^ 2) ≤ C :=
    hinput (circleMap 0 r θ) (by
      simpa only [norm_circleMap_zero, abs_of_pos hr] using hr₁)
  have hinner (θ : ℝ) : (∫⁻ η : ℂ, ‖H (θ, η)‖ₑ ^ 2) ≤ ENNReal.ofReal C := by
    have hi := (memLp_two_iff_integrable_sq_norm (hL2 θ).1.aestronglyMeasurable).1
      (hL2 θ).1
    have he : ENNReal.ofReal (∫ η : ℂ, ‖H (θ, η)‖ ^ 2) =
        ∫⁻ η : ℂ, ‖H (θ, η)‖ₑ ^ 2 := by
      simpa only [norm_pow, norm_norm, enorm_pow, enorm_norm] using
        ofReal_integral_norm_eq_lintegral_enorm hi
    rw [← he]
    exact ENNReal.ofReal_le_ofReal (hL2 θ).2
  have hMbound : (∫⁻ η : ℂ, M η) ≤ ENNReal.ofReal C := by
    calc
      (∫⁻ η : ℂ, M η) =
          ∫⁻ θ : ℝ, ∫⁻ η : ℂ, ‖H (θ, η)‖ₑ ^ 2 ∂volume ∂parameterCircleMeasure :=
        (lintegral_lintegral_swap (hHm.enorm.pow_const 2).aemeasurable).symm
      _ ≤ ∫⁻ _θ : ℝ, ENNReal.ofReal C ∂parameterCircleMeasure := lintegral_mono hinner
      _ = ENNReal.ofReal C := by simp only [lintegral_const, measure_univ, mul_one]
  have hMfinite : ∀ᵐ η : ℂ, M η < ∞ :=
    ae_lt_top' hMm.aemeasurable (hMbound.trans_lt ENNReal.ofReal_lt_top).ne
  have hm : Integrable m := integrable_toReal_of_lintegral_ne_top hMm.aemeasurable
    (hMbound.trans_lt ENNReal.ofReal_lt_top).ne
  have hmC : (∫ η : ℂ, m η) ≤ C := by
    rw [integral_toReal hMm.aemeasurable hMfinite]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hMbound).trans_eq
      (ENNReal.toReal_ofReal hC)
  have hexpand : ∀ᵐ η : ℂ,
      HasDerivAt (fun t => f t η) (D η) 0 ∧
      ‖D η‖ ^ 2 ≤ r⁻¹ ^ 2 * m η ∧
      ∀ t : ℂ, ‖t‖ ≤ r / 2 →
        ‖f t η‖ ^ 2 ≤ 4 * m η ∧
        ‖f t η -
          f 0 η - D η * t‖ ^ 2 ≤
            ((2 / r ^ 2) * ‖t‖ ^ 2) ^ 2 * m η := by
    filter_upwards [hMfinite] with η hη
    have hBm : Measurable (fun θ : ℝ => H (θ, η)) :=
      hHm.comp (measurable_id.prodMk measurable_const)
    have hBsq : Integrable (fun θ : ℝ => ‖H (θ, η)‖ ^ 2) parameterCircleMeasure := by
      refine ⟨(hBm.norm.pow_const 2).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      simpa only [enorm_pow, enorm_norm] using hη
    have hB : MemLp (fun θ : ℝ => H (θ, η)) 2 parameterCircleMeasure :=
      (memLp_two_iff_integrable_sq_norm hBm.aestronglyMeasurable).2 hBsq
    have hmass : (∫ θ : ℝ, ‖H (θ, η)‖ ^ 2 ∂parameterCircleMeasure) = m η := by
      simpa only [norm_pow, norm_norm, enorm_pow, enorm_norm] using
        integral_norm_eq_lintegral_enorm hBsq.aestronglyMeasurable
    have he := passive_circle_linear_square_control hr hr₂ (hhol η) hB
    change ‖D η‖ ^ 2 ≤ r⁻¹ ^ 2 *
        (∫ θ : ℝ, ‖H (θ, η)‖ ^ 2 ∂parameterCircleMeasure) ∧
      ∀ t : ℂ, ‖t‖ ≤ r / 2 →
        ‖f t η‖ ^ 2 ≤ 4 * (∫ θ : ℝ, ‖H (θ, η)‖ ^ 2 ∂parameterCircleMeasure) ∧
        ‖f t η - f 0 η - D η * t‖ ^ 2 ≤
          ((2 / r ^ 2) * ‖t‖ ^ 2) ^ 2 *
            (∫ θ : ℝ, ‖H (θ, η)‖ ^ 2 ∂parameterCircleMeasure) at he
    simp only [hmass] at he
    refine ⟨?_, he⟩
    exact passive_hasDerivAt_of_square_remainder hr
      (show 0 ≤ m η from ENNReal.toReal_nonneg) (fun t ht => (he.2 t ht).2)
  have hDsq : Integrable (fun η : ℂ => ‖D η‖ ^ 2) :=
    (hm.const_mul (r⁻¹ ^ 2)).mono' (hDm.norm.pow_const 2).aestronglyMeasurable
      (hexpand.mono fun η h => by
        simpa only [Real.norm_of_nonneg (sq_nonneg (‖D η‖))] using h.2.1)
  refine ⟨r, C, D, m, hr, hC, hDm,
    (memLp_two_iff_integrable_sq_norm hDm.aestronglyMeasurable).2 hDsq,
    hMm.ennreal_toReal, fun _ => ENNReal.toReal_nonneg, hm, hmC, hexpand, ?_⟩
  intro t ht
  have ht₂ : ‖t‖ < ε₂ := ht.trans_lt (by linarith)
  have hz₂ : ‖(0 : ℂ)‖ < ε₂ := by simpa only [norm_zero] using hε₂
  have hremm : Measurable (fun η : ℂ => f t η -
      f 0 η - D η * t) :=
    ((hmeas t ht₂).fun_sub (hmeas 0 hz₂)).fun_sub (hDm.mul_const t)
  have hremi : Integrable (fun η : ℂ =>
      ‖f t η -
        f 0 η - D η * t‖ ^ 2) :=
    (hm.const_mul (((2 / r ^ 2) * ‖t‖ ^ 2) ^ 2)).mono'
      (hremm.norm.pow_const 2).aestronglyMeasurable
      (hexpand.mono fun η h => by
        simpa only [Real.norm_of_nonneg (sq_nonneg _)] using (h.2.2 t ht).2)
  refine ⟨(memLp_two_iff_integrable_sq_norm hremm.aestronglyMeasurable).2 hremi, ?_⟩
  calc
    _ ≤ ∫ η : ℂ, ((2 / r ^ 2) * ‖t‖ ^ 2) ^ 2 * m η :=
      integral_mono_ae hremi (hm.const_mul _) (hexpand.mono fun _ h => (h.2.2 t ht).2)
    _ = ((2 / r ^ 2) * ‖t‖ ^ 2) ^ 2 * ∫ η : ℂ, m η := integral_const_mul _ _
    _ ≤ ((2 / r ^ 2) * ‖t‖ ^ 2) ^ 2 * C := mul_le_mul_of_nonneg_left hmC (sq_nonneg _)
    _ = (2 / r ^ 2) ^ 2 * C * ‖t‖ ^ 4 := by ring

/-- The actual input classes form a differentiable L² curve near zero. The
same derivative is the actual scalar derivative almost everywhere; no point
evaluation of a Hilbert-transform class is part of this statement. -/
theorem canonicalPassiveRegularKernelInput_hasDerivAt_toLp
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : ℍ) :
    ∃ (ε : ℝ) (D : ℂ → ℂ) (hD : MemLp D 2 (volume : Measure ℂ))
      (L : ℂ → Lp ℂ 2 (volume : Measure ℂ)),
      0 < ε ∧ Measurable D ∧
      (∀ᵐ η : ℂ,
        HasDerivAt (fun t => canonicalPassiveRegularKernelInput R p q x t η) (D η) 0) ∧
      HasDerivAt L (hD.toLp D) 0 ∧
      ∀ t : ℂ, ‖t‖ < ε →
        (L t : ℂ → ℂ) =ᵐ[volume] canonicalPassiveRegularKernelInput R p q x t := by
  obtain ⟨r, C, D, m, hr, hC, hDm, hD, _, _, _, _, hpoint, hrem⟩ :=
    canonicalPassiveRegularKernelInput_finite_cauchy_control R p hp q x
  obtain ⟨ε₀, _, hε₀, _, hinput⟩ :=
    canonicalPassiveRegularKernelInput_uniform_memLp_two R p hp q x
  let H := canonicalPassiveRegularKernelInput R p q x
  let L : ℂ → Lp ℂ 2 (volume : Measure ℂ) := fun t =>
    if ht : ‖t‖ < ε₀ then (hinput t ht).1.toLp (H t) else 0
  let d : Lp ℂ 2 (volume : Measure ℂ) := hD.toLp D
  let ε : ℝ := min ε₀ (r / 2)
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hL (t : ℂ) (ht : ‖t‖ < ε₀) :
      (L t : ℂ → ℂ) =ᵐ[volume] H t := by
    simpa only [L, dite_eq_left ht] using (hinput t ht).1.coeFn_toLp
  have hz : ‖(0 : ℂ)‖ < ε₀ := by simpa only [norm_zero] using hε₀
  let K : ℝ := Real.sqrt ((2 / r ^ 2) ^ 2 * C)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hbound (t : ℂ) (ht : ‖t‖ < ε) : ‖L t - L 0 - t • d‖ ≤ K * ‖t‖ ^ 2 := by
    have ht₀ : ‖t‖ < ε₀ := ht.trans_le (min_le_left _ _)
    have htr : ‖t‖ ≤ r / 2 := (ht.trans_le (min_le_right _ _)).le
    let f : ℂ → ℂ := fun η => H t η - H 0 η - D η * t
    have hfi : MemLp f 2 volume := (hrem t htr).1
    have he : L t - L 0 - t • d = hfi.toLp f := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub (L t - L 0) (t • d), Lp.coeFn_sub (L t) (L 0),
        Lp.coeFn_smul t d, hL t ht₀, hL 0 hz, hD.coeFn_toLp, hfi.coeFn_toLp]
        with η h₁ h₂ h₃ h₄ h₅ h₆ h₇
      simp only [Pi.sub_apply, Pi.smul_apply] at h₁ h₂ h₃
      rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇]
      change H t η - H 0 η - t * D η = H t η - H 0 η - D η * t
      rw [mul_comm t]
    have hnorm : ‖hfi.toLp f‖ ^ 2 = ∫ η : ℂ, ‖f η‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hfi.coeFn_toLp] with η hη
      rw [real_inner_self_eq_norm_sq, hη]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (sq_nonneg _))).mp
    calc
      _ = ∫ η : ℂ, ‖f η‖ ^ 2 := by rw [he, hnorm]
      _ ≤ (2 / r ^ 2) ^ 2 * C * ‖t‖ ^ 4 := (hrem t htr).2
      _ = (K * ‖t‖ ^ 2) ^ 2 := by
        dsimp only [K]
        rw [mul_pow, Real.sq_sqrt (mul_nonneg (sq_nonneg _) hC)]
        ring
  have hbig : (fun t : ℂ => L t - L 0 - t • d) =O[𝓝 0] fun t => ‖t‖ ^ 2 := by
    apply Asymptotics.IsBigO.of_bound K
    filter_upwards [ball_mem_nhds (0 : ℂ) hε] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖t‖ : ℝ))] using
      hbound t (mem_ball_zero_iff.mp ht)
  have hsmall := hbig.trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := ℂ) (by norm_num : 1 < 2))
  refine ⟨ε, D, hD, L, hε, hDm, hpoint.mono (fun _ h => h.1), ?_, ?_⟩
  · simpa only [hasDerivAt_iff_isLittleO_nhds_zero, zero_add] using hsmall
  · intro t ht
    exact hL t (ht.trans_le (min_le_left _ _))

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
