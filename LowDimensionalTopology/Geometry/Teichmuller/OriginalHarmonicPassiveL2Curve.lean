module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicPassiveL2Input
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The actual passive weighted input as an L² parameter curve

A fixed parameter circle controls the actual planar input and its square
remainder. The resulting L² curve retains the pointwise derivative and the
lower spatial factor of the full two-point kernel.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter MeasureTheory Topology Metric
open scoped ComplexConjugate UpperHalfPlane ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami LiZhongQC WeilPetersson

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

private theorem passiveInput_holomorphic_and_jointly_measurable
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    ∃ E : ℝ, 0 < E ∧
      (∀ η : ℂ, DifferentiableOn ℂ
        (fun t => canonicalPassiveWeightedKernelInput R p q z t η) (ball 0 E)) ∧
      (∀ t : ℂ, ‖t‖ < E → Measurable (canonicalPassiveWeightedKernelInput R p q z t)) ∧
      Measurable (fun x : ball (0 : ℂ) E × ℂ =>
        canonicalPassiveWeightedKernelInput R p q z x.1 x.2) := by
  classical
  obtain ⟨εS, hεS, hC1, _, hsecond, _⟩ :=
    canonicalBiparameterFamily_first_spatial_parameter_control R p hp q
  obtain ⟨εV, hεV, hspec, _, hvalue⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp q
  let E := min εS εV
  have hE : 0 < E := lt_min hεS hεV
  have heS : E ≤ εS := min_le_left _ _
  have heV : E ≤ εV := min_le_right _ _
  let a : ℂ := conj (z : ℂ)
  have hηa (η : ℍ) : (η : ℂ) ≠ a := by
    intro he
    have hi := congrArg Complex.im he
    simp only [a, conj_im, UpperHalfPlane.coe_im] at hi
    linarith [η.im_pos, z.im_pos]
  have hden (t : ℂ) (ht : ‖t‖ < E) (η : ℍ) :
      canonicalBiparameterFamily R p q 0 t η -
        canonicalBiparameterFamily R p q 0 t a ≠ 0 := by
    obtain ⟨K, hK⟩ := (hspec 0 t (by simpa only [norm_zero] using hεV)
      (ht.trans_le heV)).2.1
    apply sub_ne_zero.mpr
    exact fun h => hηa η (hK.2.2.1.2.1 (mem_univ _) (mem_univ _) h)
  let : NormedSpace ℂ ℂ := NormedField.toNormedSpace
  have hholH (η : ℍ) : DifferentiableOn ℂ
      (fun t => harmonicPlane R p q η * dz (canonicalBiparameterFamily R p q 0 t) η /
        (canonicalBiparameterFamily R p q 0 t η -
          canonicalBiparameterFamily R p q 0 t a) ^ 2) (ball 0 E) := by
    have hd := ((hsecond 0 (by simpa only [norm_zero] using hεS) η (Or.inl η.im_pos)).1).mono
      (ball_subset_ball heS)
    have hv := (hvalue 0 (by simpa only [norm_zero] using hεV) η).mono (ball_subset_ball heV)
    have ha := (hvalue 0 (by simpa only [norm_zero] using hεV) a).mono (ball_subset_ball heV)
    exact (hd.const_mul (harmonicPlane R p q η)).fun_div ((hv.fun_sub ha).fun_pow 2)
      (fun t ht => pow_ne_zero 2 (hden t (mem_ball_zero_iff.mp ht) η))
  have hhol (η : ℂ) : DifferentiableOn ℂ
      (fun t => canonicalPassiveWeightedKernelInput R p q z t η) (ball 0 E) := by
    by_cases hη : 0 < η.im
    · simpa only [canonicalPassiveWeightedKernelInput, SourceKernel.upperExtension,
        hη, dite_true, a] using hholH ⟨η, hη⟩
    · simpa only [canonicalPassiveWeightedKernelInput, SourceKernel.upperExtension,
        hη, dite_false] using (differentiableOn_const (c := (0 : ℂ)) (s := ball 0 E))
  have hμc : Continuous (fun η : ℍ => harmonicPlane R p q η) := by
    simpa only [harmonicPlane_eq_coefficient] using
      NativeHarmonicBeltrami.coefficient_continuous R p hp q
  have hmeas (t : ℂ) (ht : ‖t‖ < E) :
      Measurable (canonicalPassiveWeightedKernelInput R p q z t) := by
    let f := canonicalBiparameterFamily R p q 0 t
    have hfH : Continuous (fun η : ℍ => f η) :=
      (hC1 0 t (by simpa only [norm_zero] using hεS) (ht.trans_le heS)).continuousOn.comp_continuous
        UpperHalfPlane.continuous_coe (fun η => Or.inl η.im_pos)
    have hm : Measurable (fun η : ℍ => harmonicPlane R p q η * dz f η / (f η - f a) ^ 2) :=
      (hμc.measurable.fun_mul
        ((measurable_dz f).comp UpperHalfPlane.continuous_coe.measurable)).div
        ((hfH.measurable.sub measurable_const).pow_const 2)
    have hcoe : Measurable (fun η : upperHalf => (⟨η.val, η.property⟩ : ℍ)) := by
      apply UpperHalfPlane.measurableEmbedding_coe.measurable_comp_iff.mp
      exact measurable_subtype_coe
    change Measurable (fun η : ℂ => if hη : η ∈ upperHalf then
      harmonicPlane R p q (⟨η, hη⟩ : ℍ) * dz f η / (f η - f a) ^ 2 else 0)
    exact (hm.comp hcoe).dite measurable_const isOpen_upperHalf.measurableSet
  refine ⟨E, hE, hhol, hmeas, ?_⟩
  refine measurable_uncurry_of_continuous_of_measurable
    (u := fun t : ball (0 : ℂ) E => fun η : ℂ =>
      canonicalPassiveWeightedKernelInput R p q z t η) ?_ ?_
  · intro η
    exact (hhol η).continuousOn.domRestrict
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
theorem canonicalPassiveWeightedKernelInput_finite_cauchy_control
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    ∃ (r C : ℝ) (D : ℂ → ℂ) (m : ℂ → ℝ),
      0 < r ∧ 0 ≤ C ∧ Measurable D ∧ MemLp D 2 (volume : Measure ℂ) ∧
      Measurable m ∧ (∀ η, 0 ≤ m η) ∧ Integrable m ∧ (∫ η, m η) ≤ C ∧
      (∀ᵐ η : ℂ,
        HasDerivAt (fun t => canonicalPassiveWeightedKernelInput R p q z t η) (D η) 0 ∧
        ‖D η‖ ^ 2 ≤ r⁻¹ ^ 2 * m η ∧
        ∀ t : ℂ, ‖t‖ ≤ r / 2 →
          ‖canonicalPassiveWeightedKernelInput R p q z t η‖ ^ 2 ≤ 4 * m η ∧
          ‖canonicalPassiveWeightedKernelInput R p q z t η -
            canonicalPassiveWeightedKernelInput R p q z 0 η - D η * t‖ ^ 2 ≤
              ((2 / r ^ 2) * ‖t‖ ^ 2) ^ 2 * m η) ∧
      ∀ t : ℂ, ‖t‖ ≤ r / 2 →
        MemLp (fun η : ℂ => canonicalPassiveWeightedKernelInput R p q z t η -
          canonicalPassiveWeightedKernelInput R p q z 0 η - D η * t) 2 volume ∧
        (∫ η : ℂ, ‖canonicalPassiveWeightedKernelInput R p q z t η -
          canonicalPassiveWeightedKernelInput R p q z 0 η - D η * t‖ ^ 2) ≤
            (2 / r ^ 2) ^ 2 * C * ‖t‖ ^ 4 := by
  obtain ⟨ε₁, C, hε₁, hC, hinput⟩ :=
    canonicalPassiveWeightedKernelInput_uniform_memLp_two R p hp q z
  obtain ⟨ε₂, hε₂, hhol, hmeas, hjoint⟩ :=
    passiveInput_holomorphic_and_jointly_measurable R p hp q z
  generalize hactual : canonicalPassiveWeightedKernelInput R p q z = f at hinput hhol hmeas hjoint ⊢
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
  let H : ℝ × ℂ → ℂ := fun x =>
    f (circleMap 0 r x.1) x.2
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
theorem canonicalPassiveWeightedKernelInput_hasDerivAt_toLp
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    ∃ (ε : ℝ) (D : ℂ → ℂ) (hD : MemLp D 2 (volume : Measure ℂ))
      (L : ℂ → Lp ℂ 2 (volume : Measure ℂ)),
      0 < ε ∧ Measurable D ∧
      (∀ᵐ η : ℂ,
        HasDerivAt (fun t => canonicalPassiveWeightedKernelInput R p q z t η) (D η) 0) ∧
      HasDerivAt L (hD.toLp D) 0 ∧
      ∀ t : ℂ, ‖t‖ < ε →
        (L t : ℂ → ℂ) =ᵐ[volume] canonicalPassiveWeightedKernelInput R p q z t := by
  obtain ⟨r, C, D, m, hr, hC, hDm, hD, _, _, _, _, hpoint, hrem⟩ :=
    canonicalPassiveWeightedKernelInput_finite_cauchy_control R p hp q z
  obtain ⟨ε₀, _, hε₀, _, hinput⟩ :=
    canonicalPassiveWeightedKernelInput_uniform_memLp_two R p hp q z
  let H := canonicalPassiveWeightedKernelInput R p q z
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

/-- The actual lower spatial factor multiplies the same L² input curve.
Its derivative retains both product terms and agrees almost everywhere
with the actual weighted first derivative of the full two-point kernel. -/
theorem canonicalPassiveFullKernelInput_hasDerivAt_toLp
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    let K := fun (t : ℂ) (η : ℍ) =>
      dz (canonicalBiparameterFamily R p q 0 t) η *
        dz (canonicalBiparameterFamily R p q 0 t) (conj (z : ℂ)) /
        (canonicalBiparameterFamily R p q 0 t η -
          canonicalBiparameterFamily R p q 0 t (conj (z : ℂ))) ^ 2
    let W := fun t => SourceKernel.upperExtension (fun η => harmonicPlane R p q η * K t η)
    ∃ (ε : ℝ) (J : ℂ → ℂ) (hJ : MemLp J 2 (volume : Measure ℂ))
      (M : ℂ → Lp ℂ 2 (volume : Measure ℂ)),
      0 < ε ∧ Measurable J ∧
      (∀ᵐ η : ℂ,
        HasDerivAt (fun t => W t η) (J η) 0 ∧
        J η = SourceKernel.upperExtension
          (fun ξ => harmonicPlane R p q ξ * deriv (fun t => K t ξ) 0) η) ∧
      HasDerivAt M (hJ.toLp J) 0 ∧
      ∀ t : ℂ, ‖t‖ < ε → (M t : ℂ → ℂ) =ᵐ[volume] W t := by
  dsimp only
  obtain ⟨ε, D, hD, L, hε, hDm, hpoint, hLderiv, hL⟩ :=
    canonicalPassiveWeightedKernelInput_hasDerivAt_toLp R p hp q z
  obtain ⟨ε₀, _, hε₀, _, hinput⟩ :=
    canonicalPassiveWeightedKernelInput_uniform_memLp_two R p hp q z
  obtain ⟨εP, hεP, _, _, hparam, _⟩ :=
    canonicalBiparameterFamily_first_spatial_parameter_control R p hp q
  obtain ⟨εV, hεV, _, _, hvalue⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp q
  obtain ⟨εM, hεM, _, hmeas, _⟩ :=
    passiveInput_holomorphic_and_jointly_measurable R p hp q z
  let a : ℂ := conj (z : ℂ)
  let H := canonicalPassiveWeightedKernelInput R p q z
  let c : ℂ → ℂ := fun t => dz (canonicalBiparameterFamily R p q 0 t) a
  let K : ℂ → ℍ → ℂ := fun t η =>
    dz (canonicalBiparameterFamily R p q 0 t) η * c t /
      (canonicalBiparameterFamily R p q 0 t η -
        canonicalBiparameterFamily R p q 0 t a) ^ 2
  let W := fun t => SourceKernel.upperExtension (fun η => harmonicPlane R p q η * K t η)
  have hzP : ‖(0 : ℂ)‖ < εP := by simpa only [norm_zero] using hεP
  have hzV : ‖(0 : ℂ)‖ < εV := by simpa only [norm_zero] using hεV
  have ha : a ∈ lowerHalf := by
    change (conj (z : ℂ)).im < 0
    simpa only [conj_im, UpperHalfPlane.coe_im] using neg_lt_zero.mpr z.im_pos
  have hf0 : canonicalBiparameterFamily R p q 0 0 = id := by
    simpa only [map_zero] using
      (canonicalBiparameterFamily_diagonal R p q 0).trans (canonicalFamily_zero R p q)
  have hc0 : c 0 = 1 := by
    simp only [c, hf0, dz, fderiv_id, ContinuousLinearMap.id_apply]
    rw [I_mul_I]
    ring
  have hc : HasDerivAt c (deriv c 0) 0 :=
    (((hparam 0 hzP a (Or.inr ha)).1).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hεP))).hasDerivAt
  have hKdiff (η : ℍ) : DifferentiableAt ℂ (fun t => K t η) 0 := by
    have hη := ((hparam 0 hzP η (Or.inl η.im_pos)).1).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hεP))
    have hv := (hvalue 0 hzV (η : ℂ)).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hεV))
    have hva := (hvalue 0 hzV a).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hεV))
    have hden : canonicalBiparameterFamily R p q 0 0 η -
        canonicalBiparameterFamily R p q 0 0 a ≠ 0 := by
      rw [hf0]
      apply sub_ne_zero.mpr
      intro he
      have hi := congrArg Complex.im he
      simp only [id_eq, a, conj_im, UpperHalfPlane.coe_im] at hi
      linarith [η.im_pos, z.im_pos]
    exact (hη.fun_mul hc.differentiableAt).fun_div
      ((hv.fun_sub hva).fun_pow 2) (pow_ne_zero 2 hden)
  have hfactor (t η : ℂ) : W t η = c t * H t η := by
    by_cases hη : 0 < η.im
    · simp only [W, H, canonicalPassiveWeightedKernelInput, SourceKernel.upperExtension,
        hη, dite_true, K]
      ring
    · simp only [W, H, canonicalPassiveWeightedKernelInput, SourceKernel.upperExtension,
        hη, dite_false, mul_zero]
  let J : ℂ → ℂ := fun η => deriv c 0 * H 0 η + D η
  have hz₀ : ‖(0 : ℂ)‖ < ε₀ := by simpa only [norm_zero] using hε₀
  have hJ : MemLp J 2 volume := by
    change MemLp ((fun η : ℂ => deriv c 0 * H 0 η) + D) 2 volume
    exact ((hinput 0 hz₀).1.const_mul (deriv c 0)).add hD
  have hJm : Measurable J :=
    ((hmeas 0 (by simpa only [norm_zero] using hεM)).const_mul (deriv c 0)).fun_add hDm
  have hJclass : hJ.toLp J = hD.toLp D + deriv c 0 • L 0 := by
    apply Lp.ext
    filter_upwards [hJ.coeFn_toLp, hD.coeFn_toLp,
      hL 0 (by simpa only [norm_zero] using hε),
      Lp.coeFn_add (hD.toLp D) (deriv c 0 • L 0), Lp.coeFn_smul (deriv c 0) (L 0)]
      with η h₁ h₂ h₃ h₄ h₅
    simp only [Pi.add_apply, Pi.smul_apply] at h₄ h₅
    rw [h₁, h₄, h₅, h₂, h₃]
    change deriv c 0 * H 0 η + D η = D η + deriv c 0 * H 0 η
    exact add_comm _ _
  have hMderiv : HasDerivAt (fun t => c t • L t) (hJ.toLp J) 0 := by
    have h := hc.fun_smul hLderiv
    rw [hc0, one_smul, ← hJclass] at h
    exact h
  have hcanonical : ∀ᵐ η : ℂ,
      HasDerivAt (fun t => W t η) (J η) 0 ∧
      J η = SourceKernel.upperExtension
        (fun ξ => harmonicPlane R p q ξ * deriv (fun t => K t ξ) 0) η := by
    filter_upwards [hpoint] with η hη
    have hprod : HasDerivAt (fun t => c t * H t η) (J η) 0 := by
      simpa only [J, hc0, one_mul] using hc.fun_mul hη
    have hW : HasDerivAt (fun t => W t η) (J η) 0 := by
      convert hprod using 1
      exact funext (fun t => hfactor t η)
    refine ⟨hW, ?_⟩
    by_cases hηU : 0 < η.im
    · have hplain := HasDerivAt.const_mul (harmonicPlane R p q (⟨η, hηU⟩ : ℍ))
        (hKdiff ⟨η, hηU⟩).hasDerivAt
      have hwplain : HasDerivAt (fun t => W t η)
          (harmonicPlane R p q (⟨η, hηU⟩ : ℍ) *
            deriv (fun t => K t ⟨η, hηU⟩) 0) 0 := by
        simpa only [W, SourceKernel.upperExtension, hηU, dite_true] using hplain
      simpa only [SourceKernel.upperExtension, hηU, dite_true] using hW.unique hwplain
    · have hwzero : HasDerivAt (fun t => W t η) 0 0 := by
        simpa only [W, SourceKernel.upperExtension, hηU, dite_false] using
          hasDerivAt_const (0 : ℂ) (0 : ℂ)
      simpa only [SourceKernel.upperExtension, hηU, dite_false] using hW.unique hwzero
  refine ⟨ε, J, hJ, (fun t => c t • L t), hε, hJm, hcanonical, hMderiv, ?_⟩
  intro t ht
  filter_upwards [Lp.coeFn_smul (c t) (L t), hL t ht] with η h₁ h₂
  simp only [Pi.smul_apply] at h₁
  rw [h₁, h₂]
  simpa only [smul_eq_mul] using (hfactor t η).symm

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
