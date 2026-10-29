module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicFirstSpatialParameters
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicComplexifiedKernel
public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalHarmonicFirstJets
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring

/-!
# Finite double-circle control of the actual deformation kernel

The two Cauchy factors give a linear term and a quadratic remainder on
the physical parameter diagonal. Their absolute norm average supplies
the common majorant used for the full upper-half-plane inner integral.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter MeasureTheory Topology Metric
open scoped UpperHalfPlane ComplexConjugate ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami LiZhongQC WeilPetersson

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

private theorem double_cauchy_remainder_identity {u v : ℂ}
    (hu : 1 - u ≠ 0) (hv : 1 - v ≠ 0) :
    (1 - u)⁻¹ * (1 - v)⁻¹ - 1 - u - v =
      u ^ 2 / (1 - u) + v ^ 2 / (1 - v) + u * v / ((1 - u) * (1 - v)) := by
  field_simp [hu, hv]; ring

private theorem double_cauchy_difference_bound (u v : ℂ)
    (hu : ‖u‖ ≤ 1 / 2) (hv : ‖v‖ ≤ 1 / 2) :
    ‖(1 - u)⁻¹ * (1 - v)⁻¹ - 1‖ ≤ 4 * (‖u‖ + ‖v‖) := by
  obtain ⟨hnu, hku⟩ := norm_cauchy_factor_le_two u hu
  obtain ⟨hnv, hkv⟩ := norm_cauchy_factor_le_two v hv
  have heq : (1 - u)⁻¹ * (1 - v)⁻¹ - 1 =
      u * (1 - u)⁻¹ * (1 - v)⁻¹ + v * (1 - v)⁻¹ := by
    field_simp [hnu, hnv]; ring
  rw [heq]
  calc
    ‖u * (1 - u)⁻¹ * (1 - v)⁻¹ + v * (1 - v)⁻¹‖ ≤
        ‖u * (1 - u)⁻¹ * (1 - v)⁻¹‖ + ‖v * (1 - v)⁻¹‖ := norm_add_le _ _
    _ = ‖u‖ * ‖(1 - u)⁻¹‖ * ‖(1 - v)⁻¹‖ + ‖v‖ * ‖(1 - v)⁻¹‖ := by
      rw [norm_mul, norm_mul, norm_mul]
    _ ≤ ‖u‖ * 2 * 2 + ‖v‖ * 2 := by gcongr
    _ ≤ 4 * (‖u‖ + ‖v‖) := by nlinarith [norm_nonneg v]

private theorem double_cauchy_quadratic_remainder_bound (u v : ℂ)
    (hu : ‖u‖ ≤ 1 / 2) (hv : ‖v‖ ≤ 1 / 2) :
    ‖(1 - u)⁻¹ * (1 - v)⁻¹ - 1 - u - v‖ ≤ 2 * (‖u‖ + ‖v‖) ^ 2 := by
  obtain ⟨hnu, hku⟩ := norm_cauchy_factor_le_two u hu
  obtain ⟨hnv, hkv⟩ := norm_cauchy_factor_le_two v hv
  have h₁ : ‖u ^ 2 / (1 - u)‖ ≤ 2 * ‖u‖ ^ 2 := by
    calc
      ‖u ^ 2 / (1 - u)‖ = ‖u‖ ^ 2 * ‖(1 - u)⁻¹‖ := by
        rw [div_eq_mul_inv, norm_mul, norm_pow]
      _ ≤ ‖u‖ ^ 2 * 2 := mul_le_mul_of_nonneg_left hku (sq_nonneg _)
      _ = 2 * ‖u‖ ^ 2 := by ring
  have h₂ : ‖v ^ 2 / (1 - v)‖ ≤ 2 * ‖v‖ ^ 2 := by
    calc
      ‖v ^ 2 / (1 - v)‖ = ‖v‖ ^ 2 * ‖(1 - v)⁻¹‖ := by
        rw [div_eq_mul_inv, norm_mul, norm_pow]
      _ ≤ ‖v‖ ^ 2 * 2 := mul_le_mul_of_nonneg_left hkv (sq_nonneg _)
      _ = 2 * ‖v‖ ^ 2 := by ring
  have h₃ : ‖u * v / ((1 - u) * (1 - v))‖ ≤ 4 * ‖u‖ * ‖v‖ := by
    calc
      ‖u * v / ((1 - u) * (1 - v))‖ =
          ‖u‖ * ‖v‖ * (‖(1 - v)⁻¹‖ * ‖(1 - u)⁻¹‖) := by
        rw [div_eq_mul_inv, mul_inv_rev]
        simp only [norm_mul]
      _ ≤ ‖u‖ * ‖v‖ * (2 * 2) := by gcongr
      _ = 4 * ‖u‖ * ‖v‖ := by ring
  rw [double_cauchy_remainder_identity hnu hnv]
  calc
    ‖u ^ 2 / (1 - u) + v ^ 2 / (1 - v) + u * v / ((1 - u) * (1 - v))‖ ≤
        ‖u ^ 2 / (1 - u) + v ^ 2 / (1 - v)‖ + ‖u * v / ((1 - u) * (1 - v))‖ :=
      norm_add_le _ _
    _ ≤ (‖u ^ 2 / (1 - u)‖ + ‖v ^ 2 / (1 - v)‖) +
        ‖u * v / ((1 - u) * (1 - v))‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2) + 4 * ‖u‖ * ‖v‖ :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ = 2 * (‖u‖ + ‖v‖) ^ 2 := by ring

private def parameterCircleMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Ioc 0 (2 * Real.pi))

private theorem parameterCircleMeasure_univ : parameterCircleMeasure univ = 1 := by
  rw [parameterCircleMeasure, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Ioc, sub_zero]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr Real.two_pi_pos).ne'
    ENNReal.ofReal_ne_top

private instance parameterCircleMeasure_probability : IsProbabilityMeasure parameterCircleMeasure :=
  ⟨parameterCircleMeasure_univ⟩

private theorem flatArea_sigmaFinite : SigmaFinite flatArea := by
  let : IsFiniteMeasureOnCompacts flatArea :=
    IsFiniteMeasureOnCompacts.comap' volume UpperHalfPlane.continuous_coe
      UpperHalfPlane.measurableEmbedding_coe
  infer_instance

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

private theorem parameterCircle_double_cauchy_formula
    {F : ℂ → ℂ → ℂ} {E r : ℝ} (hr : 0 < r) (hrE : r < E)
    (hfirst : ∀ t : ℂ, ‖t‖ < E → DifferentiableOn ℂ (fun s => F s t) (ball 0 E))
    (hsecond : ∀ s : ℂ, ‖s‖ < E → DifferentiableOn ℂ (F s) (ball 0 E))
    (hboundary : Integrable (fun θφ : ℝ × ℝ =>
      F (circleMap 0 r θφ.1) (circleMap 0 r θφ.2))
      (parameterCircleMeasure.prod parameterCircleMeasure))
    {s t : ℂ} (hs : ‖s‖ ≤ r / 2) (ht : ‖t‖ ≤ r / 2) :
    (∫ θφ : ℝ × ℝ, F (circleMap 0 r θφ.1) (circleMap 0 r θφ.2) *
      ((1 - s / circleMap 0 r θφ.1)⁻¹ * (1 - t / circleMap 0 r θφ.2)⁻¹)
      ∂parameterCircleMeasure.prod parameterCircleMeasure) = F s t := by
  have hs' : ‖s‖ < r := lt_of_le_of_lt hs (by linarith)
  have ht' : ‖t‖ < r := lt_of_le_of_lt ht (by linarith)
  have hα (θ : ℝ) : ‖circleMap 0 r θ‖ < E := by
    simpa only [norm_circleMap_zero, abs_of_pos hr] using hrE
  have hm₁ : Measurable (fun θφ : ℝ × ℝ =>
      (1 - s / circleMap 0 r θφ.1)⁻¹) :=
    (measurable_const.sub (measurable_const.div
      ((continuous_circleMap 0 r).measurable.comp measurable_fst))).inv
  have hm₂ : Measurable (fun θφ : ℝ × ℝ =>
      (1 - t / circleMap 0 r θφ.2)⁻¹) :=
    (measurable_const.sub (measurable_const.div
      ((continuous_circleMap 0 r).measurable.comp measurable_snd))).inv
  have hi := hboundary.mul_bdd (hm₁.fun_mul hm₂).aestronglyMeasurable
    (Eventually.of_forall (fun θφ => show
      ‖(1 - s / circleMap 0 r θφ.1)⁻¹ * (1 - t / circleMap 0 r θφ.2)⁻¹‖ ≤ 4 from by
        rw [norm_mul]
        nlinarith [(parameterCircle_factor_bound hr hs θφ.1).2,
          (parameterCircle_factor_bound hr ht θφ.2).2,
          norm_nonneg ((1 - s / circleMap 0 r θφ.1)⁻¹),
          norm_nonneg ((1 - t / circleMap 0 r θφ.2)⁻¹)]))
  rw [integral_prod _ hi]
  calc
    (∫ θ : ℝ, ∫ φ : ℝ, F (circleMap 0 r θ) (circleMap 0 r φ) *
        ((1 - s / circleMap 0 r θ)⁻¹ * (1 - t / circleMap 0 r φ)⁻¹)
        ∂parameterCircleMeasure ∂parameterCircleMeasure) =
        ∫ θ : ℝ, F (circleMap 0 r θ) t * (1 - s / circleMap 0 r θ)⁻¹
          ∂parameterCircleMeasure := by
      apply integral_congr_ae
      filter_upwards with θ
      calc
        (∫ φ : ℝ, F (circleMap 0 r θ) (circleMap 0 r φ) *
            ((1 - s / circleMap 0 r θ)⁻¹ * (1 - t / circleMap 0 r φ)⁻¹)
            ∂parameterCircleMeasure) =
            (∫ φ : ℝ, F (circleMap 0 r θ) (circleMap 0 r φ) *
              (1 - t / circleMap 0 r φ)⁻¹ ∂parameterCircleMeasure) *
                (1 - s / circleMap 0 r θ)⁻¹ := by
          rw [← integral_mul_const]
          apply integral_congr_ae
          filter_upwards with φ
          ring
        _ = F (circleMap 0 r θ) t * (1 - s / circleMap 0 r θ)⁻¹ := by
          rw [parameterCircle_cauchy_formula hr hrE (hsecond _ (hα θ)) ht']
    _ = F s t := parameterCircle_cauchy_formula hr hrE
      (hfirst t (ht'.trans hrE)) hs'

private theorem doubleCircle_weighted_norm_bound
    {B W : ℝ × ℝ → ℂ} {c : ℝ}
    (hB : Integrable B (parameterCircleMeasure.prod parameterCircleMeasure))
    (hW : ∀ θφ, ‖W θφ‖ ≤ c) :
    ‖∫ θφ : ℝ × ℝ, B θφ * W θφ
      ∂parameterCircleMeasure.prod parameterCircleMeasure‖ ≤
        c * ∫ θφ : ℝ × ℝ, ‖B θφ‖
          ∂parameterCircleMeasure.prod parameterCircleMeasure := by
  calc
    ‖∫ θφ : ℝ × ℝ, B θφ * W θφ
        ∂parameterCircleMeasure.prod parameterCircleMeasure‖ ≤
        ∫ θφ : ℝ × ℝ, c * ‖B θφ‖
          ∂parameterCircleMeasure.prod parameterCircleMeasure := by
      apply norm_integral_le_of_norm_le (hB.norm.const_mul c)
      filter_upwards with θφ
      rw [norm_mul, mul_comm c]
      exact mul_le_mul_of_nonneg_left (hW θφ) (norm_nonneg _)
    _ = c * ∫ θφ : ℝ × ℝ, ‖B θφ‖
        ∂parameterCircleMeasure.prod parameterCircleMeasure := integral_const_mul _ _

private theorem parameterCircle_double_expansion
    {F : ℂ → ℂ → ℂ} {E r : ℝ} (hr : 0 < r) (hrE : r < E)
    (hfirst : ∀ t : ℂ, ‖t‖ < E → DifferentiableOn ℂ (fun s => F s t) (ball 0 E))
    (hsecond : ∀ s : ℂ, ‖s‖ < E → DifferentiableOn ℂ (F s) (ball 0 E))
    (hboundary : Integrable (fun θφ : ℝ × ℝ =>
      F (circleMap 0 r θφ.1) (circleMap 0 r θφ.2))
      (parameterCircleMeasure.prod parameterCircleMeasure)) :
    let σ := parameterCircleMeasure.prod parameterCircleMeasure
    let B := fun θφ : ℝ × ℝ => F (circleMap 0 r θφ.1) (circleMap 0 r θφ.2)
    let m := ∫ θφ : ℝ × ℝ, ‖B θφ‖ ∂σ
    let A₁ := ∫ θφ : ℝ × ℝ, B θφ / circleMap 0 r θφ.1 ∂σ
    let A₂ := ∫ θφ : ℝ × ℝ, B θφ / circleMap 0 r θφ.2 ∂σ
    ‖A₁‖ ≤ m / r ∧ ‖A₂‖ ≤ m / r ∧
      ∀ s t : ℂ, ‖s‖ ≤ r / 2 → ‖t‖ ≤ r / 2 →
        ‖F s t‖ ≤ 4 * m ∧
        ‖F s t - F 0 0‖ ≤ (4 / r) * (‖s‖ + ‖t‖) * m ∧
        ‖F s t - F 0 0 - A₁ * s - A₂ * t‖ ≤
          (2 / r ^ 2) * (‖s‖ + ‖t‖) ^ 2 * m := by
  dsimp only
  let σ := parameterCircleMeasure.prod parameterCircleMeasure
  let B := fun θφ : ℝ × ℝ => F (circleMap 0 r θφ.1) (circleMap 0 r θφ.2)
  let m := ∫ θφ : ℝ × ℝ, ‖B θφ‖ ∂σ
  have hαnorm (θ : ℝ) : ‖circleMap 0 r θ‖ = r := by
    rw [norm_circleMap_zero, abs_of_pos hr]
  have hm₁ : Measurable (fun θφ : ℝ × ℝ => (circleMap 0 r θφ.1)⁻¹) :=
    ((continuous_circleMap 0 r).measurable.comp measurable_fst).inv
  have hm₂ : Measurable (fun θφ : ℝ × ℝ => (circleMap 0 r θφ.2)⁻¹) :=
    ((continuous_circleMap 0 r).measurable.comp measurable_snd).inv
  have hn₁ (θφ : ℝ × ℝ) : ‖(circleMap 0 r θφ.1)⁻¹‖ ≤ r⁻¹ := by
    rw [norm_inv, hαnorm]
  have hn₂ (θφ : ℝ × ℝ) : ‖(circleMap 0 r θφ.2)⁻¹‖ ≤ r⁻¹ := by
    rw [norm_inv, hαnorm]
  have hi₁ : Integrable (fun θφ : ℝ × ℝ => B θφ / circleMap 0 r θφ.1) σ := by
    simpa only [div_eq_mul_inv] using
      hboundary.mul_bdd hm₁.aestronglyMeasurable (Eventually.of_forall hn₁)
  have hi₂ : Integrable (fun θφ : ℝ × ℝ => B θφ / circleMap 0 r θφ.2) σ := by
    simpa only [div_eq_mul_inv] using
      hboundary.mul_bdd hm₂.aestronglyMeasurable (Eventually.of_forall hn₂)
  have h0 : ‖(0 : ℂ)‖ ≤ r / 2 := by simp only [norm_zero]; positivity
  have hbase : (∫ θφ : ℝ × ℝ, B θφ ∂σ) = F 0 0 := by
    simpa only [zero_div, sub_zero, inv_one, mul_one] using
      parameterCircle_double_cauchy_formula hr hrE hfirst hsecond hboundary h0 h0
  refine ⟨?_, ?_, ?_⟩
  · simpa only [div_eq_mul_inv, mul_comm r⁻¹] using
      doubleCircle_weighted_norm_bound hboundary hn₁
  · simpa only [div_eq_mul_inv, mul_comm r⁻¹] using
      doubleCircle_weighted_norm_bound hboundary hn₂
  intro s t hs ht
  let u := fun θφ : ℝ × ℝ => s / circleMap 0 r θφ.1
  let v := fun θφ : ℝ × ℝ => t / circleMap 0 r θφ.2
  let W := fun θφ : ℝ × ℝ => (1 - u θφ)⁻¹ * (1 - v θφ)⁻¹
  have hum : Measurable u := measurable_const.div
    ((continuous_circleMap 0 r).measurable.comp measurable_fst)
  have hvm : Measurable v := measurable_const.div
    ((continuous_circleMap 0 r).measurable.comp measurable_snd)
  have hWm : Measurable W :=
    (measurable_const.sub hum).inv.mul (measurable_const.sub hvm).inv
  have huf (θφ : ℝ × ℝ) : ‖u θφ‖ ≤ 1 / 2 :=
    (parameterCircle_factor_bound hr hs θφ.1).1
  have hvf (θφ : ℝ × ℝ) : ‖v θφ‖ ≤ 1 / 2 :=
    (parameterCircle_factor_bound hr ht θφ.2).1
  have hWb (θφ : ℝ × ℝ) : ‖W θφ‖ ≤ 4 := by
    dsimp only [W]
    rw [norm_mul]
    have h₁ := (norm_cauchy_factor_le_two _ (huf θφ)).2
    have h₂ := (norm_cauchy_factor_le_two _ (hvf θφ)).2
    nlinarith [norm_nonneg ((1 - u θφ)⁻¹), norm_nonneg ((1 - v θφ)⁻¹)]
  have hiW := hboundary.mul_bdd hWm.aestronglyMeasurable
    (Eventually.of_forall hWb)
  have hrep : (∫ θφ : ℝ × ℝ, B θφ * W θφ ∂σ) = F s t :=
    parameterCircle_double_cauchy_formula hr hrE hfirst hsecond hboundary hs ht
  have huNorm (θφ : ℝ × ℝ) : ‖u θφ‖ = ‖s‖ / r := by
    dsimp only [u]
    rw [norm_div, hαnorm]
  have hvNorm (θφ : ℝ × ℝ) : ‖v θφ‖ = ‖t‖ / r := by
    dsimp only [v]
    rw [norm_div, hαnorm]
  have hsum : ‖s‖ / r + ‖t‖ / r = (‖s‖ + ‖t‖) / r := by ring
  have hdiff : F s t - F 0 0 =
      ∫ θφ : ℝ × ℝ, B θφ * (W θφ - 1) ∂σ := by
    rw [← hrep, ← hbase, ← integral_sub hiW hboundary]
    apply integral_congr_ae
    filter_upwards with θφ
    ring
  have hlin₁ : (∫ θφ : ℝ × ℝ, B θφ / circleMap 0 r θφ.1 ∂σ) * s =
      ∫ θφ : ℝ × ℝ, B θφ * u θφ ∂σ := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with θφ
    dsimp only [u]
    ring
  have hlin₂ : (∫ θφ : ℝ × ℝ, B θφ / circleMap 0 r θφ.2 ∂σ) * t =
      ∫ θφ : ℝ × ℝ, B θφ * v θφ ∂σ := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with θφ
    dsimp only [v]
    ring
  have hiu : Integrable (fun θφ : ℝ × ℝ => B θφ * u θφ) σ := by
    convert hi₁.mul_const s using 1
    ext θφ
    dsimp only [u]
    ring
  have hiv : Integrable (fun θφ : ℝ × ℝ => B θφ * v θφ) σ := by
    convert hi₂.mul_const t using 1
    ext θφ
    dsimp only [v]
    ring
  have hrem : F s t - F 0 0 -
      (∫ θφ : ℝ × ℝ, B θφ / circleMap 0 r θφ.1 ∂σ) * s -
      (∫ θφ : ℝ × ℝ, B θφ / circleMap 0 r θφ.2 ∂σ) * t =
      ∫ θφ : ℝ × ℝ, B θφ * (W θφ - 1 - u θφ - v θφ) ∂σ := by
    rw [← hrep, ← hbase, hlin₁, hlin₂,
      ← integral_sub hiW hboundary, ← integral_sub (hiW.sub' hboundary) hiu,
      ← integral_sub ((hiW.sub' hboundary).sub' hiu) hiv]
    apply integral_congr_ae
    filter_upwards with θφ
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [← hrep]
    exact doubleCircle_weighted_norm_bound hboundary hWb
  · rw [hdiff]
    have hb (θφ : ℝ × ℝ) : ‖W θφ - 1‖ ≤ (4 / r) * (‖s‖ + ‖t‖) := by
      have h := double_cauchy_difference_bound (u θφ) (v θφ) (huf θφ) (hvf θφ)
      rw [huNorm, hvNorm, hsum] at h
      change ‖(1 - u θφ)⁻¹ * (1 - v θφ)⁻¹ - 1‖ ≤ _
      calc
        _ ≤ 4 * ((‖s‖ + ‖t‖) / r) := h
        _ = (4 / r) * (‖s‖ + ‖t‖) := by ring
    exact doubleCircle_weighted_norm_bound hboundary hb
  · rw [hrem]
    have hb (θφ : ℝ × ℝ) :
        ‖W θφ - 1 - u θφ - v θφ‖ ≤ (2 / r ^ 2) * (‖s‖ + ‖t‖) ^ 2 := by
      have h := double_cauchy_quadratic_remainder_bound
        (u θφ) (v θφ) (huf θφ) (hvf θφ)
      rw [huNorm, hvNorm, hsum] at h
      change ‖(1 - u θφ)⁻¹ * (1 - v θφ)⁻¹ - 1 - u θφ - v θφ‖ ≤ _
      calc
        _ ≤ 2 * ((‖s‖ + ‖t‖) / r) ^ 2 := h
        _ = (2 / r ^ 2) * (‖s‖ + ‖t‖) ^ 2 := by
          rw [div_pow]
          ring
    exact doubleCircle_weighted_norm_bound hboundary hb

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

private theorem kernel_separately_holomorphic
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (qdir qtest : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ζ : ℍ,
      (∀ t : ℂ, ‖t‖ < ε → DifferentiableOn ℂ
        (fun s => canonicalBiparameterKernelIntegrand R p qdir qtest s t z ζ) (ball 0 ε)) ∧
      (∀ s : ℂ, ‖s‖ < ε → DifferentiableOn ℂ
        (fun t => canonicalBiparameterKernelIntegrand R p qdir qtest s t z ζ) (ball 0 ε)) := by
  obtain ⟨ε₁, hε₁, _, hdzfirst, hdzsecond, _⟩ :=
    canonicalBiparameterFamily_first_spatial_parameter_control R p hp qdir
  obtain ⟨ε₂, hε₂, hspec, hfirst, hsecond⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp qdir
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have he₁ : ε ≤ ε₁ := min_le_left _ _
  have he₂ : ε ≤ ε₂ := min_le_right _ _
  refine ⟨ε, hε, ?_⟩
  intro z ζ
  have hzU : (z : ℂ) ∈ upperHalf ∪ lowerHalf := Or.inl z.im_pos
  have hζL : conj (ζ : ℂ) ∈ upperHalf ∪ lowerHalf := by
    right
    change (conj (ζ : ℂ)).im < 0
    simpa only [conj_im, UpperHalfPlane.coe_im] using neg_lt_zero.mpr ζ.im_pos
  have hdistinct : (z : ℂ) ≠ conj (ζ : ℂ) := by
    intro h
    have hi := congrArg Complex.im h
    simp only [conj_im, UpperHalfPlane.coe_im] at hi
    linarith [z.im_pos, ζ.im_pos]
  have hden (s t : ℂ) (hs : ‖s‖ < ε) (ht : ‖t‖ < ε) :
      canonicalBiparameterFamily R p qdir s t z -
        canonicalBiparameterFamily R p qdir s t (conj (ζ : ℂ)) ≠ 0 := by
    obtain ⟨K, hK⟩ := (hspec s t (hs.trans_le he₂) (ht.trans_le he₂)).2.1
    apply sub_ne_zero.mpr
    exact fun h => hdistinct (hK.2.2.1.2.1 (mem_univ _) (mem_univ _) h)
  let : NormedSpace ℂ ℂ := NormedField.toNormedSpace
  constructor
  · intro t ht
    have hz := ((hdzfirst t (ht.trans_le he₁) z hzU).1).mono (ball_subset_ball he₁)
    have hζ := ((hdzfirst t (ht.trans_le he₁) (conj (ζ : ℂ)) hζL).1).mono
      (ball_subset_ball he₁)
    have hvz := (hfirst t (ht.trans_le he₂) (z : ℂ)).mono (ball_subset_ball he₂)
    have hvζ := (hfirst t (ht.trans_le he₂) (conj (ζ : ℂ))).mono (ball_subset_ball he₂)
    change DifferentiableOn ℂ (fun s =>
      (dz (canonicalBiparameterFamily R p qdir s t) z *
        dz (canonicalBiparameterFamily R p qdir s t) (conj (ζ : ℂ)) /
          (canonicalBiparameterFamily R p qdir s t z -
            canonicalBiparameterFamily R p qdir s t (conj (ζ : ℂ))) ^ 2) ^ 2 *
        conj (harmonicPlane R p qtest (ζ : ℂ))) (ball 0 ε)
    exact (((hz.fun_mul hζ).fun_div ((hvz.fun_sub hvζ).fun_pow 2)
      (fun s hs => pow_ne_zero 2 (hden s t (mem_ball_zero_iff.mp hs) ht))).fun_pow 2).mul_const
        (conj (harmonicPlane R p qtest (ζ : ℂ)))
  · intro s hs
    have hz := ((hdzsecond s (hs.trans_le he₁) z hzU).1).mono (ball_subset_ball he₁)
    have hζ := ((hdzsecond s (hs.trans_le he₁) (conj (ζ : ℂ)) hζL).1).mono
      (ball_subset_ball he₁)
    have hvz := (hsecond s (hs.trans_le he₂) (z : ℂ)).mono (ball_subset_ball he₂)
    have hvζ := (hsecond s (hs.trans_le he₂) (conj (ζ : ℂ))).mono (ball_subset_ball he₂)
    change DifferentiableOn ℂ (fun t =>
      (dz (canonicalBiparameterFamily R p qdir s t) z *
        dz (canonicalBiparameterFamily R p qdir s t) (conj (ζ : ℂ)) /
          (canonicalBiparameterFamily R p qdir s t z -
            canonicalBiparameterFamily R p qdir s t (conj (ζ : ℂ))) ^ 2) ^ 2 *
        conj (harmonicPlane R p qtest (ζ : ℂ))) (ball 0 ε)
    exact (((hz.fun_mul hζ).fun_div ((hvz.fun_sub hvζ).fun_pow 2)
      (fun t ht => pow_ne_zero 2 (hden s t hs (mem_ball_zero_iff.mp ht)))).fun_pow 2).mul_const
        (conj (harmonicPlane R p qtest (ζ : ℂ)))

private theorem kernel_jointly_measurable
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (qdir qtest : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ Measurable
      (fun x : ball (0 : ℂ) ε × (ball (0 : ℂ) ε × (ℍ × ℍ)) =>
        canonicalBiparameterKernelIntegrand R p qdir qtest x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  obtain ⟨ε₁, hε₁, hhol⟩ := kernel_separately_holomorphic R p hp qdir qtest
  obtain ⟨ε₂, hε₂, hspec, _, _⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp qdir
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have he₁ : ε ≤ ε₁ := min_le_left _ _
  have he₂ : ε ≤ ε₂ := min_le_right _ _
  let P := ball (0 : ℂ) ε
  have hcoefficient : Continuous (fun ζ : ℍ => harmonicPlane R p qtest ζ) := by
    have heq : (fun ζ : ℍ => harmonicPlane R p qtest ζ) =
        NativeHarmonicBeltrami.coefficient R p qtest :=
      funext (fun ζ => harmonicPlane_eq_coefficient R p qtest ζ)
    rw [heq]
    exact NativeHarmonicBeltrami.coefficient_continuous R p hp qtest
  have hspace (s t : P) : Measurable (fun x : ℍ × ℍ =>
      canonicalBiparameterKernelIntegrand R p qdir qtest s t x.1 x.2) := by
    let f := canonicalBiparameterFamily R p qdir s t
    obtain ⟨K, hK⟩ := (hspec s t
      ((mem_ball_zero_iff.mp s.property).trans_le he₂)
      ((mem_ball_zero_iff.mp t.property).trans_le he₂)).2.1
    have hf : Continuous f := continuousOn_univ.mp hK.2.2.1.1
    have hz : Measurable (fun x : ℍ × ℍ => (x.1 : ℂ)) :=
      UpperHalfPlane.continuous_coe.measurable.comp measurable_fst
    have hζ : Measurable (fun x : ℍ × ℍ => conj (x.2 : ℂ)) :=
      Complex.continuous_conj.measurable.comp
        (UpperHalfPlane.continuous_coe.measurable.comp measurable_snd)
    have hκ : Measurable (fun x : ℍ × ℍ => conj (harmonicPlane R p qtest x.2)) :=
      Complex.continuous_conj.measurable.comp (hcoefficient.measurable.comp measurable_snd)
    change Measurable (fun x : ℍ × ℍ =>
      (dz f x.1 * dz f (conj (x.2 : ℂ)) / (f x.1 - f (conj (x.2 : ℂ))) ^ 2) ^ 2 *
        conj (harmonicPlane R p qtest x.2))
    exact ((((measurable_dz f).comp hz).mul ((measurable_dz f).comp hζ)).div
      (((hf.measurable.comp hz).sub (hf.measurable.comp hζ)).pow_const 2)).pow_const 2 |>.mul hκ
  have hsecond (s : P) : Measurable (fun x : P × (ℍ × ℍ) =>
      canonicalBiparameterKernelIntegrand R p qdir qtest s x.1 x.2.1 x.2.2) := by
    refine measurable_uncurry_of_continuous_of_measurable
      (u := fun t : P => fun x : ℍ × ℍ =>
        canonicalBiparameterKernelIntegrand R p qdir qtest s t x.1 x.2) ?_ ?_
    · intro x
      exact (((hhol x.1 x.2).2 s ((mem_ball_zero_iff.mp s.property).trans_le he₁)).mono
        (ball_subset_ball he₁)).continuousOn.domRestrict
    · intro t
      exact hspace s t
  refine ⟨ε, hε, ?_⟩
  refine measurable_uncurry_of_continuous_of_measurable
    (u := fun s : P => fun x : P × (ℍ × ℍ) =>
      canonicalBiparameterKernelIntegrand R p qdir qtest s x.1 x.2.1 x.2.2) ?_ ?_
  · intro x
    exact (((hhol x.2.1 x.2.2).1 x.1
      ((mem_ball_zero_iff.mp x.1.property).trans_le he₁)).mono
        (ball_subset_ball he₁)).continuousOn.domRestrict
  · intro s
    exact hsecond s

private theorem kernel_boundary_jointly_measurable
    (qdir qtest : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {ε r : ℝ} (hr : 0 < r) (hrε : r < ε)
    (hjoint : Measurable
      (fun x : ball (0 : ℂ) ε × (ball (0 : ℂ) ε × (ℍ × ℍ)) =>
        canonicalBiparameterKernelIntegrand R p qdir qtest x.1 x.2.1 x.2.2.1 x.2.2.2))
    (z : ℍ) : Measurable (fun x : (ℝ × ℝ) × ℍ =>
      canonicalBiparameterKernelIntegrand R p qdir qtest
        (circleMap 0 r x.1.1) (circleMap 0 r x.1.2) z x.2) := by
  generalize hkernel : canonicalBiparameterKernelIntegrand R p qdir qtest = g at *
  have hα (θ : ℝ) : circleMap 0 r θ ∈ ball (0 : ℂ) ε := by
    simpa only [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr] using hrε
  have hη₁ : Measurable (fun x : (ℝ × ℝ) × ℍ =>
      (⟨circleMap 0 r x.1.1, hα x.1.1⟩ : ball (0 : ℂ) ε)) :=
    ((continuous_circleMap 0 r).measurable.comp (measurable_fst.comp measurable_fst)).subtype_mk
  have hη₂ : Measurable (fun x : (ℝ × ℝ) × ℍ =>
      (⟨circleMap 0 r x.1.2, hα x.1.2⟩ : ball (0 : ℂ) ε)) :=
    ((continuous_circleMap 0 r).measurable.comp (measurable_snd.comp measurable_fst)).subtype_mk
  exact hjoint.comp (hη₁.prodMk (hη₂.prodMk (measurable_const.prodMk measurable_snd)))

private theorem kernel_circle_average_integrable
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (qdir qtest : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (K : Set ℍ) (hK : IsCompact K) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r < ε → ∀ z ∈ K,
      let M := fun ζ : ℍ => ∫⁻ θφ : ℝ × ℝ,
        ‖canonicalBiparameterKernelIntegrand R p qdir qtest
          (circleMap 0 r θφ.1) (circleMap 0 r θφ.2) z ζ‖ₑ
          ∂parameterCircleMeasure.prod parameterCircleMeasure
      Measurable M ∧ (∫⁻ ζ : ℍ, M ζ ∂flatArea) ≤ ENNReal.ofReal C ∧
        (∀ᵐ ζ : ℍ ∂flatArea, M ζ < ∞) ∧
        Integrable (fun ζ : ℍ => (M ζ).toReal) flatArea ∧
        (∫ ζ : ℍ, (M ζ).toReal ∂flatArea) ≤ C := by
  let : SigmaFinite flatArea := flatArea_sigmaFinite
  obtain ⟨ε₁, C, hε₁, hC, hbound⟩ :=
    canonicalBiparameterKernel_uniform_integrable R p hp qdir qtest K hK
  obtain ⟨ε₂, hε₂, hjoint⟩ := kernel_jointly_measurable R p hp qdir qtest
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  refine ⟨ε, C, hε, hC, ?_⟩
  intro r hr hrε z hz
  dsimp only
  let σ := parameterCircleMeasure.prod parameterCircleMeasure
  let H : (ℝ × ℝ) × ℍ → ℂ := fun x =>
    canonicalBiparameterKernelIntegrand R p qdir qtest
      (circleMap 0 r x.1.1) (circleMap 0 r x.1.2) z x.2
  let M := fun ζ : ℍ => ∫⁻ θφ : ℝ × ℝ, ‖H (θφ, ζ)‖ₑ ∂σ
  have hr₁ : r < ε₁ := hrε.trans_le (min_le_left _ _)
  have hr₂ : r < ε₂ := hrε.trans_le (min_le_right _ _)
  have hα₁ (θ : ℝ) : ‖circleMap 0 r θ‖ < ε₁ := by
    simpa only [norm_circleMap_zero, abs_of_pos hr] using hr₁
  have hHm : Measurable H :=
    kernel_boundary_jointly_measurable R p qdir qtest hr hr₂ hjoint z
  have hMi : Measurable M := hHm.enorm.lintegral_prod_left'
  have hL1 (θφ : ℝ × ℝ) : Integrable (fun ζ : ℍ => H (θφ, ζ)) flatArea := by
    have hi := (hbound (circleMap 0 r θφ.1) (circleMap 0 r θφ.2)
      (hα₁ θφ.1) (hα₁ θφ.2) z hz).1
    apply (UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff (μ := flatArea)
      (g := canonicalBiparameterKernelIntegrand R p qdir qtest
        (circleMap 0 r θφ.1) (circleMap 0 r θφ.2) z)).mp
    rw [map_flat_coe]
    exact hi
  have hnorm (θφ : ℝ × ℝ) : (∫ ζ : ℍ, ‖H (θφ, ζ)‖ ∂flatArea) ≤ C := by
    have hb := (hbound (circleMap 0 r θφ.1) (circleMap 0 r θφ.2)
      (hα₁ θφ.1) (hα₁ θφ.2) z hz).2
    have hi := UpperHalfPlane.measurableEmbedding_coe.integral_map (μ := flatArea)
      (fun ζ : ℂ => ‖canonicalBiparameterKernelIntegrand R p qdir qtest
        (circleMap 0 r θφ.1) (circleMap 0 r θφ.2) z ζ‖)
    rw [map_flat_coe] at hi
    exact hi ▸ hb
  have hinner (θφ : ℝ × ℝ) :
      (∫⁻ ζ : ℍ, ‖H (θφ, ζ)‖ₑ ∂flatArea) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hL1 θφ)]
    exact ENNReal.ofReal_le_ofReal (hnorm θφ)
  have hMbound : (∫⁻ ζ : ℍ, M ζ ∂flatArea) ≤ ENNReal.ofReal C := by
    calc
      (∫⁻ ζ : ℍ, M ζ ∂flatArea) =
          ∫⁻ θφ : ℝ × ℝ, ∫⁻ ζ : ℍ, ‖H (θφ, ζ)‖ₑ ∂flatArea ∂σ :=
        (lintegral_lintegral_swap hHm.enorm.aemeasurable).symm
      _ ≤ ∫⁻ _θφ : ℝ × ℝ, ENNReal.ofReal C ∂σ := lintegral_mono hinner
      _ = ENNReal.ofReal C := by simp only [lintegral_const, measure_univ, mul_one]
  have hfinite : ∀ᵐ ζ : ℍ ∂flatArea, M ζ < ∞ :=
    ae_lt_top' hMi.aemeasurable (hMbound.trans_lt ENNReal.ofReal_lt_top).ne
  have hm : Integrable (fun ζ : ℍ => (M ζ).toReal) flatArea :=
    integrable_toReal_of_lintegral_ne_top hMi.aemeasurable
      (hMbound.trans_lt ENNReal.ofReal_lt_top).ne
  refine ⟨hMi, hMbound, hfinite, hm, ?_⟩
  rw [integral_toReal hMi.aemeasurable hfinite]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hMbound).trans_eq
    (ENNReal.toReal_ofReal hC)

/-- A fixed double parameter circle gives an integrable common majorant and
two integrable linear coefficients for the same actual kernel. -/
theorem canonicalBiparameterKernel_common_ae_double_circle_control
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (qdir qtest : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (K : Set ℍ) (hK : IsCompact K) :
    ∃ E C : ℝ, 0 < E ∧ 0 ≤ C ∧
      Measurable (fun x : ball (0 : ℂ) E × (ball (0 : ℂ) E × (ℍ × ℍ)) =>
        canonicalBiparameterKernelIntegrand R p qdir qtest x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
      ∀ r : ℝ, 0 < r → r < E → ∀ z ∈ K,
      ∃ (m : ℍ → ℝ) (A₁ A₂ : ℍ → ℂ),
        (∀ ζ, 0 ≤ m ζ) ∧ Measurable m ∧ Integrable m flatArea ∧
        (∫ ζ : ℍ, m ζ ∂flatArea) ≤ C ∧
        Measurable A₁ ∧ Measurable A₂ ∧ Integrable A₁ flatArea ∧ Integrable A₂ flatArea ∧
        ∀ᵐ ζ : ℍ ∂flatArea, ‖A₁ ζ‖ ≤ m ζ / r ∧ ‖A₂ ζ‖ ≤ m ζ / r ∧
          ∀ s t : ℂ, ‖s‖ ≤ r / 2 → ‖t‖ ≤ r / 2 →
            ‖canonicalBiparameterKernelIntegrand R p qdir qtest s t z ζ‖ ≤ 4 * m ζ ∧
            ‖canonicalBiparameterKernelIntegrand R p qdir qtest s t z ζ -
              canonicalBiparameterKernelIntegrand R p qdir qtest 0 0 z ζ‖ ≤
                (4 / r) * (‖s‖ + ‖t‖) * m ζ ∧
            ‖canonicalBiparameterKernelIntegrand R p qdir qtest s t z ζ -
              canonicalBiparameterKernelIntegrand R p qdir qtest 0 0 z ζ -
                A₁ ζ * s - A₂ ζ * t‖ ≤ (2 / r ^ 2) * (‖s‖ + ‖t‖) ^ 2 * m ζ := by
  obtain ⟨E₁, C, hE₁, hC, hmean⟩ :=
    kernel_circle_average_integrable R p hp qdir qtest K hK
  obtain ⟨E₂, hE₂, hhol⟩ := kernel_separately_holomorphic R p hp qdir qtest
  obtain ⟨E₃, hE₃, hjoint⟩ := kernel_jointly_measurable R p hp qdir qtest
  have hboundary (r : ℝ) (hr : 0 < r) (hrE : r < E₃) (z : ℍ) :
      Measurable (fun x : (ℝ × ℝ) × ℍ =>
        canonicalBiparameterKernelIntegrand R p qdir qtest
          (circleMap 0 r x.1.1) (circleMap 0 r x.1.2) z x.2) :=
    kernel_boundary_jointly_measurable R p qdir qtest hr hrE hjoint z
  generalize hkernel : canonicalBiparameterKernelIntegrand R p qdir qtest = g at *
  let E := min E₁ (min E₂ E₃)
  have hE : 0 < E := lt_min hE₁ (lt_min hE₂ hE₃)
  have hE₃' : E ≤ E₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hinc : Measurable (fun s : ball (0 : ℂ) E =>
      (⟨(s : ℂ), ball_subset_ball hE₃' s.property⟩ : ball (0 : ℂ) E₃)) :=
    measurable_subtype_coe.subtype_mk
  have hEm : Measurable
      (fun x : ball (0 : ℂ) E × (ball (0 : ℂ) E × (ℍ × ℍ)) =>
        g x.1 x.2.1 x.2.2.1 x.2.2.2) :=
    hjoint.comp ((hinc.comp measurable_fst).prodMk
      ((hinc.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)))
  refine ⟨E, C, hE, hC, hEm, ?_⟩
  intro r hr hrE z hz
  have hr₁ : r < E₁ := hrE.trans_le (min_le_left _ _)
  have hr₂ : r < E₂ := hrE.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hr₃ : r < E₃ := hrE.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let σ := parameterCircleMeasure.prod parameterCircleMeasure
  let H : (ℝ × ℝ) × ℍ → ℂ := fun x =>
    g
      (circleMap 0 r x.1.1) (circleMap 0 r x.1.2) z x.2
  let M := fun ζ : ℍ => ∫⁻ θφ : ℝ × ℝ, ‖H (θφ, ζ)‖ₑ ∂σ
  let m := fun ζ : ℍ => (M ζ).toReal
  let A₁ := fun ζ : ℍ => ∫ θφ : ℝ × ℝ,
    H (θφ, ζ) / circleMap 0 r θφ.1 ∂σ
  let A₂ := fun ζ : ℍ => ∫ θφ : ℝ × ℝ,
    H (θφ, ζ) / circleMap 0 r θφ.2 ∂σ
  obtain ⟨hMm, _hMbound, hMfinite, hm, hmC⟩ := hmean r hr hr₁ z hz
  have hHm : Measurable H :=
    hboundary r hr hr₃ z
  have hAm₁ : Measurable A₁ :=
    (hHm.div ((continuous_circleMap 0 r).measurable.comp
      (measurable_fst.comp measurable_fst))).stronglyMeasurable.integral_prod_left'.measurable
  have hAm₂ : Measurable A₂ :=
    (hHm.div ((continuous_circleMap 0 r).measurable.comp
      (measurable_snd.comp measurable_fst))).stronglyMeasurable.integral_prod_left'.measurable
  have hexpand : ∀ᵐ ζ : ℍ ∂flatArea,
      ‖A₁ ζ‖ ≤ m ζ / r ∧ ‖A₂ ζ‖ ≤ m ζ / r ∧
      ∀ s t : ℂ, ‖s‖ ≤ r / 2 → ‖t‖ ≤ r / 2 →
        ‖g s t z ζ‖ ≤ 4 * m ζ ∧
        ‖g s t z ζ -
          g 0 0 z ζ‖ ≤
            (4 / r) * (‖s‖ + ‖t‖) * m ζ ∧
        ‖g s t z ζ -
          g 0 0 z ζ -
            A₁ ζ * s - A₂ ζ * t‖ ≤ (2 / r ^ 2) * (‖s‖ + ‖t‖) ^ 2 * m ζ := by
    filter_upwards [hMfinite] with ζ hζ
    have hBm : Measurable (fun θφ : ℝ × ℝ => H (θφ, ζ)) :=
      hHm.comp (measurable_id.prodMk measurable_const)
    have hB : Integrable (fun θφ : ℝ × ℝ => H (θφ, ζ)) σ := by
      refine ⟨hBm.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      exact hζ
    have hnorm : (∫ θφ : ℝ × ℝ, ‖H (θφ, ζ)‖ ∂σ) = m ζ :=
      integral_norm_eq_lintegral_enorm hBm.aestronglyMeasurable
    have hex := parameterCircle_double_expansion hr hr₂ (hhol z ζ).1 (hhol z ζ).2 hB
    dsimp only [H, σ] at hnorm
    simpa only [A₁, A₂, H, σ, hnorm] using hex
  have hAi₁ : Integrable A₁ flatArea := (hm.div_const r).mono'
    hAm₁.aestronglyMeasurable (hexpand.mono (fun _ h => h.1))
  have hAi₂ : Integrable A₂ flatArea := (hm.div_const r).mono'
    hAm₂.aestronglyMeasurable (hexpand.mono (fun _ h => h.2.1))
  exact ⟨m, A₁, A₂, fun _ => ENNReal.toReal_nonneg, hMm.ennreal_toReal,
    hm, hmC, hAm₁, hAm₂, hAi₁, hAi₂, hexpand⟩

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
