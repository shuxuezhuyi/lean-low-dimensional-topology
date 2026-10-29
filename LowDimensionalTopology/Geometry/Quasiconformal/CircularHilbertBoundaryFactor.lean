module

public import LowDimensionalTopology.External.LiZhongQC.Ch02.S11_IntegralOperators

/-!
# The boundary factor for an inverse-norm convolution

The normalized inverse distance on a growing circle tends uniformly to
one. An explicit estimate controls its angular integral and the complex
coefficient that occurs after differentiating a rescaled disc integral.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The normalized inverse distance from `1` to a circle of radius `r`. -/
def inverseNormBoundaryFactor (r θ : ℝ) : ℝ :=
  r / ‖(1 : ℂ) - circleMap 0 r θ‖

private theorem inverseNormBoundaryFactor_denominator_pos {r : ℝ} (hr : 1 < r)
    (θ : ℝ) : 0 < ‖(1 : ℂ) - circleMap 0 r θ‖ := by
  have h := norm_sub_norm_le (circleMap 0 r θ) (1 : ℂ)
  rw [norm_circleMap_zero, abs_of_pos (by linarith : 0 < r), norm_one,
    norm_sub_rev] at h
  linarith

/-- A bound independent of the angular parameter. -/
theorem abs_inverseNormBoundaryFactor_sub_one_le {r : ℝ} (hr : 1 < r) (θ : ℝ) :
    |inverseNormBoundaryFactor r θ - 1| ≤ 1 / (r - 1) := by
  let d : ℝ := ‖(1 : ℂ) - circleMap 0 r θ‖
  have hr0 : 0 < r := by linarith
  have hd : 0 < d := inverseNormBoundaryFactor_denominator_pos hr θ
  have hlo : r - 1 ≤ d := by
    dsimp only [d]
    have h := norm_sub_norm_le (circleMap 0 r θ) (1 : ℂ)
    rw [norm_circleMap_zero, abs_of_pos hr0, norm_one, norm_sub_rev] at h
    exact h
  have hhi : d ≤ 1 + r := by
    simpa only [d, norm_one, norm_circleMap_zero, abs_of_pos hr0] using
      norm_sub_le (1 : ℂ) (circleMap 0 r θ)
  have herr : |r - d| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have heq : inverseNormBoundaryFactor r θ - 1 = (r - d) / d := by
    dsimp [inverseNormBoundaryFactor, d]
    field_simp [ne_of_gt (inverseNormBoundaryFactor_denominator_pos hr θ)]
  rw [heq, abs_div, abs_of_pos hd]
  calc
    |r - d| / d ≤ 1 / d := div_le_div_of_nonneg_right herr hd.le
    _ ≤ 1 / (r - 1) := one_div_le_one_div_of_le (by linarith) hlo

theorem continuous_inverseNormBoundaryFactor {r : ℝ} (hr : 1 < r) :
    Continuous (inverseNormBoundaryFactor r) := by
  exact continuous_const.div ((continuous_const.sub (continuous_circleMap 0 r)).norm)
    (fun θ => ne_of_gt (inverseNormBoundaryFactor_denominator_pos hr θ))

/-- Integrating the angular error gives an explicit bound tending to zero. -/
theorem abs_integral_inverseNormBoundaryFactor_sub_two_pi_le {r : ℝ} (hr : 1 < r) :
    |(∫ θ in (0 : ℝ)..(2 * Real.pi), inverseNormBoundaryFactor r θ) - 2 * Real.pi|
      ≤ 2 * Real.pi / (r - 1) := by
  have hi : IntervalIntegrable (inverseNormBoundaryFactor r) volume
      (0 : ℝ) (2 * Real.pi) :=
    (continuous_inverseNormBoundaryFactor hr).intervalIntegrable _ _
  have heq : (∫ θ in (0 : ℝ)..(2 * Real.pi), inverseNormBoundaryFactor r θ) - 2 * Real.pi =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), inverseNormBoundaryFactor r θ - 1 := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  rw [heq]
  calc
    |∫ θ in (0 : ℝ)..(2 * Real.pi), inverseNormBoundaryFactor r θ - 1| ≤
        (1 / (r - 1)) * |2 * Real.pi - 0| := by
      have hb (θ : ℝ) : ‖inverseNormBoundaryFactor r θ - 1‖ ≤ 1 / (r - 1) := by
        rw [Real.norm_eq_abs]
        exact abs_inverseNormBoundaryFactor_sub_one_le hr θ
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 2 * Real.pi) (C := 1 / (r - 1))
        (f := fun θ : ℝ => inverseNormBoundaryFactor r θ - 1) (fun θ _ => hb θ)
      simpa only [Real.norm_eq_abs] using h
    _ = 2 * Real.pi / (r - 1) := by
      rw [sub_zero, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      ring

/-- The normalized angular integral tends to the circumference of the
unit circle. -/
theorem tendsto_integral_inverseNormBoundaryFactor :
    Tendsto (fun r : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi), inverseNormBoundaryFactor r θ)
      atTop (𝓝 (2 * Real.pi)) := by
  have hden : Tendsto (fun r : ℝ => r - 1) atTop atTop := by
    simpa only [id, sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
  have hzero : Tendsto (fun r : ℝ => (2 * Real.pi) / (r - 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have herr : ∀ᶠ r : ℝ in atTop,
      ‖(∫ θ in (0 : ℝ)..(2 * Real.pi), inverseNormBoundaryFactor r θ) - 2 * Real.pi‖ ≤
        2 * Real.pi / (r - 1) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    simpa only [Real.norm_eq_abs] using
      abs_integral_inverseNormBoundaryFactor_sub_two_pi_le hr
  have h := (squeeze_zero_norm' herr hzero).add_const (2 * Real.pi)
  simpa only [sub_add_cancel, zero_add] using h

/-- The boundary coefficient after translating a pole and rescaling its
distance to the evaluation point. -/
def inverseNormBoundaryCoefficient (a : ℂ) (R : ℝ) : ℂ :=
  -(1 / (2 * a)) *
    ((∫ θ in (0 : ℝ)..(2 * Real.pi), inverseNormBoundaryFactor (R / ‖a‖) θ) : ℂ)

/-- The explicit coefficient has the required limit at each nonzero
distance from the translated pole. -/
theorem tendsto_inverseNormBoundaryCoefficient {a : ℂ} (ha : a ≠ 0) :
    Tendsto (inverseNormBoundaryCoefficient a) atTop (𝓝 (-(Real.pi : ℂ) / a)) := by
  have hr : Tendsto (fun R : ℝ => R / ‖a‖) atTop atTop :=
    tendsto_id.atTop_div_const (norm_pos_iff.mpr ha)
  have h := tendsto_integral_inverseNormBoundaryFactor.comp hr
  have hC := (Complex.continuous_ofReal.tendsto (2 * Real.pi)).comp h
  convert! hC.const_mul (-(1 / (2 * a))) using 1
  · funext R
    simp only [inverseNormBoundaryCoefficient, Function.comp_def, intervalIntegral.integral_ofReal]
  · congr 1
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

end LowDimensionalTopology.Geometry.Quasiconformal
