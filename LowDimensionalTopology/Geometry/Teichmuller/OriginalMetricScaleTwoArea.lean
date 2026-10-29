module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricScaleTwoPointwise
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure

/-!
# The prescribed original area of twice an original metric

The two area inputs are instances of the existing exact finite-area premise.
Twice the original measure satisfies the doubled metric's actual chart law;
its already prescribed uniqueness identifies the chosen doubled area.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Manifold ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

private theorem gram_scaleTwo
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (e : OriginalComplexChart R.toRiemannSurface) (x : X) :
    metricGramInChart (scaleTwoOriginalMetric R g) e x =
      (2 : ℝ) • metricGramInChart g e x := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  by_cases hx : x ∈ e.val.source
  · rw [metricGramInChart_eq (scaleTwoOriginalMetric R g) e x hx,
      metricGramInChart_eq g e x hx]
    ext a b
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
    simpa only [metricGramForm, ContinuousLinearMap.bilinearComp_apply,
      smul_apply, smul_eq_mul, D,
      ContinuousLinearEquiv.coe_coe] using
      (scaleTwoOriginalMetric_inner R g x (D.symm a) (D.symm b))
  · simp only [metricGramInChart, dite_eq_right hx]
    ext a b
    change (0 : ℝ) = 2 * 0
    ring

private def chartAreaDensity
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (e : OriginalComplexChart R.toRiemannSurface) (z : ℂ) : ℝ≥0∞ :=
  let B := metricGramInChart g e (e.val.symm z)
  ENNReal.ofReal (Real.sqrt
    (B 1 1 * B Complex.I Complex.I - (B 1 Complex.I) ^ 2))

private theorem density_scaleTwo
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (e : OriginalComplexChart R.toRiemannSurface) (z : ℂ) :
    chartAreaDensity R (scaleTwoOriginalMetric R g) e z =
      (2 : ℝ≥0∞) * chartAreaDensity R g e z := by
  let B := metricGramInChart g e (e.val.symm z)
  have hcoef (a b : ℂ) :
      metricGramInChart (scaleTwoOriginalMetric R g) e (e.val.symm z) a b =
        2 * B a b := by
    simpa only [B, smul_apply, smul_eq_mul] using
      congrArg (fun L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ => L a b)
        (gram_scaleTwo R g e (e.val.symm z))
  change ENNReal.ofReal (Real.sqrt
      (metricGramInChart (scaleTwoOriginalMetric R g) e (e.val.symm z) 1 1 *
        metricGramInChart (scaleTwoOriginalMetric R g) e (e.val.symm z)
          Complex.I Complex.I -
        (metricGramInChart (scaleTwoOriginalMetric R g) e (e.val.symm z)
          1 Complex.I) ^ 2)) =
    (2 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt
      (B 1 1 * B Complex.I Complex.I - (B 1 Complex.I) ^ 2))
  rw [hcoef 1 1, hcoef Complex.I Complex.I, hcoef 1 Complex.I]
  have hdet : (2 * B 1 1) * (2 * B Complex.I Complex.I) -
      (2 * B 1 Complex.I) ^ 2 =
      (2 : ℝ) ^ 2 * (B 1 1 * B Complex.I Complex.I - (B 1 Complex.I) ^ 2) := by
    ring
  have hs : Real.sqrt ((2 * B 1 1) * (2 * B Complex.I Complex.I) -
      (2 * B 1 Complex.I) ^ 2) =
      2 * Real.sqrt (B 1 1 * B Complex.I Complex.I - (B 1 Complex.I) ^ 2) := by
    rw [hdet, Real.sqrt_mul (sq_nonneg (2 : ℝ)), Real.sqrt_sq (by norm_num)]
  rw [hs, ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- The exact prescribed areas of g and its actual double satisfy μ₂ = 2μ
on the same original Borel carrier. -/
theorem originalMetricArea_scaleTwo
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R g)
    (harea₂ : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R
      (scaleTwoOriginalMetric R g)) :
    letI : MeasurableSpace X := borel X
    harea₂.exists.choose = (2 : ℝ≥0∞) • harea.exists.choose := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let μ : Measure X := harea.exists.choose
  let : IsFiniteMeasure μ := harea.exists.choose_spec.1
  have hfinite : IsFiniteMeasure ((2 : ℝ≥0∞) • μ) := by
    constructor
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top μ Set.univ)
  have hcandidate : IsFiniteMeasure ((2 : ℝ≥0∞) • μ) ∧
      ∀ p : X,
        let e : OriginalComplexChart R.toRiemannSurface :=
          ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
        Measure.map (e.val : X → ℂ) (((2 : ℝ≥0∞) • μ).restrict e.val.source) =
          ((volume : Measure ℂ).withDensity
            (chartAreaDensity R (scaleTwoOriginalMetric R g) e)).restrict e.val.target := by
    refine ⟨hfinite, ?_⟩
    intro p
    let e : OriginalComplexChart R.toRiemannSurface :=
      ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
    have hmap : Measure.map (e.val : X → ℂ) (μ.restrict e.val.source) =
        ((volume : Measure ℂ).withDensity (chartAreaDensity R g e)).restrict e.val.target :=
      harea.exists.choose_spec.2 p
    have hmeas : AEMeasurable (e.val : X → ℂ) (μ.restrict e.val.source) :=
      e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
    change Measure.map (e.val : X → ℂ) (((2 : ℝ≥0∞) • μ).restrict e.val.source) =
      ((volume : Measure ℂ).withDensity
        (chartAreaDensity R (scaleTwoOriginalMetric R g) e)).restrict e.val.target
    rw [Measure.restrict_smul, Measure.map_smul (2 : ℝ≥0∞) hmeas, hmap]
    have hdensity : chartAreaDensity R (scaleTwoOriginalMetric R g) e =
        (2 : ℝ≥0∞) • chartAreaDensity R g e := by
      funext z
      exact density_scaleTwo R g e z
    rw [hdensity, withDensity_smul' (2 : ℝ≥0∞) _ (by norm_num),
      Measure.restrict_smul]
  change harea₂.exists.choose = (2 : ℝ≥0∞) • μ
  exact harea₂.unique harea₂.exists.choose_spec hcandidate

end LowDimensionalTopology.Geometry.Teichmuller
