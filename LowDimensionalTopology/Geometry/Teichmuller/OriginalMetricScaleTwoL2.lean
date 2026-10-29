module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricScaleTwoArea
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalTensorL2PositiveBilinear

/-!
# The two original L2 comparisons for doubling a metric

Fixed original tensors have half their old integral: the area doubles and
the pointwise contraction is quartered. When the actual two sections are
also doubled, the original positive bilinear integral instead doubles.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Manifold ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The real scalar action already inherited from the same native symmetric-tensor submodule. -/
local instance canonicalScaleTwoL2TensorSMul : SMul ℝ (SmoothSymmetricTwoTensor R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact Submodule.smul (symmetricTwoTensorSubmodule R)

/-- With the same two original tensor sections fixed, the actual doubled
metric has half the original native L2 integral. -/
theorem metricTensorL2Pairing_scaleTwo
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R g)
    (harea₂ : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R
      (scaleTwoOriginalMetric R g))
    (h k : SmoothSymmetricTwoTensor R) :
    metricTensorL2Pairing R (scaleTwoOriginalMetric R g) harea₂ h k =
      (1 / 2 : ℝ) * metricTensorL2Pairing R g harea h k := by
  let : MeasurableSpace X := borel X
  let μ : Measure X := harea.exists.choose
  let μ₂ : Measure X := harea₂.exists.choose
  have hμ : μ₂ = (2 : ℝ≥0∞) • μ := originalMetricArea_scaleTwo R g harea harea₂
  have hf : metricTensorPointwisePairing R (scaleTwoOriginalMetric R g) h k =
      fun x => (1 / 4 : ℝ) * metricTensorPointwisePairing R g h k x :=
    funext (fun x => metricTensorPointwisePairing_scaleTwo R g h k x)
  change (∫ x, metricTensorPointwisePairing R (scaleTwoOriginalMetric R g) h k x ∂μ₂) =
    (1 / 2 : ℝ) * ∫ x, metricTensorPointwisePairing R g h k x ∂μ
  rw [hμ, integral_smul_measure, hf, integral_const_mul]
  have hc : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [hc]
  let value : ℝ := ∫ x, metricTensorPointwisePairing R g h k x ∂μ
  change (2 : ℝ) * ((1 / 4 : ℝ) * value) = (1 / 2 : ℝ) * value
  ring

/-- Under the concrete doubling of both original sections, the actual
metric-doubling comparison has factor two rather than one half. -/
theorem metricTensorL2Pairing_scaleTwo_pullback
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R g)
    (harea₂ : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R
      (scaleTwoOriginalMetric R g))
    (h k : SmoothSymmetricTwoTensor R) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    metricTensorL2Pairing R (scaleTwoOriginalMetric R g) harea₂
        ((2 : ℝ) • h : SmoothSymmetricTwoTensor R)
        ((2 : ℝ) • k : SmoothSymmetricTwoTensor R) =
      2 * metricTensorL2Pairing R g harea h k := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  obtain ⟨B, hB, _, _, _⟩ := exists_metricTensorL2BilinForm R g harea
  have hdouble : metricTensorL2Pairing R g harea
        ((2 : ℝ) • h : SmoothSymmetricTwoTensor R)
        ((2 : ℝ) • k : SmoothSymmetricTwoTensor R) =
      4 * metricTensorL2Pairing R g harea h k := by
    calc
      metricTensorL2Pairing R g harea
          ((2 : ℝ) • h : SmoothSymmetricTwoTensor R)
          ((2 : ℝ) • k : SmoothSymmetricTwoTensor R) =
        B ((2 : ℝ) • h : SmoothSymmetricTwoTensor R)
          ((2 : ℝ) • k : SmoothSymmetricTwoTensor R) := (hB _ _).symm
      _ = 4 * B h k := by
        rw [LinearMap.map_smul B, LinearMap.smul_apply, LinearMap.map_smul (B h)]
        change (2 : ℝ) * (2 * B h k) = 4 * B h k
        ring
      _ = 4 * metricTensorL2Pairing R g harea h k := by rw [hB h k]
  calc
    metricTensorL2Pairing R (scaleTwoOriginalMetric R g) harea₂
        ((2 : ℝ) • h : SmoothSymmetricTwoTensor R)
        ((2 : ℝ) • k : SmoothSymmetricTwoTensor R) =
      (1 / 2 : ℝ) * metricTensorL2Pairing R g harea
        ((2 : ℝ) • h : SmoothSymmetricTwoTensor R)
        ((2 : ℝ) • k : SmoothSymmetricTwoTensor R) :=
      metricTensorL2Pairing_scaleTwo R g harea harea₂ _ _
    _ = 2 * metricTensorL2Pairing R g harea h k := by
      rw [hdouble]
      ring

end LowDimensionalTopology.Geometry.Teichmuller
