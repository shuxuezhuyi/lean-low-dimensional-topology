module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricTensorPairing
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The original tensor integral for the prescribed metric-area measure

The area existence input fixes the unique finite Borel measure by the metric's
actual preferred-chart densities. The integrand is the original contraction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces MeasureTheory
universe u

/-- Integrate the actual contraction against the uniquely prescribed native metric area. -/
def metricTensorL2Pairing {X : Type u} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) (g : SmoothSurfaceMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R g)
    (ξ η : SmoothSymmetricTwoTensor R) : ℝ := by
  letI : MeasurableSpace X := borel X
  let μ : Measure X := harea.exists.choose
  exact ∫ x : X, metricTensorPointwisePairing R g ξ η x ∂μ

end LowDimensionalTopology.Geometry.Teichmuller
