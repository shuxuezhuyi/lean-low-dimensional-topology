module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricTensorDivergence
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricTensorTrace

/-! # The original transverse-traceless tensor set -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- All original smooth symmetric tensors with zero native trace and zero
whole native divergence covector, for the same arbitrary original metric. -/
def transverseTracelessTensors
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u}) :
    Set (SmoothSymmetricTwoTensor R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact {h | (∀ x : X, metricTensorTrace R g h x = 0) ∧
    ∀ x : X, (metricTensorDivergence R g hdiv h).toFun x = 0}

/-- Membership is exactly the two original pointwise zero conditions. -/
theorem mem_transverseTracelessTensors_iff
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u})
    (h : SmoothSymmetricTwoTensor R) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    h ∈ transverseTracelessTensors R g hdiv ↔
      (∀ x : X, metricTensorTrace R g h x = 0) ∧
        ∀ x : X, (metricTensorDivergence R g hdiv h).toFun x = 0 :=
  Iff.rfl

end LowDimensionalTopology.Geometry.Teichmuller
