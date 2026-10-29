module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricTensorTrace
public import Mathlib.LinearAlgebra.Trace

/-!
# Pointwise contraction of original symmetric tensors

Raise one index of each tensor with the same original metric, compose the
two resulting endomorphisms of the original real tangent fibre, and take
their ordinary linear trace.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The pointwise contraction using the inverse metric in both covariant slots. -/
def metricTensorPointwisePairing (g : SmoothSurfaceMetric R.toRiemannSurface)
    (ξ η : SmoothSymmetricTwoTensor R) : X → ℝ :=
  fun x => LinearMap.trace ℝ (RealSurfaceTangent R.toRiemannSurface x)
    ((metricRaisedTensor R g ξ x).comp (metricRaisedTensor R g η x))

/-- The metric contraction is symmetric in the two original tensors. -/
theorem metricTensorPointwisePairing_symm (g : SmoothSurfaceMetric R.toRiemannSurface)
    (ξ η : SmoothSymmetricTwoTensor R) (x : X) :
    metricTensorPointwisePairing R g ξ η x = metricTensorPointwisePairing R g η ξ x := by
  exact LinearMap.trace_comp_comm'
    (metricRaisedTensor R g η x) (metricRaisedTensor R g ξ x)

end LowDimensionalTopology.Geometry.Teichmuller
