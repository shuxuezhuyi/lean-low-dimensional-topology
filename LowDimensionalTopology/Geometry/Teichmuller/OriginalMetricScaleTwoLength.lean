module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricScaleTwoPointwise

/-!
# Length elements under doubling the original metric

The comparison is on the same original tangent vector. It does not require
a separate path-length or distance construction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- Doubling the metric multiplies the length of each original tangent vector
by the square root of two. -/
theorem scaleTwoOriginalMetric_length_element
    (g : SmoothSurfaceMetric R.toRiemannSurface) (x : X)
    (v : RealSurfaceTangent R.toRiemannSurface x) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    Real.sqrt ((scaleTwoOriginalMetric R g).inner x v v) =
      Real.sqrt 2 * Real.sqrt (g.inner x v v) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  rw [scaleTwoOriginalMetric_inner R g x v v]
  exact Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (g.inner x v v)

end LowDimensionalTopology.Geometry.Teichmuller
