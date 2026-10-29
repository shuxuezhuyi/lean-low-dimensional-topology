module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalSymmetricTensors
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Trace

/-!
# Trace of an original covariant tensor relative to a metric

The positive metric identifies each original real tangent space with its
dual. Raising the first index of a covariant tensor gives an endomorphism
of that same tangent space; its ordinary linear trace is the metric trace.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- Positivity makes the original metric nondegenerate on every real tangent fibre. -/
theorem metricForm_nondegenerate
    (g : SmoothSurfaceMetric R.toRiemannSurface) (x : X) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ((g.inner x).toLinearMap₁₂).Nondegenerate := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  constructor
  · intro v hv
    by_contra hne
    exact (ne_of_gt (g.pos x v hne)) (hv v)
  · intro v hv
    by_contra hne
    exact (ne_of_gt (g.pos x v hne)) (hv v)

/-- Raise one index using the given metric on the unchanged real tangent fibre. -/
def metricRaisedTensor (g : SmoothSurfaceMetric R.toRiemannSurface)
    (h : SmoothSymmetricTwoTensor R) (x : X) :
    RealSurfaceTangent R.toRiemannSurface x →ₗ[ℝ]
      RealSurfaceTangent R.toRiemannSurface x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact LinearMap.BilinForm.symmCompOfNondegenerate
    (h.val.toFun x).toLinearMap₁₂ (g.inner x).toLinearMap₁₂
    (metricForm_nondegenerate R g x)

/-- The raised endomorphism is exactly the metric inverse composed with the tensor. -/
theorem metricRaisedTensor_spec (g : SmoothSurfaceMetric R.toRiemannSurface)
    (h : SmoothSymmetricTwoTensor R) (x : X)
    (v w : RealSurfaceTangent R.toRiemannSurface x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    g.inner x (metricRaisedTensor R g h x v) w = h.val.toFun x v w := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact LinearMap.BilinForm.symmCompOfNondegenerate_left_apply
    (h.val.toFun x).toLinearMap₁₂ (metricForm_nondegenerate R g x) w v

/-- The pointwise scalar trace of a symmetric covariant tensor relative to a metric. -/
def metricTensorTrace (g : SmoothSurfaceMetric R.toRiemannSurface)
    (h : SmoothSymmetricTwoTensor R) : X → ℝ :=
  fun x => LinearMap.trace ℝ (RealSurfaceTangent R.toRiemannSurface x)
    (metricRaisedTensor R g h x)

end LowDimensionalTopology.Geometry.Teichmuller
