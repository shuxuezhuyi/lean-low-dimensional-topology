module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricTensorPairing

/-!
# Doubling an original metric and its fixed-tensor contraction

The metric is doubled on the unchanged original tangent fibres. Its smooth
certificate is the existing native symmetric-tensor scalar multiple. Raising
one index is halved, so the contraction of two fixed original tensors is
one quarter of the original contraction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The real scalar action already inherited from the same native symmetric-tensor submodule. -/
local instance canonicalNativeS2SMul : SMul ℝ (SmoothSymmetricTwoTensor R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact Submodule.smul (symmetricTwoTensorSubmodule R)

/-- Twice the given actual metric on the same original tangent bundle. -/
def scaleTwoOriginalMetric (g : SmoothSurfaceMetric R.toRiemannSurface) :
    SmoothSurfaceMetric R.toRiemannSurface := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let s : SmoothSymmetricTwoTensor R :=
    (2 : ℝ) • SmoothSurfaceMetric.toSymmetricTwoTensor R g
  refine
    { inner := s.val.toFun
      symm := ?_
      pos := ?_
      isVonNBounded := ?_
      contMDiff := s.val.contMDiff_toFun }
  · intro x v w
    change 2 * g.inner x v w = 2 * g.inner x w v
    rw [g.symm x v w]
  · intro x v hv
    change 0 < 2 * g.inner x v v
    exact mul_pos (by norm_num) (g.pos x v hv)
  · intro x
    refine Bornology.IsVonNBounded.subset ?_ (g.isVonNBounded x)
    intro v hv
    change 2 * g.inner x v v < 1 at hv
    change g.inner x v v < 1
    linarith

/-- The doubled metric has exactly twice every original bilinear value. -/
theorem scaleTwoOriginalMetric_inner
    (g : SmoothSurfaceMetric R.toRiemannSurface) (x : X)
    (v w : RealSurfaceTangent R.toRiemannSurface x) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    (scaleTwoOriginalMetric R g).inner x v w = 2 * g.inner x v w := by
  rfl

private theorem raised_scaleTwo
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (h : SmoothSymmetricTwoTensor R) (x : X) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    metricRaisedTensor R (scaleTwoOriginalMetric R g) h x =
      (1 / 2 : ℝ) • metricRaisedTensor R g h x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change metricRaisedTensor R (scaleTwoOriginalMetric R g) h x =
    (1 / 2 : ℝ) • metricRaisedTensor R g h x
  apply LinearMap.ext
  intro v
  change metricRaisedTensor R (scaleTwoOriginalMetric R g) h x v =
    (1 / 2 : ℝ) • metricRaisedTensor R g h x v
  apply sub_eq_zero.mp
  apply (metricForm_nondegenerate R g x).1
  intro w
  change g.inner x
    (metricRaisedTensor R (scaleTwoOriginalMetric R g) h x v -
      (1 / 2 : ℝ) • metricRaisedTensor R g h x v) w = 0
  have hs := metricRaisedTensor_spec R (scaleTwoOriginalMetric R g) h x v w
  rw [scaleTwoOriginalMetric_inner R g x] at hs
  have ht := metricRaisedTensor_spec R g h x v w
  rw [map_sub, sub_apply, map_smul, smul_apply]
  change g.inner x (metricRaisedTensor R (scaleTwoOriginalMetric R g) h x v) w -
    (1 / 2 : ℝ) * g.inner x (metricRaisedTensor R g h x v) w = 0
  linarith [hs, ht]

/-- With both original tensors fixed, doubling the actual metric divides
its double contraction by four. -/
theorem metricTensorPointwisePairing_scaleTwo
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (h k : SmoothSymmetricTwoTensor R) (x : X) :
    metricTensorPointwisePairing R (scaleTwoOriginalMetric R g) h k x =
      (1 / 4 : ℝ) * metricTensorPointwisePairing R g h k x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let V := TangentSpace 𝓘(ℝ, ℂ) x
  change LinearMap.trace ℝ V
      ((metricRaisedTensor R (scaleTwoOriginalMetric R g) h x).comp
        (metricRaisedTensor R (scaleTwoOriginalMetric R g) k x)) =
    (1 / 4 : ℝ) * LinearMap.trace ℝ V
      ((metricRaisedTensor R g h x).comp (metricRaisedTensor R g k x))
  rw [raised_scaleTwo R g h x, raised_scaleTwo R g k x,
    LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, map_smul]
  change ((1 / 2 : ℝ) * (1 / 2 : ℝ)) *
      LinearMap.trace ℝ V
        ((metricRaisedTensor R g h x).comp (metricRaisedTensor R g k x)) =
    (1 / 4 : ℝ) * LinearMap.trace ℝ V
      ((metricRaisedTensor R g h x).comp (metricRaisedTensor R g k x))
  ring

end LowDimensionalTopology.Geometry.Teichmuller
