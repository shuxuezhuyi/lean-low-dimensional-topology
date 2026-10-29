module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalSmoothMetricGaussianCurvature

/-!
# Gaussian log-density covariance for the same original metric

An actual isothermal realization consists of a smooth marking and a compatible
positive metric whose full native pullback is the given original metric. The
classical input transports the chosen curvature coordinate law to every such
realization on the existing homeomorphic copy of the original carrier.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller
open scoped Manifold ContDiff
universe u

/-- The Gaussian log-density law is unchanged by an actual compatible
isothermal realization of the same full original metric. This input contains
no metric rescaling equation or assertion about a curvature level set. -/
def OriginalMetricGaussianCurvatureCovariance : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (R : ClosedRiemannSurface X)
      (hreg : Quasiconformal.SmoothCompactBeltramiRegularity)
      (g : SmoothSurfaceMetric R.toRiemannSurface) (K : X → ℝ),
    HasMetricGaussianCurvatureCoordinates R hreg g K →
      ∀ (S : RiemannSurface (ULift.{0} X))
        (f : SmoothSurfaceEquiv R.toRiemannSurface S)
        (G : AtlasInducedMetric S),
        letI := R.toRiemannAtlas.toChartedSpace
        letI := R.toRiemannAtlas.isRealManifold
        letI := S.toRiemannAtlas.toChartedSpace
        letI := S.toRiemannAtlas.isRealManifold
        (∀ (x : X) (v w : RealSurfaceTangent R.toRiemannSurface x),
          G.metric.inner (f.toHomeomorph x)
              (surfaceDifferential R.toRiemannSurface S f x v)
              (surfaceDifferential R.toRiemannSurface S f x w) =
            g.inner x v w) →
        ∀ (e : OriginalComplexChart S) (z : ℂ), z ∈ e.val.target →
          let ell : ℂ → ℝ := fun a => Real.log (G.density e (e.val.symm a))
          let lap : ℝ :=
            fderiv ℝ (fun a => fderiv ℝ ell a 1) z 1 +
            fderiv ℝ (fun a => fderiv ℝ ell a Complex.I) z Complex.I
          K ((SmoothSurfaceEquiv.symm f).toHomeomorph (e.val.symm z)) =
            -lap / (2 * G.density e (e.val.symm z))

end LowDimensionalTopology.Unproved.Teichmuller
