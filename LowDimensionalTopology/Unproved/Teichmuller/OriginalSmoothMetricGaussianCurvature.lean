module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricIsothermalRealization
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Gaussian curvature from the same original metric's isothermal coordinates

The missing classical input is existence of a smooth global function for the
ordinary log-density formula. The native isothermal target and its marking
are already constructed from the entire original metric. No existence of a
metric with a prescribed curvature is included in this input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff
universe u

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

/-- The Gaussian log-density law in every genuine isothermal target chart.
The positive density is that of the same transported original metric. Only
points in the open target are evaluated, so totalizations outside it do not
change either derivative at a valid point. -/
def HasMetricGaussianCurvatureCoordinates
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (hreg : Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R.toRiemannSurface) (K : X → ℝ) : Prop :=
  let S := rawMetricIsothermalSurface R.toRiemannSurface hreg g
  let f := rawMetricIsothermalMarking R.toRiemannSurface hreg g
  let G := rawMetricIsothermalTargetMetric R.toRiemannSurface hreg g
  ∀ (e : OriginalComplexChart S) (z : ℂ), z ∈ e.val.target →
    let ell : ℂ → ℝ := fun w => Real.log (G.density e (e.val.symm w))
    let lap : ℝ :=
      fderiv ℝ (fun w => fderiv ℝ ell w 1) z 1 +
      fderiv ℝ (fun w => fderiv ℝ ell w Complex.I) z Complex.I
    K ((SmoothSurfaceEquiv.symm f).toHomeomorph (e.val.symm z)) =
      -lap / (2 * G.density e (e.val.symm z))

end LowDimensionalTopology.Geometry.Teichmuller

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller

/-- Every original smooth metric has a smooth Gaussian curvature function
prescribed by its actual isothermal-coordinate formula. -/
def OriginalSmoothMetricGaussianCurvature : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (R : ClosedRiemannSurface X)
      (hreg : Quasiconformal.SmoothCompactBeltramiRegularity)
      (g : SmoothSurfaceMetric R.toRiemannSurface),
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    ∃ K : X → ℝ,
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ K ∧ HasMetricGaussianCurvatureCoordinates R hreg g K

end LowDimensionalTopology.Unproved.Teichmuller
