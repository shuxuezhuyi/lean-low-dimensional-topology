module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalSmoothMetricGaussianCurvature

/-!
# Gaussian curvature and the two original metric slices

The chosen scalar function is smooth and satisfies the displayed formula
on every genuine chart of the same metric's actual isothermal realization.
Gaussian curvature minus one and minus one half are distinct metric slices.
The latter corresponds to real scalar curvature minus one under Scal = 2 K.
No metric rescaling or geometric quotient comparison is asserted here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (hreg : Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (hcurv : Unproved.Teichmuller.OriginalSmoothMetricGaussianCurvature.{u})

/-- The same coordinate law determines a function uniquely, by genuine
chart coverage and the inverse of the actual original marking. -/
theorem metricGaussianCurvatureCoordinates_unique
    (g : SmoothSurfaceMetric R.toRiemannSurface) (K L : X → ℝ)
    (hK : HasMetricGaussianCurvatureCoordinates R hreg g K)
    (hL : HasMetricGaussianCurvatureCoordinates R hreg g L) : K = L := by
  let S := rawMetricIsothermalSurface R.toRiemannSurface hreg g
  let f := rawMetricIsothermalMarking R.toRiemannSurface hreg g
  let := S.toRiemannAtlas.toChartedSpace
  funext x
  let y := f.toHomeomorph x
  let e : OriginalComplexChart S := ⟨chartAt ℂ y, chart_mem_atlas ℂ y⟩
  have hy : y ∈ e.val.source := mem_chart_source ℂ y
  have hz : e.val y ∈ e.val.target := e.val.map_source hy
  have hKz := hK e (e.val y) hz
  have hLz := hL e (e.val y) hz
  have hx : (SmoothSurfaceEquiv.symm f).toHomeomorph
      (e.val.symm (e.val y)) = x := by
    rw [e.val.left_inv hy]
    exact f.toHomeomorph.symm_apply_apply x
  have hKL : K ((SmoothSurfaceEquiv.symm f).toHomeomorph (e.val.symm (e.val y))) =
      L ((SmoothSurfaceEquiv.symm f).toHomeomorph (e.val.symm (e.val y))) :=
    hKz.trans hLz.symm
  simpa only [hx] using hKL

/-- The actual Gaussian curvature function on the original point carrier. -/
def metricGaussianCurvature (g : SmoothSurfaceMetric R.toRiemannSurface) : X → ℝ :=
  (hcurv X R hreg g).choose

/-- Smoothness and the exact same-metric coordinate formula of the chosen function. -/
theorem metricGaussianCurvature_spec (g : SmoothSurfaceMetric R.toRiemannSurface) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (metricGaussianCurvature R hreg hcurv g) ∧
      HasMetricGaussianCurvatureCoordinates R hreg g
        (metricGaussianCurvature R hreg hcurv g) := by
  exact (hcurv X R hreg g).choose_spec

/-- The coordinate law alone identifies any other candidate with the
chosen Gaussian curvature; no smoothness premise is needed for uniqueness. -/
theorem metricGaussianCurvature_unique (g : SmoothSurfaceMetric R.toRiemannSurface)
    (K : X → ℝ) (hK : HasMetricGaussianCurvatureCoordinates R hreg g K) :
    K = metricGaussianCurvature R hreg hcurv g := by
  exact metricGaussianCurvatureCoordinates_unique R hreg g K
    (metricGaussianCurvature R hreg hcurv g) hK (metricGaussianCurvature_spec R hreg hcurv g).2

/-- All original smooth metrics whose Gaussian curvature is minus one. -/
def curvatureMinusOneMetrics : Set (SmoothSurfaceMetric R.toRiemannSurface) :=
  {g | ∀ x : X, metricGaussianCurvature R hreg hcurv g x = -1}

/-- The separate Gaussian level minus one half, corresponding to standard
real scalar curvature minus one in dimension two. -/
def gaussianCurvatureMinusHalfMetrics : Set (SmoothSurfaceMetric R.toRiemannSurface) :=
  {g | ∀ x : X, metricGaussianCurvature R hreg hcurv g x = -(1 / 2 : ℝ)}

end LowDimensionalTopology.Geometry.Teichmuller
