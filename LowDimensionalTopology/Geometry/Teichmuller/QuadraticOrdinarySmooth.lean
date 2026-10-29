module

public import LowDimensionalTopology.Geometry.Surfaces.SingularMeasuredFoliation
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticNaturalCoordinate
public import LowDimensionalTopology.Geometry.Teichmuller.ConformalSmooth
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Real smoothness of the original ordinary quadratic coordinate

The actual ordinary coordinate and its actual inverse are real smooth in the
unchanged original surface structure, on their full source and target.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
    {q : HolomorphicQuadraticDifferential R.toRiemannAtlas} {p : X}

/-- The actual ordinary neighborhood chart and inverse retain the original real smooth structure. -/
theorem QuadraticNaturalCoordinateData.ordinaryNeighborhood_isRealSmooth
    (D : QuadraticNaturalCoordinateData R q p) :
    IsRealSmoothFoliationChart R D.ordinaryNeighborhood := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  have hZ : AnalyticOnNhd ℂ (D.ordinaryChart : ℂ → ℂ) D.ordinaryChart.source :=
    D.normal.analytic
  have hZinv : AnalyticOnNhd ℂ (D.ordinaryChart.symm : ℂ → ℂ) D.ordinaryChart.target :=
    openPartialHomeomorph_analytic_inverse D.ordinaryChart hZ
  have hZsmooth : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (D.ordinaryChart : ℂ → ℂ) D.ordinaryChart.source :=
    ((hZ.contDiffOn (n := ∞) D.ordinaryChart.open_source.uniqueDiffOn).restrict_scalars
      ℝ).contMDiffOn
  have hZinvSmooth : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (D.ordinaryChart.symm : ℂ → ℂ) D.ordinaryChart.target :=
    ((hZinv.contDiffOn (n := ∞) D.ordinaryChart.open_target.uniqueDiffOn).restrict_scalars
      ℝ).contMDiffOn
  have hchart : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (chartAt ℂ p) (chartAt ℂ p).source := contMDiffOn_chart
  have hchartInv : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (chartAt ℂ p).symm (chartAt ℂ p).target := contMDiffOn_chart_symm
  let A : OpenPartialHomeomorph X ℂ := (chartAt ℂ p).trans D.ordinaryChart
  have hA : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ A A.source :=
    hZsmooth.comp' hchart
  have hAinv : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ A.symm A.target :=
    hchartInv.comp' hZinvSmooth
  change ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ A
      (A.source ∩ A ⁻¹' interior (Metric.ball (0 : ℂ) D.radius)) ∧
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ A.symm
      (A.target ∩ interior (Metric.ball (0 : ℂ) D.radius))
  exact ⟨hA.mono inter_subset_left, hAinv.mono inter_subset_left⟩

end LowDimensionalTopology.Geometry.Teichmuller
