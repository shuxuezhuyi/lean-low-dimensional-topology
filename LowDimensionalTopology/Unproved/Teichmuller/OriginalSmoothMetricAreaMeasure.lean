module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricGramSmooth
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# The prescribed finite area of an original smooth surface metric

The classical input is existence and uniqueness of a finite Borel measure
with the actual inverse-chart Gram density in every preferred original chart.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller MeasureTheory
universe u

/-- The original metric prescribes a unique finite Borel measure by its true chart densities. -/
def OriginalSmoothMetricAreaMeasure {X : Type u} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) (g : SmoothSurfaceMetric R.toRiemannSurface) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  letI : MeasurableSpace X := borel X
  ∃! μ : Measure X,
    IsFiniteMeasure μ ∧
    ∀ p : X,
      let e : OriginalComplexChart R.toRiemannSurface :=
        ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
      let B : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
        fun z => metricGramInChart g e (e.val.symm z)
      Measure.map (e.val : X → ℂ) (μ.restrict e.val.source) =
        ((volume : Measure ℂ).withDensity (fun z =>
          ENNReal.ofReal (Real.sqrt
            (B z 1 1 * B z Complex.I Complex.I - (B z 1 Complex.I) ^ 2)))).restrict e.val.target

end LowDimensionalTopology.Unproved.Teichmuller
