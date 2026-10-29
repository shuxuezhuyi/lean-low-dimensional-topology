module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricTensorDivergence
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalTensorL2Pairing
public import LowDimensionalTopology.Geometry.Teichmuller.SmoothFormInterior

/-!
# The exact original-metric closed-surface Green prerequisite

The formal-adjoint identity is on the compact boundaryless original surface,
with its actual metric, chosen area and positive tensor divergence. The
coordinate predicate fixes the same native vector field and symmetric tensor.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Bundle MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

open scoped Classical in
/-- The original metric Lie coordinate expression on every actual original
chart, with the same vector field and both native tangent slots. -/
def HasOriginalMetricLieCoordinates
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X) →
      SmoothSymmetricTwoTensor R → Prop :=
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  fun V L => ∀ e : OriginalComplexChart R.toRiemannSurface,
    let b : Fin 2 → ℂ := Complex.basisOneI
    let G : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun z i j =>
      metricGramInChart g e (e.val.symm z) (b i) (b j)
    let C : ℂ → Fin 2 → ℝ := fun z k =>
      if hz : z ∈ e.val.target then
        let x := e.val.symm z
        let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x
          (e.val.map_target hz)
        Complex.basisOneI.repr (D (V.toFun x)) k
      else 0
    let coordPartial : (ℂ → ℝ) → Fin 2 → ℂ → ℝ :=
      fun f j z => fderiv ℝ f z (b j)
    ∀ (z : ℂ) (hz : z ∈ e.val.target) (i j : Fin 2),
      let x := e.val.symm z
      let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x
        (e.val.map_target hz)
      L.val.toFun x (D.symm (b i)) (D.symm (b j)) =
        ∑ k : Fin 2,
          (C z k * coordPartial (fun w => G w i j) k z +
            G z i k * coordPartial (fun w => C w k) j z +
            G z j k * coordPartial (fun w => C w k) i z)

end LowDimensionalTopology.Geometry.Teichmuller

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller MeasureTheory
open scoped Manifold ContDiff
universe u

/-- The classical closed-surface Green identity for the same original metric,
its chosen area, its positive tensor divergence and an actual Lie representative.
This input contains no Lie existence, orthogonality or TT conclusion. -/
def OriginalClosedMetricTensorGreen : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (R : ClosedRiemannSurface X)
      (g : SmoothSurfaceMetric R.toRiemannSurface)
      (harea : OriginalSmoothMetricAreaMeasure R g)
      (hdiv : OriginalSmoothMetricTensorDivergence.{u}),
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    letI : MeasurableSpace X := borel X
    let μ : Measure X := harea.exists.choose
    ∀ (V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X))
        (L h : SmoothSymmetricTwoTensor R),
      HasOriginalMetricLieCoordinates R g V L →
        metricTensorL2Pairing R g harea h L =
          -2 * ∫ x : X, (metricTensorDivergence R g hdiv h).toFun x (V.toFun x) ∂μ

end LowDimensionalTopology.Unproved.Teichmuller
