module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricTensorTrace
public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricGramSmooth
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Positive divergence on the original symmetric tensor bundle

The general coordinate-independence and smooth global gluing statement is
kept explicit as one unproved proposition. Its output is an actual smooth
covector on the original real tangent bundle. The direct consumers choose
that covector, display the prescribed formula and retain its uniqueness.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle
open scoped Manifold ContDiff BigOperators
universe u

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The positive-divergence coordinate law on every actual original chart.
The target is open, so derivatives at a valid point depend on a neighbourhood
inside that target. The zero totalization of A outside it is irrelevant.
The Gram form uses the same metric and the actual inverse chart differential. -/
def HasMetricTensorDivergenceCoordinates
    (g : SmoothSurfaceMetric R.toRiemannSurface) (h : SmoothSymmetricTwoTensor R) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℝ) ∞
      (fun x : X => TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ) → Prop := by
  letI := R.toRiemannAtlas.toChartedSpace
  letI := R.toRiemannAtlas.isRealManifold
  exact fun delta =>
    ∀ e : OriginalComplexChart R.toRiemannSurface,
      let b : Fin 2 → ℂ := Complex.basisOneI
      let G : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun z i j =>
        metricGramInChart g e (e.val.symm z) (b i) (b j)
      let A : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun z i j => by
        classical
        exact if hz : z ∈ e.val.target then
          let x := e.val.symm z
          let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x
            (e.val.map_target hz)
          (Complex.basisOneI.repr
            (D (metricRaisedTensor R g h x (D.symm (b i))))) j
        else 0
      let mu : ℂ → ℝ := fun z => Real.sqrt (Matrix.det (G z))
      let coordPartial : (ℂ → ℝ) → Fin 2 → ℂ → ℝ :=
        fun f j z => fderiv ℝ f z (b j)
      ∀ (z : ℂ) (hz : z ∈ e.val.target) (i : Fin 2),
        let x := e.val.symm z
        let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x
          (e.val.map_target hz)
        delta.toFun x (D.symm (b i)) =
          (mu z)⁻¹ * (∑ j : Fin 2,
            coordPartial (fun w => mu w * A w i j) j z)
          - (1 / 2 : ℝ) * (∑ k : Fin 2, ∑ l : Fin 2, ∑ j : Fin 2,
            (G z)⁻¹ k l * A z l j * coordPartial (fun w => G w j k) i z)

end LowDimensionalTopology.Geometry.Teichmuller

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller

/-- The displayed positive coordinate formula determines a unique native
smooth covector for every actual original metric and symmetric two-tensor. -/
def OriginalSmoothMetricTensorDivergence : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (R : ClosedRiemannSurface X)
      (g : SmoothSurfaceMetric R.toRiemannSurface) (h : SmoothSymmetricTwoTensor R),
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    ∃! delta : ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℝ) ∞
        (fun x : X => TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ),
      HasMetricTensorDivergenceCoordinates R g h delta

end LowDimensionalTopology.Unproved.Teichmuller
