module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence

/-! # The positive native tensor divergence selected by its precise gluing input -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle
open scoped Manifold ContDiff BigOperators
universe u

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The actual smooth native covector selected by the precise gluing input. -/
def metricTensorDivergence (g : SmoothSurfaceMetric R.toRiemannSurface)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u})
    (h : SmoothSymmetricTwoTensor R) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℝ) ∞
      (fun x : X => TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ) := by
  letI := R.toRiemannAtlas.toChartedSpace
  letI := R.toRiemannAtlas.isRealManifold
  exact (hdiv X R g h).exists.choose

/-- The selected native divergence has the exact positive coordinate formula. -/
theorem metricTensorDivergence_coordinates
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u})
    (h : SmoothSymmetricTwoTensor R) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
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
        (metricTensorDivergence R g hdiv h).toFun x (D.symm (b i)) =
          (mu z)⁻¹ * (∑ j : Fin 2,
            coordPartial (fun w => mu w * A w i j) j z)
          - (1 / 2 : ℝ) * (∑ k : Fin 2, ∑ l : Fin 2, ∑ j : Fin 2,
            (G z)⁻¹ k l * A z l j * coordPartial (fun w => G w j k) i z) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact (hdiv X R g h).exists.choose_spec

/-- Any native smooth covector satisfying the same actual law is the selected one. -/
theorem metricTensorDivergence_unique
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u})
    (h : SmoothSymmetricTwoTensor R) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    ∀ delta : ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℝ) ∞
        (fun x : X => TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ),
      HasMetricTensorDivergenceCoordinates R g h delta →
        delta = metricTensorDivergence R g hdiv h := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  intro delta hdelta
  exact (hdiv X R g h).unique hdelta (hdiv X R g h).exists.choose_spec

end LowDimensionalTopology.Geometry.Teichmuller
