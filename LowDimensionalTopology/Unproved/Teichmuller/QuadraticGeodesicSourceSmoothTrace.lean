module

public import LowDimensionalTopology.Unproved.Teichmuller.QuadraticSmoothCarrierInputs

/-!
# Smooth realization of the same finite quadratic-geodesic trace

The given path and its clock are retained. The classical input supplies a
piecewise smooth representative of its same image with the same endpoints.
It asserts no length equality, shortestness, geodesicity or uniqueness.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane ENNReal

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller LiZhongQC

/-- A finite nonbacktracking actual local-geodesic trace admits a source-smooth
representative. The supplied clock may pause, and zeros may be endpoints. -/
def QuadraticGeodesicSourceSmoothTrace
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (_hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X} : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  letI := R.toRiemannAtlas.isManifold
  ∀ hp : IsUniformization Γ p,
    let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
      (utm_liftQD_differentiableOn q.property hp)
    letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
    ∀ {a b : ℍ} (γ : Path a b), a ≠ b →
      phiLengthPath (qH : ℍ → ℂ → ℂ) γ < ⊤ →
      IsPhiGeodesicRS (qH : ℍ → ℂ → ℂ) γ →
      NativePathHasIntervalFibers γ →
      ∃ δ : Path a b,
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface δ ∧
        NativePathHasIntervalFibers δ ∧ Set.range δ = Set.range γ

end LowDimensionalTopology.Unproved.Teichmuller
