module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticL1Norm

/-!
# Royden's quadratic-differential rigidity, retained as an unproved proposition

One unit complex number works for every quadratic differential. The inducing
biholomorphism goes from the target surface to the source surface. This
declaration supplies no proof of the rigidity theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Teichmuller

universe u v

/-- A genuine L1 isometry is one common unit phase times biholomorphic quadratic pullback. -/
def RoydenQuadraticL1Rigidity
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  letI := S.toRiemannAtlas.toChartedSpace
  ∀ g : ℕ, 1 < g → R.HasGenus g → S.HasGenus g →
    ∀ α : HolomorphicQuadraticDifferential R.toRiemannAtlas ≃ₗ[ℂ]
        HolomorphicQuadraticDifferential S.toRiemannAtlas,
      (∀ q, QuadraticL1.coefficientIntegral S (α q) = QuadraticL1.coefficientIntegral R q) →
      ∃ (h : Y ≃ₜ X) (c : ℂ),
        RiemannAnalyticMap S.toRiemannAtlas R.toRiemannAtlas h ∧
        RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas h.symm ∧ ‖c‖ = 1 ∧
          ∀ (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (y : Y) (w : ℂ),
            let e := chartAt ℂ y
            let k := chartAt ℂ (h y)
            let H := riemannChartMap e h k
            w ∈ riemannChartMapDomain e h k →
              (α q : Y → ℂ → ℂ) y w =
                c * (q : X → ℂ → ℂ) (h y) (H w) * (deriv H w) ^ 2

end LowDimensionalTopology.Unproved.Teichmuller
