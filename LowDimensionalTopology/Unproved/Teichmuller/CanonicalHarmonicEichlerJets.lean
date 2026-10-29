module

public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalHarmonicFirstJets

/-!
# The independent canonical-family Eichler first-variation prerequisite

This proposition concerns the same normalized solution, its actual point and
spatial first derivatives, and an actual normalized holomorphic primitive.
It assumes no hyperbolic density, density derivative or invariant metric.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller.HarmonicFirstVariation
open Geometry.Teichmuller.QuadraticBergman LiZhongQC
universe u

/-- Actual canonical harmonic first jets from a normalized controlled Eichler primitive. -/
def CanonicalHarmonicEichlerJets : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : ℍ → X),
    (letI := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p) →
    ∀ q : HolomorphicQuadraticDifferential R.toRiemannAtlas,
    ∃ ψ : ℂ → ℂ,
      DifferentiableOn ℂ ψ upperHalf ∧
      (∀ z ∈ upperHalf, deriv (deriv (deriv ψ)) z = uniformizedQuadratic R p q z) ∧
      ContinuousOn ψ {z : ℂ | 0 ≤ z.im} ∧ ψ 0 = 0 ∧ ψ 1 = 0 ∧
      Tendsto (fun z : ℍ => ψ z / (z : ℂ) ^ 2)
        (Filter.comap (fun z : ℍ => (z : ℂ)) (Filter.cocompact ℂ)) (𝓝 0) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε →
        ContDiffOn ℝ 1 (canonicalFamily R p q t) upperHalf) ∧
      ∀ z : ℍ,
        HasFDerivAt (fun t : ℂ => canonicalFamily R p q t z)
          (eichlerPointJet ψ z) 0 ∧
        HasFDerivAt (fun t : ℂ => dz (canonicalFamily R p q t) z)
          (eichlerDzJet ψ z) 0 ∧
        HasFDerivAt (fun t : ℂ => dzbar (canonicalFamily R p q t) z)
          (ContinuousLinearMap.mul ℝ ℂ (harmonicPlane R p q z)) 0

end LowDimensionalTopology.Unproved.Teichmuller
