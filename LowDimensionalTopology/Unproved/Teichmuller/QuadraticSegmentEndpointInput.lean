module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeQuadraticSegments
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticUpperHalfDistance
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedUniqueness

/-!
# Endpoint ray images of an actual quadratic segment

These two inputs isolate the classical passage from a supplied locally straight
embedded arc to a ray image in an actual ordinary coordinate. They do not
assert a length, distance or minimizing property, or regularity of its speed.
Both inputs remain unproved until independent proofs are supplied.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller LiZhongQC

/-- A supplied smooth geometric segment ending at a zero has a ray tail in
its actual normalized ordinary coordinate. The original parameter is retained. -/
def NativeQuadraticZeroEndpointRay : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (_hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X},
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ _hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      let qH := upperHalfNativeQuadratic ψ
        (utm_liftQD_differentiableOn q.property _hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (L : Path a b),
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface L →
        IsQuadraticSegment upperHalfNativeSurface qH L.toContinuousMap →
        ∀ first : Bool,
          let z₀ : UpperHalfPlane := if first then a else b
          ψ (z₀ : ℂ) = 0 →
          ∀ m : ℕ, 0 < m → ∀ ξ : ℂ → ℂ,
            AnalyticAt ℂ ξ (z₀ : ℂ) → ξ (z₀ : ℂ) = 0 →
            deriv ξ (z₀ : ℂ) ≠ 0 →
            (∀ᶠ z in 𝓝 (z₀ : ℂ),
              ψ z = (((m : ℂ) + 2) / 2) ^ 2 * ξ z ^ m * deriv ξ z ^ 2) →
            ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ v : ℂ, ‖v‖ = 1 ∧
              ∀ u ∈ Icc (0 : ℝ) ε, ∃ ρ : ℝ, 0 ≤ ρ ∧
                ξ (L.extend (if first then u else 1 - u) : ℂ) = (ρ : ℂ) * v

/-- The classical ordinary endpoint transport for the same supplied smooth
embedded segment. This asserts only a ray image, allowing zero velocity. -/
def NativeQuadraticOrdinaryEndpointRay : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (_hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X},
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ _hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      let qH := upperHalfNativeQuadratic ψ
        (utm_liftQD_differentiableOn q.property _hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (L : Path a b),
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface L →
        IsQuadraticSegment upperHalfNativeSurface qH L.toContinuousMap →
        ∀ first : Bool,
          let z₀ : UpperHalfPlane := if first then a else b
          ψ (z₀ : ℂ) ≠ 0 →
          ∀ ξ : ℂ → ℂ,
            AnalyticAt ℂ ξ (z₀ : ℂ) → ξ (z₀ : ℂ) = 0 →
            deriv ξ (z₀ : ℂ) ≠ 0 →
            (∀ᶠ z in 𝓝 (z₀ : ℂ), deriv ξ z ^ 2 = ψ z) →
            ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ v : ℂ, ‖v‖ = 1 ∧
              ∀ u ∈ Icc (0 : ℝ) ε, ∃ ρ : ℝ, 0 ≤ ρ ∧
                ξ (L.extend (if first then u else 1 - u) : ℂ) = (ρ : ℂ) * v

end LowDimensionalTopology.Unproved.Teichmuller
