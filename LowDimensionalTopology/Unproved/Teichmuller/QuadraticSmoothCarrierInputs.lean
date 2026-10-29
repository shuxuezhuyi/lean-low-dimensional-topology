module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticUpperHalfDistance
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedUniqueness

/-!
# Explicit classical inputs for the actual smooth path carrier

The two independent inputs concern rectifiable arc factorization and smooth
approximation. Their mathematical assertions remain unproved. The original
paths and the actual lifted differential are retained by their consumers.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller LiZhongQC

/-- A path does not backtrack: equal values force constancy between their times. -/
def NativePathHasIntervalFibers {a b : UpperHalfPlane} (α : Path a b) : Prop :=
  ∀ s t : unitInterval, s ≤ t → α s = α t → ∀ u ∈ Icc s t, α u = α s

/-- The classical common rectifiable-arc factorization for two actual paths
in H. Continuous monotone clocks may have plateau intervals. -/
def NativeCommonMonotoneArc : Prop :=
  ∀ {a b : UpperHalfPlane} (α β : Path a b), a ≠ b →
    (∃ K : NNReal, LipschitzOnWith K (fun u : ℝ => (α.extend u : ℂ)) (Icc 0 1)) →
    (∃ K : NNReal, LipschitzOnWith K (fun u : ℝ => (β.extend u : ℂ)) (Icc 0 1)) →
    NativePathHasIntervalFibers α → NativePathHasIntervalFibers β →
    Set.range α = Set.range β →
    ∃ (κ : Path a b) (K : NNReal) (σ τ : unitInterval → unitInterval)
      (hσ : Continuous σ) (hσ0 : σ 0 = 0) (hσ1 : σ 1 = 1)
      (hτ : Continuous τ) (hτ0 : τ 0 = 0) (hτ1 : τ 1 = 1),
      Function.Injective κ ∧
      LipschitzOnWith K (fun u : ℝ => (κ.extend u : ℂ)) (Icc 0 1) ∧
      Monotone σ ∧ Monotone τ ∧
      α = κ.reparam σ hσ hσ0 hσ1 ∧ β = κ.reparam τ hτ hτ0 hτ1

/-- The classical epsilon approximation by actual native smooth competitors,
for the same original surface, differential, uniformization and endpoints. -/
def NativeQuadraticSmoothCofinality : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) (g : ℕ),
    2 ≤ g → R.HasGenus g →
    ∀ q : HolomorphicQuadraticDifferential R.toRiemannAtlas, q ≠ 0 →
    ∀ {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
      {p : UpperHalfPlane → X},
      letI := R.toRiemannAtlas.toChartedSpace
      letI := R.toRiemannAtlas.isManifold
      ∀ _hp : IsUniformization Γ p,
        let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
        let qH := upperHalfNativeQuadratic ψ
          (utm_liftQD_differentiableOn q.property _hp)
        letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
        ∀ {a b : UpperHalfPlane} (γ : Path a b),
          phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) γ < ⊤ →
          ∀ ε : NNReal, 0 < ε → ∃ δ : Path a b,
            HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface δ ∧
            phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) δ ≤
              phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) γ + (ε : ENNReal)

end LowDimensionalTopology.Unproved.Teichmuller
