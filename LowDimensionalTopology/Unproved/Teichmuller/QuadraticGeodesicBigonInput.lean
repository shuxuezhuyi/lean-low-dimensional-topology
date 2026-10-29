module

public import LowDimensionalTopology.Unproved.Teichmuller.QuadraticGeodesicPolygonInputs

/-!
# Finite two-path geometry before the written quadratic uniqueness calculation

The two original paths, their native lifted differential and every actual
polygon corner trace are retained. This input is only the classical finite
bigon extraction in the source's ``replace the two endpoints'' reduction.
It states no angle estimate, angle sum, uniqueness or minimizing conclusion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller LiZhongQC

/-- Distinct traces of the two actual local geodesics supply finite simple
polygon geometry. Only the two joining vertices may fail to follow an
actual interior corner of one of the original paths. -/
def QuadraticGeodesicBigonExtraction
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (_hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X} : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  letI := R.toRiemannAtlas.isManifold
  ∀ hp : IsUniformization Γ p,
    let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
    let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
    letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
    ∀ {a b : ℍ} (α β : Path a b), a ≠ b →
      IsPhiGeodesicRS (qH : ℍ → ℂ → ℂ) α →
      IsPhiGeodesicRS (qH : ℍ → ℂ → ℂ) β →
      Set.range α ≠ Set.range β →
      ∃ (c : ℂ) (r : ℝ), 0 < r ∧
        MapsTo (fun w : ℂ => c + (r : ℂ) * w) unitDisc upperHalf ∧
        ∃ (n : ℕ) (hn : NeZero n),
          letI := hn
          ∃ (P : PhiPolygon (fun w => (r : ℂ) ^ 2 * ψ (c + (r : ℂ) * w)) n)
            (E : Finset (Fin n)),
            (fun w : ℂ => c + (r : ℂ) * w) '' frontier P.dom ⊆
              Set.range (fun u : unitInterval => (α u : ℂ)) ∪
                Set.range (fun u : unitInterval => (β u : ℂ)) ∧
            E.card ≤ 2 ∧
            ∀ j ∉ E,
              FollowsActualPolygonCorner α 0 1 c r P j ∨
                FollowsActualPolygonCorner β 0 1 c r P j

end LowDimensionalTopology.Unproved.Teichmuller
