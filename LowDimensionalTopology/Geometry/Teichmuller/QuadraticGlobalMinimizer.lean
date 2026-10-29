module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticPiecewiseSmoothDistance
public import LowDimensionalTopology.Geometry.Teichmuller.DECoverDescent

/-! Global quadratic minimizers on the same actual native piecewise smooth path carrier. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

universe u
variable {X : Type u} [TopologicalSpace X]

/-- A global quadratic minimizer is an actual admissible path attaining the source infimum. -/
def IsGlobalQuadraticMinimizer (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) {a b : X} (γ : Path a b) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  HasPiecewiseSmoothChartSubdivision R γ ∧
    phiLengthPath (q : X → ℂ → ℂ) γ = piecewiseSmoothQuadraticDistance R q a b

/-- The same actual constant path is a global minimizer on the diagonal. -/
theorem isGlobalQuadraticMinimizer_refl (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (a : X) :
    IsGlobalQuadraticMinimizer R q (Path.refl a) := by
  let := R.toRiemannAtlas.toChartedSpace
  refine ⟨hasPiecewiseSmoothChartSubdivision_refl R a, ?_⟩
  rw [quadraticLengthPath_refl R q a, piecewiseSmoothQuadraticDistance_self R q a]

/-- Attainment bounds the minimizer's original length by every smooth competitor's length. -/
theorem IsGlobalQuadraticMinimizer.length_le_competitor {R : RiemannSurface X}
    {q : HolomorphicQuadraticDifferential R.toRiemannAtlas} {a b : X} {γ : Path a b}
    (hγ : IsGlobalQuadraticMinimizer R q γ) (δ : Path a b)
    (hδ : HasPiecewiseSmoothChartSubdivision R δ) :
    letI := R.toRiemannAtlas.toChartedSpace
    phiLengthPath (q : X → ℂ → ℂ) γ ≤ phiLengthPath (q : X → ℂ → ℂ) δ := by
  let := R.toRiemannAtlas.toChartedSpace
  rw [hγ.2]
  exact piecewiseSmoothQuadraticDistance_le_length R q δ hδ

/-- For an actual smooth path, attainment is equivalent to global competitor minimality. -/
theorem isGlobalQuadraticMinimizer_iff_length_le (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) {a b : X} (γ : Path a b) :
    letI := R.toRiemannAtlas.toChartedSpace
    IsGlobalQuadraticMinimizer R q γ ↔
      HasPiecewiseSmoothChartSubdivision R γ ∧
        ∀ δ : Path a b, HasPiecewiseSmoothChartSubdivision R δ →
          phiLengthPath (q : X → ℂ → ℂ) γ ≤ phiLengthPath (q : X → ℂ → ℂ) δ := by
  let := R.toRiemannAtlas.toChartedSpace
  constructor
  · intro hγ
    exact ⟨hγ.1, fun δ hδ => hγ.length_le_competitor δ hδ⟩
  · rintro ⟨hγ, hmin⟩
    refine ⟨hγ, le_antisymm ?_ (piecewiseSmoothQuadraticDistance_le_length R q γ hγ)⟩
    unfold piecewiseSmoothQuadraticDistance
    exact le_iInf fun δ => le_iInf fun hδ => hmin δ hδ

/-- The global criterion applies to fixed actual H endpoints in its existing native surface. -/
theorem isGlobalQuadraticMinimizer_upperHalf_iff
    (q : HolomorphicQuadraticDifferential upperHalfNativeSurface.toRiemannAtlas)
    {a b : UpperHalfPlane} (γ : Path a b) :
    letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
    IsGlobalQuadraticMinimizer upperHalfNativeSurface q γ ↔
      HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface γ ∧
        ∀ δ : Path a b, HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface δ →
          phiLengthPath (q : UpperHalfPlane → ℂ → ℂ) γ ≤
            phiLengthPath (q : UpperHalfPlane → ℂ → ℂ) δ := by
  exact isGlobalQuadraticMinimizer_iff_length_le upperHalfNativeSurface q γ

end LowDimensionalTopology.Geometry.Teichmuller
