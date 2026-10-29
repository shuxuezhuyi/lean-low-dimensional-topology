module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalInfinitesimalTeichmullerFunction
public import LowDimensionalTopology.Geometry.Teichmuller.NativeNonzeroTangentQuotient

/-!
# Descent of the original positive-direction distance function

This unproved proposition identifies values only when both the original
marked point and its actual Bers tangent direction agree.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Unproved.Teichmuller
open LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Teichmuller
open TeichmullerSpace GammaMeasurableBeltrami NormalizedCoefficientTransport

/-- The actual directional distance function is independent of coefficient
presentations of the same original marked point and tangent direction. -/
def OriginalInfinitesimalDistanceDescent
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p) : Prop :=
  ∀ (ξ ξ' : Ball Γ) (η η' : Space Γ),
    coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ξ =
      coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ξ' →
    nonzeroBersDerivative R hp hg hgenus hΓ ξ η =
      nonzeroBersDerivative R hp hg hgenus hΓ ξ' η' →
    coefficientInfinitesimalTeichmullerFunction R hg hgenus hΓ hfree hp ξ η =
      coefficientInfinitesimalTeichmullerFunction R hg hgenus hΓ hfree hp ξ' η'

end LowDimensionalTopology.Unproved.Teichmuller
