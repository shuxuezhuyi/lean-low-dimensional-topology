module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonChristoffelRegularity
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonPureCoordinateCancellation

/-! The original pure holomorphic cancellation needs no independent regularity premise. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3*g-3)
local notation "E" => I → ℂ
local notation "Dz" => nativeWeilPeterssonCoordinateDz (g := g)
local notation "G" => nativeWeilPeterssonChristoffelExpression R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth

/-- At every genuine native chart point, smoothness of the original H supplies
the actual Christoffel derivatives used in the pure holomorphic cancellation. -/
theorem nativeWeilPeterssonChristoffelExpression_pureHolomorphic_of_localSmoothness
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (a : TeichmullerSpace.{0,0} R) (t : E) (ht : t ∈ (chart a).target) (j k l r : I) :
    Dz (G a j k l) r t - Dz (G a j k r) l t +
      (∑ n, G a j n r t * G a n k l t) -
      (∑ n, G a j n l t * G a n k r t) = 0 := by
  refine nativeWeilPeterssonChristoffelExpression_pureHolomorphic_of_differentiable
    R hp hg hgenus hΓ hfree hsmooth hWP a t ht ?_ j k l r
  intro b c d
  exact differentiableAt_nativeWeilPeterssonChristoffelExpression_of_localSmoothness
    R hp hg hgenus hΓ hfree hsmooth hWP a b c d t ht

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
