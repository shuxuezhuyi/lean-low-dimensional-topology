module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonMixedKernelDerivation
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonRicciExpressionSign

/-! Original Ricci/scalar expressions with their mixed control discharged. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "hP" => canonicalHandleGroupPresentation g
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth

variable (a : TeichmullerSpace.{0,0} R) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (hvary : Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (hdiag : Unproved.Teichmuller.WeilPeterssonDiagonalKernelControl
      R hp hg hgenus hΓ hfree hsmooth)

local notation "t" => (chart a) (β ν.val)
local notation "hmixed" => nativeWeilPeterssonMixedKernelControl_of_secondVariation_diagonal
  R hp hg hgenus hΓ hfree hsmooth hvary hdiag

include hvary hdiag hF

/-- Strict Ricci-expression sign with only the original analytic inputs. -/
theorem nativeWeilPeterssonDirectionalRicciExpression_re_neg_derived
    (v : E) (hv : v ≠ 0) :
    (nativeWeilPeterssonDirectionalRicciExpression
      R hp hg hgenus hΓ hfree hsmooth a v t).re < 0 := by
  exact nativeWeilPeterssonDirectionalRicciExpression_re_neg
    R hp hg hgenus hΓ hfree hsmooth a ν P F hF hvary hmixed hdiag v hv

/-- Strict sign of the actual inverse-Hermitian scalar expression. -/
theorem nativeWeilPeterssonScalarExpression_re_neg_derived :
    (nativeWeilPeterssonScalarExpression R hp hg hgenus hΓ hfree hsmooth a t).re < 0 := by
  exact nativeWeilPeterssonScalarExpression_re_neg
    R hp hg hgenus hΓ hfree hsmooth a ν P F hF hvary hmixed hdiag

/-- The separate full-real-trace expression retains the source's g = 2 Re h. -/
theorem nativeWeilPeterssonRealScalarExpression_neg_derived :
    nativeWeilPeterssonRealScalarExpression R hp hg hgenus hΓ hfree hsmooth a t < 0 := by
  exact nativeWeilPeterssonRealScalarExpression_neg
    R hp hg hgenus hΓ hfree hsmooth a ν P F hF hvary hmixed hdiag

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
