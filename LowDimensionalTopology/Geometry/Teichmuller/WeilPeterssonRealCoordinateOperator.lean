module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonRealForm
public import LowDimensionalTopology.Geometry.Teichmuller.NativeRealTangent
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# The entire real WP bilinear operator in the actual Bers coordinates

The coefficients, tangent inverse coordinates, original form and factor 2 are
unchanged. Fixed-vector smoothness is lifted to the normed operator space.
-/

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

local notation "E" => Fin (3*g-3) → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "coord" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "realPair" => nativeWeilPeterssonRealCoordinatePairing R hp hg hgenus hΓ hfree hsmooth

/-- The whole original real bilinear form, in the actual inverse Bers coordinates. -/
def nativeWeilPeterssonRealCoordinateOperator (a : TeichmullerSpace.{0,0} R) (t : E) :
    E →L[ℝ] E →L[ℝ] ℝ := by
  let := C
  let q := (chart a).symm t
  let L : TangentSpace TI q ≃ₗ[ℝ] E := (coord q).toLinearEquiv.restrictScalars ℝ
  exact ((nativeWeilPeterssonRealBilinForm R hp hg hgenus hΓ hfree hsmooth q).compl₁₂
    L.symm.toLinearMap L.symm.toLinearMap).toContinuousBilinearMap

/-- Evaluation is exactly the already defined original twice-real-part pairing. -/
@[simp] theorem nativeWeilPeterssonRealCoordinateOperator_apply
    (a : TeichmullerSpace.{0,0} R) (t v w : E) :
    nativeWeilPeterssonRealCoordinateOperator R hp hg hgenus hΓ hfree hsmooth a t v w =
      realPair a v w t := rfl

/-- The full normed bilinear-operator family is smooth under the same explicit
analytic input, for every actual Bers chart. -/
theorem contDiffOn_nativeWeilPeterssonRealCoordinateOperator_of_localSmoothness
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) (a : TeichmullerSpace.{0,0} R) :
    ContDiffOn ℝ ∞
      (nativeWeilPeterssonRealCoordinateOperator R hp hg hgenus hΓ hfree hsmooth a)
      (chart a).target := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  exact (contDiffOn_nativeWeilPeterssonRealCoordinatePairing_of_localSmoothness
    R hp hg hgenus hΓ hfree hsmooth hWP a v w).congr
      (fun t _ => nativeWeilPeterssonRealCoordinateOperator_apply
        R hp hg hgenus hΓ hfree hsmooth a t v w)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
