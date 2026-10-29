module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalWPDeformedReferenceCoefficients
public import LowDimensionalTopology.Unproved.Teichmuller.WeilPeterssonDeformedReferenceRealCurvatureNaturality

/-!
# Lowering the actual reference-change curvature identity

The actual WP isometry lowers the concrete real-curvature naturality input.
Only the fixed original coefficient-smoothness input is used; the genuine
inverse-reference producer supplies the corresponding smoothness on the
actual deformed surface.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport
open Unproved.Teichmuller

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "H" => nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "M" => nativeWeilPeterssonCoefficientMatrix
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "pair" => nativeWeilPeterssonRealCoordinatePairing
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

private theorem reference_metric_eq_pairing (t u v : E) :
    FiniteKahlerCoordinateContract.metric M t u v = pair u v t := by
  rw [nativeWeilPeterssonRealCoordinatePairing_eq_sum]
  unfold FiniteKahlerCoordinateContract.metric FiniteKahlerCoordinateContract.hermitian
  apply congrArg (fun z : ℂ => 2 * z.re)
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  change u j * nativeWeilPeterssonLocalCoefficient
      R hp hg hgenus hΓ hfree hsmooth (basePoint R) j k t * conj (v k) = _
  ring

variable (ν : Ball Γ)

local notation "Y" => deformedNativeSurface R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "hY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν
local notation "hΔ" => And.left (deformedGroup_spec hΓ ν)
local notation "hfY" => deformedNativeSurface_actsFreely R hgenus hΓ hp ν
local notation "CY" => canonicalComplexChartedSpace Y hg hY hP hΔ hfY hpY hsmooth
local notation "BCY" => bersCoordinates Y hg hY hP hΔ hfY hpY
local notation "HY" => nativeWeilPeterssonCore Y hpY hg hY hΔ hfY hsmooth
local notation "KY" => nativeWeilPeterssonCoordinateEquiv Y hpY hg hY hΔ hfY hsmooth
local notation "chartY" => nativeWeilPeterssonCoordinateChart Y hpY hg hY hΔ hfY hsmooth
local notation "MY" => nativeWeilPeterssonCoefficientMatrix
  Y hpY hg hY hΔ hfY hsmooth (basePoint Y)
local notation "pairY" => nativeWeilPeterssonRealCoordinatePairing
  Y hpY hg hY hΔ hfY hsmooth (basePoint Y)
local notation "A" => deformedReferenceChangeEquiv R hp hg hgenus hΓ ν
local notation "f" => deformedReferenceWeilPeterssonCoordinateMap R hp hg hgenus hΓ ν
local notation "x" => BC (β ν.val)
local notation "J" => fderiv ℝ f x

private theorem reference_metric_at_center (u v : E) :
    FiniteKahlerCoordinateContract.metric M x u v =
      FiniteKahlerCoordinateContract.metric MY 0 (J u) (J v) := by
  let := C
  let := CY
  let a := β ν.val
  have hleft : (chart (basePoint R)).symm (BC a) = a := by
    simpa only [nativeWeilPeterssonCoordinateChart_coe] using
      (chart (basePoint R)).left_inv (mem_chart_source E a)
  have hleftY : (chartY (basePoint Y)).symm (f (BC a)) = A a := by
    rw [deformedReferenceWeilPeterssonCoordinateMap_point]
    simpa only [nativeWeilPeterssonCoordinateChart_coe] using
      (chartY (basePoint Y)).left_inv (mem_chart_source E (A a))
  have hframe (z : E) : mfderiv TI TI A a ((K a).symm z) =
      (KY (A a)).symm (fderiv ℝ f (BC a) z) := by
    apply (KY (A a)).injective
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      deformedReferenceWeilPeterssonCoordinateMap_tangent
        R hp hg hgenus hΓ hfree hsmooth ν a ((K a).symm z)
  have hcore := nativeWeilPeterssonCore_deformedReference_allPoints_pullback
    R hp hg hgenus hΓ hfree hsmooth ν a ((K a).symm u) ((K a).symm v)
  rw [hframe, hframe] at hcore
  have hpair : pair u v (BC a) =
      pairY (fderiv ℝ f (BC a) u) (fderiv ℝ f (BC a) v) (f (BC a)) := by
    dsimp only [nativeWeilPeterssonRealCoordinatePairing]
    rw [hleft, hleftY]
    exact (congrArg (fun z : ℂ => 2 * z.re) hcore).symm
  calc
    _ = pair u v x := reference_metric_eq_pairing R hp hg hgenus hΓ hfree hsmooth x u v
    _ = pairY (J u) (J v) (f x) := hpair
    _ = FiniteKahlerCoordinateContract.metric MY (f x) (J u) (J v) :=
      (reference_metric_eq_pairing Y hpY hg hY hΔ hfY hsmooth (f x) (J u) (J v)).symm
    _ = _ := by rw [deformedReferenceWeilPeterssonCoordinateMap_center]

/-- The same actual twice-real-part metric lowers the concrete three-slot
curvature input, while the original smoothness input supplies target
smoothness through the genuine inverse-reference producer. -/
theorem nativeWeilPeterssonDeformedReference_loweredRealCurvature
    (hWP : WeilPeterssonLocalCoefficientSmoothness R hp hg hgenus hΓ hfree hsmooth)
    (hnat : WeilPeterssonDeformedReferenceRealCurvatureNaturality
      R hp hg hgenus hΓ hfree hsmooth) :
    WeilPeterssonLocalCoefficientSmoothness Y hpY hg hY hΔ hfY hsmooth ∧
      ∀ u v w s : E,
        FiniteKahlerCoordinateContract.metric M x
            (FiniteKahlerCoordinateContract.realCurvature M x u v w) s =
          FiniteKahlerCoordinateContract.metric MY 0
            (FiniteKahlerCoordinateContract.realCurvature MY 0 (J u) (J v) (J w)) (J s) := by
  refine ⟨nativeWeilPeterssonLocalCoefficientSmoothness_deformedReference
    R hp hg hgenus hΓ hfree hsmooth ν hWP, ?_⟩
  intro u v w s
  rw [reference_metric_at_center R hp hg hgenus hΓ hfree hsmooth ν,
    hnat ν hWP u v w]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
