module

public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceHarmonicAmbient
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceGeometricWitness
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceWeilPeterssonCoordinates
public import LowDimensionalTopology.Geometry.Teichmuller.NativeRealTangentTrivialization

/-!
# The actual fixed deformed reference preserves WP at every original point

The already proved ambient harmonic law applies at every coefficient for
one fixed reference coefficient. Its actual target-region witness and the
unchanged selected integral specifications give the full Hermitian law.
The existing actual reference-coordinate derivative then transports the
English-normalized form, retaining every original native tangent vector.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "RI" => 𝓘(ℝ, E)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "H" => nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "D" => nativeWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "omega" => nativeWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hfree hsmooth

private theorem fixedReferenceCore_pointEq :
    letI := C
    ∀ {a b : TeichmullerSpace R} (_h : a = b) (v w : TangentSpace TI a),
      (H b).inner (tangentSpaceCast TI a b w) (tangentSpaceCast TI a b v) =
        (H a).inner w v := by
  let := C
  intro a b h v w
  subst b
  rfl

variable (ν : Ball Γ)

local notation "Y" => deformedNativeSurface R hgenus hΓ hp ν
local notation "hY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "Δ" => deformedGroup hΓ ν
local notation "hΔ" => And.left (deformedGroup_spec hΓ ν)
local notation "hfY" => deformedNativeSurface_actsFreely R hgenus hΓ hp ν
local notation "CY" => canonicalComplexChartedSpace Y hg hY hP hΔ hfY hpY hsmooth
local notation "βY" => coefficientProjection Y hg hY hP hΔ hfY hpY
local notation "BCY" => bersCoordinates Y hg hY hP hΔ hfY hpY
local notation "HY" => nativeWeilPeterssonCore Y hpY hg hY hΔ hfY hsmooth
local notation "KY" => nativeWeilPeterssonCoordinateEquiv Y hpY hg hY hΔ hfY hsmooth
local notation "DY" => nativeWeilPeterssonRealTangentCoordinateEquiv Y hpY hg hY hΔ hfY hsmooth
local notation "chartY" => nativeWeilPeterssonCoordinateChart Y hpY hg hY hΔ hfY hsmooth
local notation "ΩY" => nativeWeilPeterssonFundamentalRealCoordinateForm
  Y hpY hg hY hΔ hfY hsmooth (basePoint Y)
local notation "omegaY" => nativeWeilPeterssonRealFundamentalForm Y hpY hg hY hΔ hfY hsmooth
local notation "A" => deformedReferenceChangeEquiv R hp hg hgenus hΓ ν
local notation "f" => deformedReferenceWeilPeterssonCoordinateMap R hp hg hgenus hΓ ν

/-- For one fixed actual reference coefficient, the full selected original
Hermitian tensor is preserved at every original native marked point. -/
theorem nativeWeilPeterssonCore_deformedReference_allPoints_pullback :
    letI := C
    letI := CY
    ∀ (a : TeichmullerSpace R) (v w : TangentSpace TI a),
      (HY (A a)).inner (mfderiv TI TI A a w) (mfderiv TI TI A a v) =
        (H a).inner w v := by
  let := C
  let := CY
  intro a
  obtain ⟨μ, hμ⟩ := coefficientProjectionBall_surjective R hg hgenus hΓ hfree hp a
  have hμa : β μ.val = a :=
    (coefficientProjection_ball R hg hgenus hΓ hfree hp μ).trans hμ
  rw [← hμa]
  intro v w
  obtain ⟨P, F, hF⟩ := exists_deformedHalfPlaneFundamentalRegion R hgenus hΓ hp μ
  obtain ⟨P', hF', _c, _hc, _hcover⟩ :=
    exists_deformedReferenceGeometricWitness R hp hgenus hΓ ν μ P F hF
  let κ := translatedBall hΓ ν μ
  have hpoint : A (β μ.val) = βY κ.val := by
    rw [coefficientProjection_ball R hg hgenus hΓ hfree hp μ,
      coefficientProjection_ball Y hg hY hΔ hfY hpY κ]
    exact deformedReferenceChangeEquiv_coefficientProjection R hp hg hgenus hΓ hfree ν μ
  let J := tangentSpaceCast TI (A (β μ.val)) (βY κ.val)
  have hambient := deformedReferenceChangeEquiv_harmonic_ambient
    R hp hg hgenus hΓ hfree hsmooth ν μ P F hF P'
      ((fun z : ℍ => (1 : Deck) • z) ⁻¹' F) hF'
  have hregion : ((fun z : ℍ => (1 : Deck) • z) ⁻¹' F) = F := by
    ext z
    simp
  calc
    (HY (A (β μ.val))).inner (mfderiv TI TI A (β μ.val) w)
        (mfderiv TI TI A (β μ.val) v) =
        (HY (βY κ.val)).inner (J (mfderiv TI TI A (β μ.val) w))
          (J (mfderiv TI TI A (β μ.val) v)) :=
      (fixedReferenceCore_pointEq Y hpY hg hY hΔ hfY hsmooth hpoint _ _).symm
    _ = WeilPetersson.beltramiPairing ((fun z : ℍ => (1 : Deck) • z) ⁻¹' F)
        (TH μ P F hF hsmooth v).val.val (TH μ P F hF hsmooth w).val.val := by
      rw [nativeWeilPeterssonCore_integral Y hpY hg hY hΔ hfY hsmooth κ P' _ hF',
        hambient v, hambient w]
    _ = WeilPetersson.beltramiPairing F
        (TH μ P F hF hsmooth v).val.val (TH μ P F hF hsmooth w).val.val := by rw [hregion]
    _ = (H (β μ.val)).inner w v :=
      (nativeWeilPeterssonCore_integral R hp hg hgenus hΓ hfree hsmooth μ P F hF v w).symm

/-- The fixed actual reference-coordinate map pulls back the original form
on the entire original native Bers image, with its actual real derivative. -/
theorem nativeWeilPeterssonCoordinateForm_deformedReference_allPoints_pullback :
    ∀ a : TeichmullerSpace R,
      Ω (BC a) = (ΩY (f (BC a))).compContinuousLinearMap (fderiv ℝ f (BC a)) := by
  let := C
  let := CY
  intro a
  have ht (z : E) : mfderiv TI TI A a ((K a).symm z) =
      (KY (A a)).symm (fderiv ℝ f (BC a) z) := by
    apply (KY (A a)).injective
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      deformedReferenceWeilPeterssonCoordinateMap_tangent
        R hp hg hgenus hΓ hfree hsmooth ν a ((K a).symm z)
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  change Ω (BC a) ![v 0, v 1] =
    ΩY (f (BC a)) ![fderiv ℝ f (BC a) (v 0), fderiv ℝ f (BC a) (v 1)]
  rw [deformedReferenceWeilPeterssonCoordinateMap_point,
    nativeWeilPeterssonCoordinateForm_complexFrame, nativeWeilPeterssonCoordinateForm_complexFrame]
  have hleft : (chart (basePoint R)).symm (BC a) = a := by
    simpa only [nativeWeilPeterssonCoordinateChart_coe] using
      (chart (basePoint R)).left_inv (mem_chart_source E a)
  have hleftY : (chartY (basePoint Y)).symm (BCY (A a)) = A a := by
    simpa only [nativeWeilPeterssonCoordinateChart_coe] using
      (chartY (basePoint Y)).left_inv (mem_chart_source E (A a))
  rw [hleft, hleftY, nativeWeilPeterssonFundamentalForm_apply, nativeWeilPeterssonFundamentalForm_apply]
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, ht] using
    congrArg (fun z : ℂ => -2 * z.im)
      (nativeWeilPeterssonCore_deformedReference_allPoints_pullback
        R hp hg hgenus hΓ hfree hsmooth ν a ((K a).symm (v 0)) ((K a).symm (v 1))).symm

/-- Every actual original real tangent pair is transported by the actual
global reference-coordinate derivative at its own point. -/
theorem nativeWeilPeterssonRealForm_deformedReference_allPoints_coordinates :
    letI := C
    letI := CY
    ∀ (a : TeichmullerSpace R) (v w : TangentSpace RI a),
      omega a ![v, w] = omegaY (A a)
        ![(DY (A a)).symm (fderiv ℝ f (BC a) (D a v)),
          (DY (A a)).symm (fderiv ℝ f (BC a) (D a w))] := by
  let := C
  let := CY
  intro a v w
  have h := nativeWeilPeterssonCoordinateForm_deformedReference_allPoints_pullback
    R hp hg hgenus hΓ hfree hsmooth ν a
  have hleft : (chart (basePoint R)).symm (BC a) = a := by
    simpa only [nativeWeilPeterssonCoordinateChart_coe] using
      (chart (basePoint R)).left_inv (mem_chart_source E a)
  have hleftY : (chartY (basePoint Y)).symm (BCY (A a)) = A a := by
    simpa only [nativeWeilPeterssonCoordinateChart_coe] using
      (chartY (basePoint Y)).left_inv (mem_chart_source E (A a))
  calc
    omega a ![v, w] = Ω (BC a) ![D a v, D a w] := by
      rw [nativeWeilPeterssonFundamentalRealCoordinateForm_apply, hleft]
      simp only [ContinuousLinearEquiv.symm_apply_apply]
    _ = ΩY (f (BC a)) ![fderiv ℝ f (BC a) (D a v), fderiv ℝ f (BC a) (D a w)] := by
      rw [h]
      rfl
    _ = omegaY (A a)
        ![(DY (A a)).symm (fderiv ℝ f (BC a) (D a v)),
          (DY (A a)).symm (fderiv ℝ f (BC a) (D a w))] := by
      rw [deformedReferenceWeilPeterssonCoordinateMap_point,
        nativeWeilPeterssonFundamentalRealCoordinateForm_apply, hleftY]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
