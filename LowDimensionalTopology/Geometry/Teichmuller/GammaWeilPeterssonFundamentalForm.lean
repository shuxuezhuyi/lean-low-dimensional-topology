module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaWeilPeterssonCoordinatePairing
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSmoothForm

/-! The original group WP fundamental form, with the English factor `-2 Im h`. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : LiZhongQC.IsFuchsian Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "RI" => 𝓘(ℝ, E)
local notation "TG" => LiZhongQC.TeichGamma Γ
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "D" => canonicalGammaDiffeomorph R hp hg hgenus hΓ hfree hsmooth
local notation "HG" => gammaWeilPeterssonCore R hp hg hgenus hΓ hsmooth
local notation "HN" => nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth
local notation "gcoord" => gammaWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ
local notation "realCoord" => gammaWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ
local notation "realify" => gammaRealComplexTangentEquiv R hp hg hgenus hΓ
local notation "ncoord" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "nrealCoord" =>
  nativeWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "nativeForm" =>
  nativeWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hfree hsmooth

/-- The original native form at the corresponding point, in its actual real coordinates. -/
def gammaWeilPeterssonFundamentalModelForm (a : TG) : E [⋀^Fin 2]→L[ℝ] ℝ := by
  let := C; let := mΓ; let := CG
  exact (nativeForm ((D).symm a)).compContinuousLinearMap
    (nrealCoord ((D).symm a)).symm.toContinuousLinearMap

local notation "modelForm" =>
  gammaWeilPeterssonFundamentalModelForm R hp hg hgenus hΓ hsmooth

/-- Its literal value is the original group Core's first-linear `-2 Im` pairing. -/
theorem gammaWeilPeterssonFundamentalModelForm_apply (a : TG) :
    letI := C; letI := mΓ; letI := CG
    ∀ v : Fin 2 → E, modelForm a v =
      -2 * ((HG a).inner ((gcoord a).symm (v 1)) ((gcoord a).symm (v 0))).im := by
  let := C; let := mΓ; let := CG
  intro v
  change nativeForm ((D).symm a)
    (fun i => (nrealCoord ((D).symm a)).symm (v i)) = _
  rw [nativeWeilPeterssonRealFundamentalForm_apply, nativeWeilPeterssonFundamentalForm_apply]
  change -2 * ((HN ((D).symm a)).inner
      ((ncoord ((D).symm a)).symm (v 1)) ((ncoord ((D).symm a)).symm (v 0))).im = _
  exact (congrArg (fun z : ℂ => -2 * z.im)
    (gammaWeilPeterssonCoordinateInner_eq_native R hp hg hgenus hΓ hsmooth a (v 0) (v 1))).symm

/-- The actual continuous alternating form on the original group real tangent fibre. -/
def gammaWeilPeterssonRealFundamentalForm (a : TG) :
    letI := mΓ; letI := CG
    TangentSpace RI a [⋀^Fin 2]→L[ℝ] ℝ := by
  let := mΓ; let := CG
  exact (modelForm a).compContinuousLinearMap (realCoord a).toContinuousLinearMap

/-- Same-point realification gives exactly the original group Hermitian value. -/
@[simp] theorem gammaWeilPeterssonRealFundamentalForm_apply (a : TG) :
    letI := C; letI := mΓ; letI := CG
    ∀ v : Fin 2 → TangentSpace RI a,
      gammaWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hsmooth a v =
        -2 * ((HG a).inner (realify a (v 1)) (realify a (v 0))).im := by
  let := C; let := mΓ; let := CG
  intro v
  have hc (z : TangentSpace RI a) : (gcoord a).symm (realCoord a z) = realify a z :=
    (gcoord a).symm_apply_apply _
  change modelForm a (fun i => realCoord a (v i)) = _
  simpa only [hc] using gammaWeilPeterssonFundamentalModelForm_apply
    R hp hg hgenus hΓ hsmooth a (fun i => realCoord a (v i))

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
