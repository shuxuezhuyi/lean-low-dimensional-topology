module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaWeilPeterssonCoordinatePairing

/-! The original group WP real form in the actual original real tangent fibres. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Bornology
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
local notation "coord" => gammaWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ
local notation "realCoord" => gammaWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ
local notation "realify" => gammaRealComplexTangentEquiv R hp hg hgenus hΓ
local notation "nmodel" => nativeWeilPeterssonRealModelForm R hp hg hgenus hΓ hfree hsmooth

/-- The original group pairing in the same actual model coordinates. -/
def gammaWeilPeterssonRealModelForm (a : TG) : E →L[ℝ] E →L[ℝ] ℝ := by
  let := C; let := mΓ; let := CG
  exact nmodel ((D).symm a)
local notation "modelForm" => gammaWeilPeterssonRealModelForm R hp hg hgenus hΓ hsmooth

/-- Pull back the same original model form through the actual real Bers differential. -/
def gammaWeilPeterssonRealTangentForm (a : TG) :
    letI := mΓ; letI := CG; TangentSpace RI a →L[ℝ] TangentSpace RI a →L[ℝ] ℝ := by
  let := mΓ; let := CG
  let : IsNormableSpace ℝ (TangentSpace RI a) := (realCoord a).isNormableSpace
  exact ContinuousLinearMap.bilinearComp (modelForm a)
    (realCoord a).toContinuousLinearMap (realCoord a).toContinuousLinearMap
local notation "realForm" => gammaWeilPeterssonRealTangentForm R hp hg hgenus hΓ hsmooth

/-- The value is the English twice-real-part of the original selected group Core. -/
theorem gammaWeilPeterssonRealTangentForm_apply (a : TG) :
    letI := C; letI := mΓ; letI := CG
    ∀ v w : TangentSpace RI a,
      realForm a v w = 2 * ((HG a).inner (realify a w) (realify a v)).re := by
  let := C; let := mΓ; let := CG
  intro v w
  change nmodel ((D).symm a) (realCoord a v) (realCoord a w) = _
  have hK (u : TangentSpace RI a) : (coord a).symm (realCoord a u) = realify a u :=
    (coord a).symm_apply_apply (realify a u)
  exact (gammaWeilPeterssonRealModelForm_coordinate R hp hg hgenus hΓ hsmooth a
    (realCoord a v) (realCoord a w)).symm.trans
      (congrArg (fun z : ℂ => 2 * z.re)
        (congrArg₂ ((HG a).inner) (hK w) (hK v)))

/-- Actual inverse tangent coordinates recover the same model pairing. -/
theorem gammaWeilPeterssonRealTangentForm_coordinate_apply (a : TG) (v w : E) :
    letI := mΓ; letI := CG
    realForm a ((realCoord a).symm v) ((realCoord a).symm w) = modelForm a v w := by
  let := mΓ; let := CG
  change modelForm a (realCoord a ((realCoord a).symm v))
    (realCoord a ((realCoord a).symm w)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- Symmetry uses the original Hermitian family, with its unchanged source convention. -/
theorem gammaWeilPeterssonRealTangentForm_symm (a : TG) :
    letI := C; letI := mΓ; letI := CG
    ∀ v w, realForm a v w = realForm a w v := by
  let := C; let := mΓ; let := CG
  intro v w
  rw [gammaWeilPeterssonRealTangentForm_apply, gammaWeilPeterssonRealTangentForm_apply]
  simpa only [Complex.conj_re] using congrArg (fun z : ℂ => 2 * z.re)
    ((HG a).conj_inner_symm (realify a v) (realify a w))

/-- Strict positivity is inherited from the unchanged positive model form. -/
theorem gammaWeilPeterssonRealTangentForm_pos (a : TG) :
    letI := mΓ; letI := CG
    ∀ v, v ≠ 0 → 0 < realForm a v v := by
  let := C; let := mΓ; let := CG
  intro v hv
  change 0 < nmodel ((D).symm a) (realCoord a v) (realCoord a v)
  exact nativeWeilPeterssonRealModelForm_pos R hp hg hgenus hΓ hfree hsmooth _ _
    ((realCoord a).toLinearEquiv.map_ne_zero_iff.mpr hv)

/-- Unit sublevels are bounded in the pre-existing actual group tangent topology. -/
theorem gammaWeilPeterssonRealTangentForm_isVonNBounded (a : TG) :
    letI := mΓ; letI := CG
    IsVonNBounded ℝ {v : TangentSpace RI a | realForm a v v < 1} := by
  let := C; let := mΓ; let := CG
  have hB := Auxiliary.Analysis.quadraticForm_isVonNBounded (modelForm a)
    (nativeWeilPeterssonRealModelForm_pos R hp hg hgenus hΓ hfree hsmooth ((D).symm a))
  apply (hB.image (realCoord a).symm.toContinuousLinearMap).subset
  intro v hv
  refine ⟨realCoord a v, ?_, (realCoord a).symm_apply_apply v⟩
  change modelForm a (realCoord a v) (realCoord a v) < 1
  exact hv
end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
