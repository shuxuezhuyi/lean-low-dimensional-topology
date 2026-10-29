module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonRealCoordinateOperator
public import LowDimensionalTopology.Geometry.Teichmuller.NativeRealTangentTrivialization
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.QuadraticFormMetric

/-!
# The original WP form on the actual real tangent bundle

The model form is the original complex-fibre form in its actual Bers coordinates.
The actual real-fibre form is its pullback by the same real Bers differential.
No new norm is installed on either native tangent carrier.
-/

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
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "RI" => 𝓘(ℝ, E)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "coord" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "realCoord" =>
  nativeWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "realify" => nativeRealComplexTangentEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "realBilin" => nativeWeilPeterssonRealBilinForm R hp hg hgenus hΓ hfree hsmooth

/-- The unchanged original real pairing in the actual coordinate fibre. -/
def nativeWeilPeterssonRealModelForm (a : TeichmullerSpace.{0,0} R) :
    E →L[ℝ] E →L[ℝ] ℝ := by
  let := C
  let L : TangentSpace TI a ≃ₗ[ℝ] E := (coord a).toLinearEquiv.restrictScalars ℝ
  exact LinearMap.toContinuousBilinearMap
    ((realBilin a).compl₁₂ L.symm.toLinearMap L.symm.toLinearMap)

/-- Model evaluation retains the actual inverse complex Bers differential. -/
@[simp] theorem nativeWeilPeterssonRealModelForm_apply (a : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v w : E,
      nativeWeilPeterssonRealModelForm R hp hg hgenus hΓ hfree hsmooth a v w =
        realBilin a ((coord a).symm v) ((coord a).symm w) := by
  let := C
  exact fun _ _ => rfl

/-- The previously constructed full chart operator is this same model family. -/
theorem nativeWeilPeterssonRealCoordinateOperator_eq_modelForm
    (a : TeichmullerSpace.{0,0} R) (t : E) :
    nativeWeilPeterssonRealCoordinateOperator R hp hg hgenus hΓ hfree hsmooth a t =
      nativeWeilPeterssonRealModelForm R hp hg hgenus hΓ hfree hsmooth
        ((chart a).symm t) := rfl

/-- Strict positivity in the existing normed finite-dimensional model. -/
theorem nativeWeilPeterssonRealModelForm_pos (a : TeichmullerSpace.{0,0} R)
    (v : E) (hv : v ≠ 0) :
    0 < nativeWeilPeterssonRealModelForm R hp hg hgenus hΓ hfree hsmooth a v v := by
  let := C
  rw [nativeWeilPeterssonRealModelForm_apply]
  exact nativeWeilPeterssonRealBilinForm_pos R hp hg hgenus hΓ hfree hsmooth a _
    ((coord a).symm.toLinearEquiv.map_ne_zero_iff.mpr hv)

/-- The original twice-real-part form on the actual real tangent fibre. -/
def nativeWeilPeterssonRealTangentForm (a : TeichmullerSpace.{0,0} R) :
    letI := C
    TangentSpace RI a →L[ℝ] TangentSpace RI a →L[ℝ] ℝ := by
  let := C
  let : IsNormableSpace ℝ (TangentSpace RI a) := (realCoord a).isNormableSpace
  exact ContinuousLinearMap.bilinearComp
    (nativeWeilPeterssonRealModelForm R hp hg hgenus hΓ hfree hsmooth a)
    (realCoord a).toContinuousLinearMap (realCoord a).toContinuousLinearMap

/-- Evaluation is the original form under the same-point realification. -/
@[simp] theorem nativeWeilPeterssonRealTangentForm_apply (a : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v w : TangentSpace RI a,
      nativeWeilPeterssonRealTangentForm R hp hg hgenus hΓ hfree hsmooth a v w =
        realBilin a (realify a v) (realify a w) := by
  let := C
  intro v w
  have hK (u : TangentSpace RI a) : (coord a).symm (realCoord a u) = realify a u :=
    (coord a).symm_apply_apply (realify a u)
  simp only [nativeWeilPeterssonRealTangentForm, ContinuousLinearMap.bilinearComp_apply,
    nativeWeilPeterssonRealModelForm_apply]
  exact congrArg₂ (fun u z : TangentSpace TI a => realBilin a u z) (hK v) (hK w)

/-- Pulling the actual form back by its actual inverse tangent coordinates
recovers the original model form. -/
theorem nativeWeilPeterssonRealTangentForm_coordinate_apply
    (a : TeichmullerSpace.{0,0} R) (v w : E) :
    letI := C
    nativeWeilPeterssonRealTangentForm R hp hg hgenus hΓ hfree hsmooth a
        ((realCoord a).symm v) ((realCoord a).symm w) =
      nativeWeilPeterssonRealModelForm R hp hg hgenus hΓ hfree hsmooth a v w := by
  let := C
  change nativeWeilPeterssonRealModelForm R hp hg hgenus hΓ hfree hsmooth a
      (realCoord a ((realCoord a).symm v)) (realCoord a ((realCoord a).symm w)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- Symmetry of the original WP real form on the actual real tangent fibre. -/
theorem nativeWeilPeterssonRealTangentForm_symm (a : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v w, nativeWeilPeterssonRealTangentForm R hp hg hgenus hΓ hfree hsmooth a v w =
      nativeWeilPeterssonRealTangentForm R hp hg hgenus hΓ hfree hsmooth a w v := by
  let := C
  intro v w
  rw [nativeWeilPeterssonRealTangentForm_apply, nativeWeilPeterssonRealTangentForm_apply]
  exact nativeWeilPeterssonRealBilinForm_symm R hp hg hgenus hΓ hfree hsmooth a _ _

/-- Strict positivity on the same original real tangent carrier. -/
theorem nativeWeilPeterssonRealTangentForm_pos (a : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v, v ≠ 0 → 0 <
      nativeWeilPeterssonRealTangentForm R hp hg hgenus hΓ hfree hsmooth a v v := by
  let := C
  intro v hv
  rw [nativeWeilPeterssonRealTangentForm_apply]
  exact nativeWeilPeterssonRealBilinForm_pos R hp hg hgenus hΓ hfree hsmooth a _
    ((realify a).toLinearEquiv.map_ne_zero_iff.mpr hv)

/-- The positive unit sublevel is bounded for the pre-existing tangent topology.
This is the finite-dimensional model theorem followed by the actual inverse chart. -/
theorem nativeWeilPeterssonRealTangentForm_isVonNBounded (a : TeichmullerSpace.{0,0} R) :
    letI := C
    IsVonNBounded ℝ {v : TangentSpace RI a |
      nativeWeilPeterssonRealTangentForm R hp hg hgenus hΓ hfree hsmooth a v v < 1} := by
  let := C
  let B := nativeWeilPeterssonRealModelForm R hp hg hgenus hΓ hfree hsmooth a
  have hB : IsVonNBounded ℝ {v : E | B v v < 1} :=
    Auxiliary.Analysis.quadraticForm_isVonNBounded B
      (nativeWeilPeterssonRealModelForm_pos R hp hg hgenus hΓ hfree hsmooth a)
  apply (hB.image (realCoord a).symm.toContinuousLinearMap).subset
  intro v hv
  refine ⟨realCoord a v, ?_, (realCoord a).symm_apply_apply v⟩
  change B (realCoord a v) (realCoord a v) < 1
  change nativeWeilPeterssonRealTangentForm R hp hg hgenus hΓ hfree hsmooth a v v < 1 at hv
  exact hv

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
