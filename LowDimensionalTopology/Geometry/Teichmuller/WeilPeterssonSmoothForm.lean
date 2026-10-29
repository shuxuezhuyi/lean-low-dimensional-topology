module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonRealForm
public import LowDimensionalTopology.Geometry.Teichmuller.NativeRealTangentTrivialization
public import LowDimensionalTopology.Geometry.Teichmuller.SmoothFormInterior
public import LowDimensionalTopology.Geometry.Teichmuller.SmoothTwoFormCoordinates

/-!
# The original WP fundamental form as a smooth real tangent two-form

The fibre value is precisely the same-point realification pullback of the
original fundamental form, with English normalization `-2 Im h`. Its actual
inverse real Bers coordinates are smooth under the existing explicit analytic
input. The actual alternating tangent bundle then supplies the smooth section.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set Filter Topology
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
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "coord" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "realify" => nativeRealComplexTangentEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "realCoord" =>
  nativeWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "originalForm" =>
  nativeWeilPeterssonFundamentalForm R hp hg hgenus hΓ hfree hsmooth
local notation "realManifold" =>
  Topology.IsOpenEmbedding.isManifold_singleton (I := RI) (n := ω)
    (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth)

/-- The same original WP fundamental form on the actual real tangent fibre. -/
def nativeWeilPeterssonRealFundamentalForm (q : TeichmullerSpace.{0,0} R) :
    letI := C
    TangentSpace RI q [⋀^Fin 2]→L[ℝ] ℝ := by
  let := C
  exact (originalForm q).compContinuousLinearMap (realify q).toContinuousLinearMap

local notation "realForm" =>
  nativeWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hfree hsmooth

/-- Every value is exactly the original form pulled back by same-point
realification, without changing its first-linear convention or factor. -/
@[simp] theorem nativeWeilPeterssonRealFundamentalForm_apply
    (q : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v : Fin 2 → TangentSpace RI q,
      realForm q v = originalForm q (fun i => realify q (v i)) := by
  let := C
  exact fun _ => rfl

/-- Actual inverse real tangent coordinates agree with the original inverse
complex coordinates after the same-point identification. -/
theorem nativeWeilPeterssonRealFundamentalForm_inverse_coordinates
    (q : TeichmullerSpace.{0,0} R) (v w : E) :
    letI := C
    realForm q ![(realCoord q).symm v, (realCoord q).symm w] =
      originalForm q ![(coord q).symm v, (coord q).symm w] := by
  let := C
  rw [nativeWeilPeterssonRealFundamentalForm_apply]
  exact congrArg (originalForm q) (by
    funext i
    fin_cases i <;> rfl)

/-- The actual inverse-real-coordinate evaluation is smooth under the same
named local coefficient input as the original tangent form. -/
theorem contDiffOn_nativeWeilPeterssonRealFundamentalForm_inverse_coordinates_of_localSmoothness
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) (a : TeichmullerSpace.{0,0} R) (v w : E) :
    letI := C
    ContDiffOn ℝ ∞ (fun t => let q := (chart a).symm t
      realForm q ![(realCoord q).symm v, (realCoord q).symm w]) (chart a).target := by
  let := C
  apply (contDiffOn_nativeWeilPeterssonFundamentalForm_of_localSmoothness
    R hp hg hgenus hΓ hfree hsmooth hWP a v w).congr
  intro t _
  exact nativeWeilPeterssonRealFundamentalForm_inverse_coordinates
    R hp hg hgenus hΓ hfree hsmooth ((chart a).symm t) v w

/-- The entire actual two-form in the actual inverse real Bers coordinates. -/
def nativeWeilPeterssonFundamentalRealCoordinateForm
    (a : TeichmullerSpace.{0,0} R) (t : E) : E [⋀^Fin 2]→L[ℝ] ℝ := by
  let := C
  let q := (chart a).symm t
  exact (realForm q).compContinuousLinearMap (realCoord q).symm.toContinuousLinearMap

local notation "coordinateForm" =>
  nativeWeilPeterssonFundamentalRealCoordinateForm R hp hg hgenus hΓ hfree hsmooth

/-- Its evaluations are evaluations on the actual inverse real tangent frame. -/
@[simp] theorem nativeWeilPeterssonFundamentalRealCoordinateForm_apply
    (a : TeichmullerSpace.{0,0} R) (t v w : E) :
    letI := C
    coordinateForm a t ![v, w] =
      realForm ((chart a).symm t)
        ![(realCoord ((chart a).symm t)).symm v,
          (realCoord ((chart a).symm t)).symm w] := by
  let := C
  change realForm ((chart a).symm t)
      (fun i => (realCoord ((chart a).symm t)).symm (![v, w] i)) = _
  congr 1
  ext i
  fin_cases i <;> rfl

/-- Smoothness holds in the normed space of entire actual coordinate two-forms. -/
theorem contDiffOn_nativeWeilPeterssonFundamentalRealCoordinateForm_of_localSmoothness
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) (a : TeichmullerSpace.{0,0} R) :
    ContDiffOn ℝ ∞ (coordinateForm a) (chart a).target := by
  let := C
  apply FormInterior.contDiffOn_twoForm_of_evaluations
  intro v w
  apply (contDiffOn_nativeWeilPeterssonRealFundamentalForm_inverse_coordinates_of_localSmoothness
    R hp hg hgenus hΓ hfree hsmooth hWP a v w).congr
  intro t _
  exact nativeWeilPeterssonFundamentalRealCoordinateForm_apply
    R hp hg hgenus hΓ hfree hsmooth a t v w

/-- The genuine tangent inverse trivialization gives precisely these coordinates. -/
theorem nativeWeilPeterssonRealFundamentalForm_coordinates
    (a q : TeichmullerSpace.{0,0} R) :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
    (realForm q).compContinuousLinearMap
        ((trivializationAt E (TangentSpace RI) a).symmL ℝ q) =
      coordinateForm a ((chart a) q) := by
  let := C
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
  rw [nativeWeilPeterssonRealTangentCoordinateEquiv_symmL]
  change (realForm q).compContinuousLinearMap (realCoord q).symm.toContinuousLinearMap =
    (realForm ((chart a).symm ((chart a) q))).compContinuousLinearMap
      (realCoord ((chart a).symm ((chart a) q))).symm.toContinuousLinearMap
  rw [(chart a).left_inv (show q ∈ (chart a).source from mem_chart_source E q)]

/-- The actual alternating tangent bundle section is globally smooth. -/
theorem contMDiff_nativeWeilPeterssonRealFundamentalForm_of_localSmoothness
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
    ContMDiff RI (ModelWithCorners.prod RI 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ)) ∞
      (fun q => TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ) q (realForm q)) := by
  let := C
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
  intro a
  apply (Bundle.contMDiffAt_section a).mpr
  simp only [FormInterior.form_trivialization]
  have ht : (chart a) a ∈ (chart a).target :=
    (chart a).map_source (mem_chart_source E a)
  have hA := (contDiffOn_nativeWeilPeterssonFundamentalRealCoordinateForm_of_localSmoothness
    R hp hg hgenus hΓ hfree hsmooth hWP a).contDiffAt ((chart a).open_target.mem_nhds ht)
  have hc : ContMDiffAt RI RI ∞ (chart a) a := by
    change ContMDiffAt RI RI ∞ (extChartAt RI a) a
    exact contMDiffAt_extChartAt
  apply (hA.comp_contMDiffAt hc).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun q =>
    nativeWeilPeterssonRealFundamentalForm_coordinates R hp hg hgenus hΓ hfree hsmooth a q

/-- The original WP fundamental form as an actual smooth real differential form. -/
def nativeWeilPeterssonSmoothFundamentalForm
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
    FormInterior.SmoothForm RI (M := TeichmullerSpace.{0,0} R) 2 := by
  let := C
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
  exact ⟨realForm, contMDiff_nativeWeilPeterssonRealFundamentalForm_of_localSmoothness
    R hp hg hgenus hΓ hfree hsmooth hWP⟩

/-- The bundled smooth form retains exactly the original same-point fibre value. -/
@[simp] theorem nativeWeilPeterssonSmoothFundamentalForm_apply
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) (q : TeichmullerSpace.{0,0} R) :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
    ∀ v : Fin 2 → TangentSpace RI q,
      nativeWeilPeterssonSmoothFundamentalForm R hp hg hgenus hΓ hfree hsmooth hWP q v =
        originalForm q (fun i => realify q (v i)) := by
  let := C
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
  exact nativeWeilPeterssonRealFundamentalForm_apply R hp hg hgenus hΓ hfree hsmooth q

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
