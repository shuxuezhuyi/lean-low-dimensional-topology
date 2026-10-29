module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaWeilPeterssonFundamentalForm

/-! The original group WP fundamental form as an actual smooth real two-form. -/

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
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : LiZhongQC.IsFuchsian Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "RI" => 𝓘(ℝ, E)
local notation "TG" => LiZhongQC.TeichGamma Γ
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "D" => canonicalGammaDiffeomorph R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => gammaWeilPeterssonCoordinateChart R hp hg hgenus hΓ
local notation "realCoord" => gammaWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ
local notation "nchart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "nrealCoord" =>
  nativeWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "nativeForm" =>
  nativeWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hfree hsmooth
local notation "nativeCoordinates" =>
  nativeWeilPeterssonFundamentalRealCoordinateForm R hp hg hgenus hΓ hfree hsmooth
local notation "modelForm" =>
  gammaWeilPeterssonFundamentalModelForm R hp hg hgenus hΓ hsmooth
local notation "realForm" => gammaWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hsmooth
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  (I := RI) (n := ω) (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp)
local instance : Nonempty TG := ⟨LiZhongQC.TeichGamma.origin Γ⟩

/-- Every actual group point has the same full coordinate form as its native point. -/
theorem gammaWeilPeterssonFundamentalModelForm_coordinates (b a : TG) :
    letI := C; letI := mΓ; letI := CG
    modelForm a = nativeCoordinates ((D).symm b) ((chart b) a) := by
  let := C; let := mΓ; let := CG
  have ha : a ∈ (chart b).source := mem_chart_source E a
  have h := gammaWeilPeterssonCoordinateChart_symm_native R hp hg hgenus hΓ hsmooth
    b ((chart b) a) ((chart b).map_source ha)
  rw [(chart b).left_inv ha] at h
  exact congrArg (fun q : TeichmullerSpace.{0,0} R =>
    (nativeForm q).compContinuousLinearMap (nrealCoord q).symm.toContinuousLinearMap) h

/-- These are the genuine alternating tangent-bundle coordinates. -/
theorem gammaWeilPeterssonRealFundamentalForm_coordinates (b a : TG) :
    letI := C; letI := mΓ; letI := CG; letI : IsManifold RI ω TG := realManifold
    (realForm a).compContinuousLinearMap
        ((trivializationAt E (TangentSpace RI) b).symmL ℝ a) =
      nativeCoordinates ((D).symm b) ((chart b) a) := by
  let := C; let := mΓ; let := CG; let : IsManifold RI ω TG := realManifold
  rw [gammaWeilPeterssonRealTangentCoordinateEquiv_symmL]
  calc
    _ = modelForm a := by
      apply ContinuousAlternatingMap.ext
      intro v
      change modelForm a (fun i => realCoord a ((realCoord a).symm (v i))) = modelForm a v
      exact congrArg (modelForm a) (funext fun i => (realCoord a).apply_symm_apply (v i))
    _ = _ := gammaWeilPeterssonFundamentalModelForm_coordinates R hp hg hgenus hΓ hsmooth b a

/-- The original group form is a globally smooth section under the existing hWP input. -/
theorem contMDiff_gammaWeilPeterssonRealFundamentalForm_of_localSmoothness
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C; letI := mΓ; letI := CG; letI : IsManifold RI ω TG := realManifold
    ContMDiff RI (ModelWithCorners.prod RI 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ)) ∞
      (fun a => TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ) a (realForm a)) := by
  let := C; let := mΓ; let := CG; let : IsManifold RI ω TG := realManifold
  intro b
  apply (Bundle.contMDiffAt_section b).mpr
  simp only [FormInterior.form_trivialization]
  have ht : (chart b) b ∈ (nchart ((D).symm b)).target := by
    rw [← gammaWeilPeterssonCoordinateChart_target_eq_native R hp hg hgenus hΓ hsmooth b]
    exact (chart b).map_source (mem_chart_source E b)
  have hA := (contDiffOn_nativeWeilPeterssonFundamentalRealCoordinateForm_of_localSmoothness
    R hp hg hgenus hΓ hfree hsmooth hWP ((D).symm b)).contDiffAt
      ((nchart ((D).symm b)).open_target.mem_nhds ht)
  have hc : ContMDiffAt RI RI ∞ (chart b) b := by
    change ContMDiffAt RI RI ∞ (extChartAt RI b) b
    exact contMDiffAt_extChartAt
  apply (hA.comp_contMDiffAt hc).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun a =>
    gammaWeilPeterssonRealFundamentalForm_coordinates R hp hg hgenus hΓ hsmooth b a

/-- The English-normalized original group WP smooth real differential two-form. -/
def gammaWeilPeterssonSmoothFundamentalForm
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C; letI := mΓ; letI := CG; letI : IsManifold RI ω TG := realManifold
    FormInterior.SmoothForm RI (M := TG) 2 := by
  let := C; let := mΓ; let := CG; let : IsManifold RI ω TG := realManifold
  exact ⟨realForm, contMDiff_gammaWeilPeterssonRealFundamentalForm_of_localSmoothness
    R hp hg hgenus hΓ hsmooth hWP⟩

/-- The bundled smooth form still has the literal original group Core value. -/
@[simp] theorem gammaWeilPeterssonSmoothFundamentalForm_apply
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) (a : TG) :
    letI := C; letI := mΓ; letI := CG; letI : IsManifold RI ω TG := realManifold
    ∀ v : Fin 2 → TangentSpace RI a,
      gammaWeilPeterssonSmoothFundamentalForm R hp hg hgenus hΓ hsmooth hWP a v =
        -2 * ((gammaWeilPeterssonCore R hp hg hgenus hΓ hsmooth a).inner
          (gammaRealComplexTangentEquiv R hp hg hgenus hΓ a (v 1))
          (gammaRealComplexTangentEquiv R hp hg hgenus hΓ a (v 0))).im := by
  let := C; let := mΓ; let := CG; let : IsManifold RI ω TG := realManifold
  exact gammaWeilPeterssonRealFundamentalForm_apply R hp hg hgenus hΓ hsmooth a

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
