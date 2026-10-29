module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonRealTangentForm
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The smooth WP metric on the original real Teichmüller tangent bundle

The smoothness hypothesis is the same named original coefficient input.
The value is the unchanged original selected integral form with English factor 2.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Bornology Set Filter Topology ContinuousLinearMap
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport NativePetersson

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
local notation "realManifold" =>
  Topology.IsOpenEmbedding.isManifold_singleton (I := RI) (n := ω)
    (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth)
local notation "H" => nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "realCoord" =>
  nativeWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "realify" => nativeRealComplexTangentEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "modelForm" => nativeWeilPeterssonRealModelForm R hp hg hgenus hΓ hfree hsmooth
local notation "realForm" => nativeWeilPeterssonRealTangentForm R hp hg hgenus hΓ hfree hsmooth
local notation "FormModel" => E →L[ℝ] E →L[ℝ] ℝ

/-- The whole model-operator family is smooth as a function of the actual point. -/
theorem contMDiff_nativeWeilPeterssonRealModelForm_of_localSmoothness
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
    ContMDiff RI 𝓘(ℝ, FormModel) ∞ modelForm := by
  let := C
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
  intro a
  have hs := (contDiffOn_nativeWeilPeterssonRealCoordinateOperator_of_localSmoothness
    R hp hg hgenus hΓ hfree hsmooth hWP a).contDiffAt
      ((chart a).open_target.mem_nhds (mem_chart_target E a))
  have hc : ContMDiffAt RI RI ∞ (chart a) a := by
    change ContMDiffAt RI RI ∞ (extChartAt RI a) a
    exact contMDiffAt_extChartAt
  apply (hs.comp_contMDiffAt hc).congr_of_eventuallyEq
  filter_upwards [(chart a).open_source.mem_nhds (mem_chart_source E a)] with q hq
  rw [Function.comp_apply, nativeWeilPeterssonRealCoordinateOperator_eq_modelForm]
  have hleft : (chart a).symm ((chartAt E a) q) = q :=
    (chart a).left_inv hq
  exact congrArg
    (fun y : TeichmullerSpace.{0,0} R => (modelForm y : FormModel))
    hleft.symm

/-- The actual nested Hom-bundle coordinates are exactly the original model form. -/
theorem nativeWeilPeterssonRealTangentForm_trivialization
    (a q : TeichmullerSpace.{0,0} R) :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
    ((trivializationAt FormModel
      (fun y : TeichmullerSpace.{0,0} R => TangentSpace RI y →L[ℝ]
        TangentSpace RI y →L[ℝ] ℝ) a) ⟨q, realForm q⟩).2 = modelForm q := by
  let := C
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
  let e := trivializationAt E (TangentSpace RI) a
  have hq : q ∈ e.baseSet := mem_chart_source E q
  have hs : e.symmL ℝ q = (realCoord q).symm.toContinuousLinearMap :=
    nativeWeilPeterssonRealTangentCoordinateEquiv_symmL R hp hg hgenus hΓ hfree hsmooth a q
  have hsym (u : E) : e.symm q u = (realCoord q).symm u :=
    (e.symmL_apply (R := ℝ) hq u).symm.trans
      (congrArg (fun L : E →L[ℝ] TangentSpace RI q => L u) hs)
  rw [hom_trivializationAt_apply]
  ext v w
  change inCoordinates E (TangentSpace RI) (E →L[ℝ] ℝ)
      (fun y : TeichmullerSpace.{0,0} R => TangentSpace RI y →L[ℝ] ℝ)
      a q a q (realForm q) v w = modelForm q v w
  rw [inCoordinates_apply_eq₂ hq hq (Set.mem_univ q)]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply]
  rw [hsym v, hsym w]
  exact nativeWeilPeterssonRealTangentForm_coordinate_apply R hp hg hgenus hΓ hfree hsmooth q v w

/-- The original twice-real-part form is a smooth section of the actual tensor bundle. -/
theorem contMDiff_nativeWeilPeterssonRealTangentForm_of_localSmoothness
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
    ContMDiff RI (ModelWithCorners.prod RI 𝓘(ℝ, FormModel)) ∞
      (fun a : TeichmullerSpace.{0,0} R => TotalSpace.mk' FormModel a (realForm a)) := by
  let := C
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
  intro a
  apply (Bundle.contMDiffAt_section a).mpr
  apply (contMDiff_nativeWeilPeterssonRealModelForm_of_localSmoothness
    R hp hg hgenus hΓ hfree hsmooth hWP a).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall
    (nativeWeilPeterssonRealTangentForm_trivialization R hp hg hgenus hΓ hfree hsmooth a)

/-- The genuine smooth real WP metric on the original fixed marked quotient. -/
def nativeWeilPeterssonSmoothRealMetric
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
    Bundle.ContMDiffRiemannianMetric RI ∞ E
      (fun a : TeichmullerSpace.{0,0} R => TangentSpace RI a) := by
  let := C
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
  exact
    { inner := realForm
      symm := nativeWeilPeterssonRealTangentForm_symm R hp hg hgenus hΓ hfree hsmooth
      pos := nativeWeilPeterssonRealTangentForm_pos R hp hg hgenus hΓ hfree hsmooth
      isVonNBounded :=
        nativeWeilPeterssonRealTangentForm_isVonNBounded R hp hg hgenus hΓ hfree hsmooth
      contMDiff := contMDiff_nativeWeilPeterssonRealTangentForm_of_localSmoothness
        R hp hg hgenus hΓ hfree hsmooth hWP }

/-- The official metric has exactly the English value `2 Re h` on the original fibres. -/
theorem nativeWeilPeterssonSmoothRealMetric_inner
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) (a : TeichmullerSpace.{0,0} R) :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
    ∀ v w : TangentSpace RI a,
      (nativeWeilPeterssonSmoothRealMetric R hp hg hgenus hΓ hfree hsmooth hWP).inner a v w =
        2 * ((H a).inner (realify a w) (realify a v)).re := by
  let := C
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
  intro v w
  change realForm a v w = _
  rw [nativeWeilPeterssonRealTangentForm_apply]
  rfl

/-- Every coefficient and genuine region still computes this same metric by
the original source integral and actual harmonic tangent map. -/
theorem nativeWeilPeterssonSmoothRealMetric_integral
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
    ∀ (ν : Ball Γ)
      (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
      (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
      (v w : TangentSpace RI (β ν.val)),
      (nativeWeilPeterssonSmoothRealMetric R hp hg hgenus hΓ hfree hsmooth hWP).inner
          (β ν.val) v w =
        2 * (WeilPetersson.beltramiPairing F
          (TH ν P F hF hsmooth (realify (β ν.val) v)).val.val
          (TH ν P F hF hsmooth (realify (β ν.val) w)).val.val).re := by
  let := C
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
  intro ν P F hF v w
  rw [nativeWeilPeterssonSmoothRealMetric_inner,
    nativeWeilPeterssonCore_integral R hp hg hgenus hΓ hfree hsmooth ν P F hF]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
