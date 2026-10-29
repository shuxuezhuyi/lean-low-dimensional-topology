module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaWeilPeterssonRealTangentForm
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSmoothRealMetric

/-! The official smooth real WP metric on the full original group Teichmuller space. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set Filter Topology ContinuousLinearMap
open scoped UpperHalfPlane Manifold ContDiff
namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : LiZhongQC.IsFuchsian Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
local notation "E" => Fin (3*g-3) → ℂ
local notation "RI" => 𝓘(ℝ, E)
local notation "TG" => LiZhongQC.TeichGamma Γ
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "D" => canonicalGammaDiffeomorph R hp hg hgenus hΓ hfree hsmooth
local notation "HG" => gammaWeilPeterssonCore R hp hg hgenus hΓ hsmooth
local notation "chart" => gammaWeilPeterssonCoordinateChart R hp hg hgenus hΓ
local notation "realCoord" => gammaWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ
local notation "realify" => gammaRealComplexTangentEquiv R hp hg hgenus hΓ
local notation "modelForm" => gammaWeilPeterssonRealModelForm R hp hg hgenus hΓ hsmooth
local notation "realForm" => gammaWeilPeterssonRealTangentForm R hp hg hgenus hΓ hsmooth
local notation "nmodel" => nativeWeilPeterssonRealModelForm R hp hg hgenus hΓ hfree hsmooth
local notation "FormModel" => E →L[ℝ] E →L[ℝ] ℝ
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  (I := RI) (n := ω) (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp)
local instance : Nonempty TG := ⟨LiZhongQC.TeichGamma.origin Γ⟩

/-- Smoothness follows in the actual group chart from the same original full operator family. -/
theorem contMDiff_gammaWeilPeterssonRealModelForm_of_localSmoothness
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C; letI := mΓ; letI := CG; letI : IsManifold RI ω TG := realManifold
    ContMDiff RI 𝓘(ℝ, FormModel) ∞ modelForm := by
  let := C; let := mΓ; let := CG; let : IsManifold RI ω TG := realManifold
  intro a
  have hs := ContDiffOn.contDiffAt
    ((contDiffOn_nativeWeilPeterssonRealCoordinateOperator_of_localSmoothness
      R hp hg hgenus hΓ hfree hsmooth hWP ((D).symm a)).mono
        (gammaWeilPeterssonCoordinateChart_target_eq_native R hp hg hgenus hΓ hsmooth a).le)
    ((chart a).open_target.mem_nhds (mem_chart_target E a))
  have hc : ContMDiffAt RI RI ∞ (chart a) a := by
    change ContMDiffAt RI RI ∞ (extChartAt RI a) a
    exact contMDiffAt_extChartAt
  apply (hs.comp_contMDiffAt hc).congr_of_eventuallyEq
  filter_upwards [(chart a).open_source.mem_nhds (mem_chart_source E a)] with q hq
  rw [Function.comp_apply, nativeWeilPeterssonRealCoordinateOperator_eq_modelForm]
  have ht : (chartAt E a) q ∈ (chart a).target := (chart a).map_source hq
  have hi := gammaWeilPeterssonCoordinateChart_symm_native R hp hg hgenus hΓ hsmooth a
    ((chartAt E a) q) ht
  have hl : (chart a).symm ((chartAt E a) q) = q := (chart a).left_inv hq
  exact congrArg (fun b : TeichmullerSpace.{0,0} R => (nmodel b : FormModel))
    ((congrArg (fun z : TG => (D).symm z) hl).symm.trans hi)

/-- Actual nested Hom coordinates are exactly the original model pairing. -/
theorem gammaWeilPeterssonRealTangentForm_trivialization (a q : TG) :
    letI := mΓ; letI := CG; letI : IsManifold RI ω TG := realManifold
    ((trivializationAt FormModel (fun y : TG => TangentSpace RI y →L[ℝ]
      TangentSpace RI y →L[ℝ] ℝ) a) ⟨q, realForm q⟩).2 = modelForm q := by
  let := mΓ; let := CG; let : IsManifold RI ω TG := realManifold
  let e := trivializationAt E (TangentSpace RI) a
  have hq : q ∈ e.baseSet := mem_chart_source E q
  have hs := gammaWeilPeterssonRealTangentCoordinateEquiv_symmL R hp hg hgenus hΓ a q
  have hsym (u : E) : e.symm q u = (realCoord q).symm u :=
    (e.symmL_apply (R := ℝ) hq u).symm.trans
      (congrArg (fun L : E →L[ℝ] TangentSpace RI q => L u) hs)
  rw [hom_trivializationAt_apply]
  ext v w
  change inCoordinates E (TangentSpace RI) (E →L[ℝ] ℝ)
    (fun y : TG => TangentSpace RI y →L[ℝ] ℝ) a q a q (realForm q) v w = modelForm q v w
  rw [inCoordinates_apply_eq₂ hq hq (Set.mem_univ q)]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply]
  rw [hsym v, hsym w]
  exact gammaWeilPeterssonRealTangentForm_coordinate_apply R hp hg hgenus hΓ hsmooth q v w

/-- The genuine smooth positive metric on every actual real tangent fibre of original T(Gamma). -/
def gammaWeilPeterssonSmoothRealMetric
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C; letI := mΓ; letI := CG; letI : IsManifold RI ω TG := realManifold
    Bundle.ContMDiffRiemannianMetric RI ∞ E (fun a : TG => TangentSpace RI a) := by
  let := C; let := mΓ; let := CG; let : IsManifold RI ω TG := realManifold
  refine
    { inner := realForm
      symm := gammaWeilPeterssonRealTangentForm_symm R hp hg hgenus hΓ hsmooth
      pos := gammaWeilPeterssonRealTangentForm_pos R hp hg hgenus hΓ hsmooth
      isVonNBounded := gammaWeilPeterssonRealTangentForm_isVonNBounded R hp hg hgenus hΓ hsmooth
      contMDiff := ?_ }
  intro a
  apply (Bundle.contMDiffAt_section a).mpr
  apply (contMDiff_gammaWeilPeterssonRealModelForm_of_localSmoothness
    R hp hg hgenus hΓ hsmooth hWP a).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall
    (gammaWeilPeterssonRealTangentForm_trivialization R hp hg hgenus hΓ hsmooth a)

/-- The official metric retains the original selected group Core and exact English factor. -/
theorem gammaWeilPeterssonSmoothRealMetric_inner
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) (a : TG) :
    letI := C; letI := mΓ; letI := CG; letI : IsManifold RI ω TG := realManifold
    ∀ v w : TangentSpace RI a,
      (gammaWeilPeterssonSmoothRealMetric R hp hg hgenus hΓ hsmooth hWP).inner a v w =
        2 * ((HG a).inner (realify a w) (realify a v)).re := by
  let := C; let := mΓ; let := CG; let : IsManifold RI ω TG := realManifold
  exact gammaWeilPeterssonRealTangentForm_apply R hp hg hgenus hΓ hsmooth a

/-- Every coefficient and genuine region computes the same actual metric by its original integral. -/
theorem gammaWeilPeterssonSmoothRealMetric_integral
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C; letI := mΓ; letI := CG; letI : IsManifold RI ω TG := realManifold
    ∀ (ν : Ball Γ)
      (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
      (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
      (v w : TangentSpace RI (D (coefficientProjection R hg hgenus hP hΓ hfree hp ν.val))),
      let a := D (coefficientProjection R hg hgenus hP hΓ hfree hp ν.val)
      (gammaWeilPeterssonSmoothRealMetric R hp hg hgenus hΓ hsmooth hWP).inner a v w =
        2 * (WeilPetersson.beltramiPairing F
          (gammaWeilPeterssonTangentHarmonicEquiv R hp hg hgenus hΓ hsmooth ν P F hF
            (realify a v)).val.val
          (gammaWeilPeterssonTangentHarmonicEquiv R hp hg hgenus hΓ hsmooth ν P F hF
            (realify a w)).val.val).re := by
  let := C; let := mΓ; let := CG; let : IsManifold RI ω TG := realManifold
  intro ν P F hF v w
  dsimp only
  rw [gammaWeilPeterssonSmoothRealMetric_inner,
    gammaWeilPeterssonCore_integral R hp hg hgenus hΓ hsmooth ν P F hF]
end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
