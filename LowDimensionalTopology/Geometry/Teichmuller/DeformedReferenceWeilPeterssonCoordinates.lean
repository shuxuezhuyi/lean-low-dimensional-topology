module

public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceWeilPeterssonNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonBaseCoordinateClosedness
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Actual finite Bers coordinates for the WP reference pullback

Both coordinate maps use the original normalized translation and its actual
analytic inverse on the full open Bers images. The local coordinate tensor
identity follows from the actual harmonic-naturalness consumer. Differentiability
at the deformed origin is transported from the fixed original surface only.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "W" => weightedLinearBersCoordinates R hg hgenus hP hΓ hp
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "U" => PartialEquiv.target (PartialHomeomorph.toPartialEquiv
  (OpenPartialHomeomorph.toPartialHomeomorph (chart (basePoint R))))
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

/-- The target is precisely the range of the actual singleton native Bers chart. -/
theorem nativeWeilPeterssonCoordinateChart_target_eq_range (a : TeichmullerSpace.{0,0} R) :
    (chart a).target = range BC := by
  change (Topology.IsOpenEmbedding.toOpenPartialHomeomorph BC
    (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth)).target = _
  exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target _ _

private theorem wp_weighted_mem_iff (t : E) :
    (W).symm t ∈ coefficientBersImage hΓ ↔ t ∈ U := by
  rw [nativeWeilPeterssonCoordinateChart_target_eq_range]
  constructor
  · intro ht
    obtain ⟨μ, hμ⟩ := (mem_coefficientBersImage_iff_coefficient hΓ _).mp ht
    refine ⟨coefficientProjectionBall R hg hgenus hP hΓ hfree hp μ, ?_⟩
    rw [coefficientProjectionBall_coordinates, hμ, (W).apply_symm_apply]
  · rintro ⟨a, rfl⟩
    obtain ⟨μ, rfl⟩ := coefficientProjectionBall_surjective R hg hgenus hΓ hfree hp a
    rw [coefficientProjectionBall_coordinates, (W).symm_apply_apply]
    exact (mem_coefficientBersImage_iff_coefficient hΓ _).mpr ⟨μ, rfl⟩

variable (ν : Ball Γ)
local notation "Y" => deformedNativeSurface R hgenus hΓ hp ν
local notation "hY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "Δ" => deformedGroup hΓ ν
local notation "hΔ" => And.left (deformedGroup_spec hΓ ν)
local notation "hfY" => deformedNativeSurface_actsFreely R hgenus hΓ hp ν
local notation "CY" => canonicalComplexChartedSpace Y hg hY hP hΔ hfY hpY hsmooth
local notation "BCY" => bersCoordinates Y hg hY hP hΔ hfY hpY
local notation "WY" => weightedLinearBersCoordinates Y hg hY hP hΔ hpY
local notation "KY" => nativeWeilPeterssonCoordinateEquiv Y hpY hg hY hΔ hfY hsmooth
local notation "chartY" => nativeWeilPeterssonCoordinateChart Y hpY hg hY hΔ hfY hsmooth
local notation "UY" => PartialEquiv.target (PartialHomeomorph.toPartialEquiv
  (OpenPartialHomeomorph.toPartialHomeomorph (chartY (basePoint Y))))
local notation "ΩY" => nativeWeilPeterssonFundamentalRealCoordinateForm
  Y hpY hg hY hΔ hfY hsmooth (basePoint Y)
local notation "A" => deformedReferenceChangeEquiv R hp hg hgenus hΓ ν

/-- The genuine normalized reference change in the original finite Bers coordinates. -/
def deformedReferenceWeilPeterssonCoordinateMap (t : E) : E :=
  WY (bersTranslation hΓ ν ((W).symm t))

/-- Its genuine inverse, using the existing full inverse Bers translation. -/
def deformedReferenceWeilPeterssonInverseCoordinateMap (t : E) : E :=
  W (inverseBersTranslation hΓ ν ((WY).symm t))

local notation "f" => deformedReferenceWeilPeterssonCoordinateMap R hp hg hgenus hΓ ν
local notation "q" => deformedReferenceWeilPeterssonInverseCoordinateMap R hp hg hgenus hΓ ν

/-- Both literal coordinate maps are analytic on their actual full targets. -/
theorem deformedReferenceWeilPeterssonCoordinateMap_analytic :
    AnalyticOnNhd ℂ f U ∧ AnalyticOnNhd ℂ q UY := by
  constructor
  · intro t ht
    exact ((WY).toContinuousLinearMap.analyticAt _).comp
      (((analyticOnNhd_bersTranslation_coefficientBersImage R hp hg hgenus hΓ ν) _
        ((wp_weighted_mem_iff R hp hg hgenus hΓ hfree hsmooth t).mpr ht)).comp
          ((W).symm.toContinuousLinearMap.analyticAt t))
  · intro t ht
    exact ((W).toContinuousLinearMap.analyticAt _).comp
      (((analyticOnNhd_inverseBersTranslation_coefficientBersImage R hp hg hgenus hΓ ν) _
        ((wp_weighted_mem_iff Y hpY hg hY hΔ hfY hsmooth t).mpr ht)).comp
          ((WY).symm.toContinuousLinearMap.analyticAt t))

/-- The maps respect the actual open source and target, and are inverses there. -/
theorem deformedReferenceWeilPeterssonCoordinateMap_domains :
    MapsTo f U UY ∧ MapsTo q UY U ∧
      (∀ t ∈ U, q (f t) = t) ∧ (∀ t ∈ UY, f (q t) = t) := by
  let e := coefficientBersTranslationEquiv hΓ ν
  have hf : MapsTo f U UY := by
    intro t ht
    apply (wp_weighted_mem_iff Y hpY hg hY hΔ hfY hsmooth (f t)).mp
    change (WY).symm (WY (bersTranslation hΓ ν ((W).symm t))) ∈ coefficientBersImage hΔ
    rw [(WY).symm_apply_apply]
    exact bersTranslation_mapsTo_coefficientBersImage hΓ ν
      ((wp_weighted_mem_iff R hp hg hgenus hΓ hfree hsmooth t).mpr ht)
  have hq : MapsTo q UY U := by
    intro t ht
    have hm := (wp_weighted_mem_iff Y hpY hg hY hΔ hfY hsmooth t).mpr ht
    apply (wp_weighted_mem_iff R hp hg hgenus hΓ hfree hsmooth (q t)).mp
    change (W).symm (W (inverseBersTranslation hΓ ν ((WY).symm t))) ∈ coefficientBersImage hΓ
    rw [(W).symm_apply_apply, inverseBersTranslation_eq_equiv_symm hΓ ν ⟨_, hm⟩]
    exact (e.symm ⟨_, hm⟩).property
  refine ⟨hf, hq, ?_, ?_⟩
  · intro t ht
    let φ : coefficientBersImage hΓ :=
      ⟨(W).symm t, (wp_weighted_mem_iff R hp hg hgenus hΓ hfree hsmooth t).mpr ht⟩
    have hi : inverseBersTranslation hΓ ν (bersTranslation hΓ ν φ.val) = φ.val := by
      rw [← coefficientBersTranslationEquiv_apply hΓ ν φ,
        inverseBersTranslation_eq_equiv_symm]
      exact congrArg Subtype.val (e.symm_apply_apply φ)
    change W (inverseBersTranslation hΓ ν
      ((WY).symm (WY (bersTranslation hΓ ν ((W).symm t))))) = t
    rw [(WY).symm_apply_apply, hi, (W).apply_symm_apply]
  · intro t ht
    let ψ : coefficientBersImage hΔ :=
      ⟨(WY).symm t, (wp_weighted_mem_iff Y hpY hg hY hΔ hfY hsmooth t).mpr ht⟩
    have hi : bersTranslation hΓ ν (inverseBersTranslation hΓ ν ψ.val) = ψ.val := by
      rw [inverseBersTranslation_eq_equiv_symm hΓ ν ψ]
      rw [← coefficientBersTranslationEquiv_apply hΓ ν (e.symm ψ)]
      exact congrArg Subtype.val (e.apply_symm_apply ψ)
    change WY (bersTranslation hΓ ν
      ((W).symm (W (inverseBersTranslation hΓ ν ((WY).symm t))))) = t
    rw [(W).symm_apply_apply, hi, (WY).apply_symm_apply]

/-- This coordinate expression is the actual marked reference map at every native point. -/
theorem deformedReferenceWeilPeterssonCoordinateMap_point (a : TeichmullerSpace.{0,0} R) :
    f (BC a) = BCY (A a) :=
  (deformedReferenceChangeEquiv_bersCoordinates R hp hg hgenus hΓ hfree ν a).symm

/-- The native coefficient centre, expressed in its actual native Bers coordinates,
is sent to the actual deformed origin. -/
theorem deformedReferenceWeilPeterssonCoordinateMap_center : f (BC (β ν.val)) = 0 := by
  rw [deformedReferenceWeilPeterssonCoordinateMap_point,
    deformedReferenceChangeEquiv_base, bersCoordinates_basePoint]

include hsmooth in
/-- The actual inverse sends that actual origin back to the original coefficient centre. -/
theorem deformedReferenceWeilPeterssonInverseCoordinateMap_zero : q 0 = BC (β ν.val) := by
  have ht : BC (β ν.val) ∈ U := by
    rw [nativeWeilPeterssonCoordinateChart_target_eq_range]
    exact mem_range_self _
  have h := (deformedReferenceWeilPeterssonCoordinateMap_domains
    R hp hg hgenus hΓ hfree hsmooth ν).2.2.1 _ ht
  rwa [deformedReferenceWeilPeterssonCoordinateMap_center] at h

private theorem wp_deformed_origin_mem : (0 : E) ∈ UY := by
  rw [nativeWeilPeterssonCoordinateChart_target_eq_range]
  exact ⟨basePoint Y, bersCoordinates_basePoint Y hg hY hP hΔ hfY hpY⟩

/-- The coordinate derivative is the derivative of the original reference map
in the actual complex Bers frames, with no replacement tangent operator. -/
theorem deformedReferenceWeilPeterssonCoordinateMap_tangent :
    letI := C; letI := CY
    ∀ (a : TeichmullerSpace.{0,0} R) (v : TangentSpace TI a),
      KY (A a) (mfderiv TI TI A a v) = fderiv ℝ f (BC a) (K a v) := by
  let := C; let := CY
  intro a v
  have ht : BC a ∈ U := by
    rw [nativeWeilPeterssonCoordinateChart_target_eq_range]
    exact mem_range_self a
  have hχ := ((analyticOnNhd_bersTranslation_coefficientBersImage R hp hg hgenus hΓ ν) _
    ((wp_weighted_mem_iff R hp hg hgenus hΓ hfree hsmooth (BC a)).mpr ht)).differentiableAt
  have hd : HasFDerivAt f
      (((WY).toContinuousLinearMap.comp (fderiv ℂ (bersTranslation hΓ ν) ((W).symm (BC a)))).comp
        (W).symm.toContinuousLinearMap) (BC a) :=
    ((WY).toContinuousLinearMap.hasFDerivAt.comp _ hχ.hasFDerivAt).comp _
      (W).symm.toContinuousLinearMap.hasFDerivAt
  rw [hd.differentiableAt.fderiv_restrictScalars (𝕜 := ℝ), hd.fderiv]
  change WY (canonicalBersTangentEquiv Y hg hY hP hΔ hfY hpY hsmooth (A a)
    (mfderiv TI TI A a v)) = WY (fderiv ℂ (bersTranslation hΓ ν) ((W).symm (BC a))
      ((W).symm (W (canonicalBersTangentEquiv R hg hgenus hP hΓ hfree hp hsmooth a v))))
  rw [(W).symm_apply_apply]
  exact congrArg WY (deformedReferenceChangeEquiv_mfderiv_bersCoordinates
    R hp hg hgenus hΓ hfree ν hsmooth a v)

/-- On a genuine open coordinate neighborhood of the actual coefficient centre,
the actual original WP coordinate form is the ordinary differential pullback. -/
theorem nativeWeilPeterssonCoordinateForm_deformedReference_local_pullback
    (hnat : Unproved.Teichmuller.DeformedReferenceHarmonicNaturality
      R hp hg hgenus hΓ hfree hsmooth) :
    ∃ V : Set E, IsOpen V ∧ BC (β ν.val) ∈ V ∧ V ⊆ U ∧
      ∀ t ∈ V, Ω t = (ΩY (f t)).compContinuousLinearMap (fderiv ℝ f t) := by
  let := C; let := CY
  obtain ⟨V, hVo, hν, hV⟩ := nativeWeilPeterssonCore_deformedReference_local_pullback
    R hp hg hgenus hΓ hfree hsmooth ν hnat
  have hE := canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth
  refine ⟨BC '' V, hE.isOpenMap _ hVo, ⟨β ν.val, hν, rfl⟩, ?_, ?_⟩
  · rintro t ⟨a, _, rfl⟩
    rw [nativeWeilPeterssonCoordinateChart_target_eq_range]
    exact mem_range_self a
  · rintro t ⟨a, ha, rfl⟩
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
      nativeWeilPeterssonCoordinateForm_complexFrame,
      nativeWeilPeterssonCoordinateForm_complexFrame]
    have hleft : (chart (basePoint R)).symm (BC a) = a := by
      simpa only [nativeWeilPeterssonCoordinateChart_coe] using
        (chart (basePoint R)).left_inv (mem_chart_source E a)
    have hleftY : (chartY (basePoint Y)).symm (BCY (A a)) = A a := by
      simpa only [nativeWeilPeterssonCoordinateChart_coe] using
        (chartY (basePoint Y)).left_inv (mem_chart_source E (A a))
    rw [hleft, hleftY]
    rw [nativeWeilPeterssonFundamentalForm_apply, nativeWeilPeterssonFundamentalForm_apply]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, ht] using
      congrArg (fun z : ℂ => -2 * z.im) (hV a ha ((K a).symm (v 0)) ((K a).symm (v 1))).symm

/-- Only the fixed original hWP is used. The genuine analytic inverse and
local tensor identity imply differentiability of the actual deformed form at 0. -/
theorem differentiableAt_deformedWeilPeterssonCoordinateForm_zero
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (hnat : Unproved.Teichmuller.DeformedReferenceHarmonicNaturality
      R hp hg hgenus hΓ hfree hsmooth) : DifferentiableAt ℝ ΩY 0 := by
  obtain ⟨V, hVo, hν, _, hV⟩ := nativeWeilPeterssonCoordinateForm_deformedReference_local_pullback
    R hp hg hgenus hΓ hfree hsmooth ν hnat
  have ha := deformedReferenceWeilPeterssonCoordinateMap_analytic R hp hg hgenus hΓ hfree hsmooth ν
  obtain ⟨_, hqU, _, hfq⟩ := deformedReferenceWeilPeterssonCoordinateMap_domains
    R hp hg hgenus hΓ hfree hsmooth ν
  have h0 : (0 : E) ∈ UY := wp_deformed_origin_mem R hp hg hgenus hΓ hsmooth ν
  have hq0 : q 0 = BC (β ν.val) :=
    deformedReferenceWeilPeterssonInverseCoordinateMap_zero R hp hg hgenus hΓ hfree hsmooth ν
  have hqc : ContDiffAt ℝ 2 q 0 := (ha.2 0 h0).restrictScalars.contDiffAt
  have hdq := hqc.differentiableAt (by norm_num)
  have hΩ : DifferentiableAt ℝ Ω (q 0) :=
    ((contDiffOn_nativeWeilPeterssonFundamentalRealCoordinateForm_of_localSmoothness
      R hp hg hgenus hΓ hfree hsmooth hWP (basePoint R)).contDiffAt
        ((chart (basePoint R)).open_target.mem_nhds (hqU h0))).differentiableAt (by simp)
  have hdq' : DifferentiableAt ℝ (fderiv ℝ q) 0 :=
    (hqc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hρ := (hΩ.comp 0 hdq).continuousAlternatingMapCompContinuousLinearMap hdq'
  apply hρ.congr_of_eventuallyEq
  have hV0 : q 0 ∈ V := by rwa [hq0]
  filter_upwards [(chartY (basePoint Y)).open_target.mem_nhds h0,
    hdq.continuousAt.preimage_mem_nhds (hVo.mem_nhds hV0)] with y hy hyV
  have hevent : (fun z => f (q z)) =ᶠ[𝓝 y] id := by
    filter_upwards [(chartY (basePoint Y)).open_target.mem_nhds hy] with z hz
    exact hfq z hz
  have hD : (fderiv ℝ f (q y)).comp (fderiv ℝ q y) = ContinuousLinearMap.id ℝ E := by
    have h := hevent.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_fun_comp y ((ha.1 _ (hqU hy)).differentiableAt.restrictScalars ℝ)
      ((ha.2 _ hy).differentiableAt.restrictScalars ℝ), fderiv_id] at h
    exact h
  simp only [Function.comp_def]
  rw [hV (q y) hyV, hfq y hy]
  apply ContinuousAlternatingMap.ext
  intro v
  change ΩY y v = ΩY y (fun i => fderiv ℝ f (q y) (fderiv ℝ q y (v i)))
  congr 1
  funext i
  exact (congrArg (fun L : E →L[ℝ] E => L (v i)) hD).symm

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
