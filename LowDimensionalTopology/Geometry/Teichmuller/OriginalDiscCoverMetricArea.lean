module

public import LowDimensionalTopology.Geometry.Teichmuller.DiscCoverPoincareMetric
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalTensorPairingIsothermal
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Map

/-!
# The native area of the existing disk-cover metric

The selected native area and the intrinsic hyperbolic area have the same
actual inverse-sheet density in each original chart. The comparison is local
on the unchanged original surface and uses the existing disk-cover metric.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Hyperbolic AtlasMetricConstruction

variable {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)

private theorem selected_discCover_area_on_sheet
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R
      (discCoverAtlasInducedMetric M).metric)
    (j : X) (l : OpenPartialHomeomorph extendedUnitDisc X)
    (hl : M.discCover = (l : extendedUnitDisc → X)) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    letI : MeasurableSpace X := borel X
    ∀ (s : Set X), MeasurableSet s →
      s ⊆ (chosenChart R.toRiemannSurface j).val.source ∩ l.target →
      harea.exists.choose s =
        discHyperbolicArea ((fun x => discFiniteHomeomorph (l.symm x)) '' s) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  intro s hs hsub
  let e := chosenChart R.toRiemannSurface j
  let μ : Measure X := harea.exists.choose
  let T : Set ℂ := e.val '' s
  let F := discCoverSheetCoordinate e l
  have hTs : T ⊆ e.val.target := by
    rintro _ ⟨x, hxs, rfl⟩
    exact e.val.map_source (hsub hxs).1
  have hT : MeasurableSet T := by
    have he := e.val.isOpenEmbedding_restrict.measurableEmbedding
    have hh := he.measurableSet_image.mpr (hs.preimage measurable_subtype_coe)
    have him : e.val.source.domRestrict e.val '' (Subtype.val ⁻¹' s) = T := by
      ext z
      constructor
      · rintro ⟨x, hxs, rfl⟩
        exact ⟨x.val, hxs, rfl⟩
      · rintro ⟨x, hxs, rfl⟩
        exact ⟨⟨x, (hsub hxs).1⟩, hxs, rfl⟩
    rwa [him] at hh
  have hpre : e.val ⁻¹' T ∩ e.val.source = s := by
    ext x
    constructor
    · rintro ⟨⟨y, hys, hyx⟩, hx⟩
      have heq : y = x := e.val.injOn (hsub hys).1 hx hyx
      exact heq ▸ hys
    · intro hx
      exact ⟨⟨x, hx, rfl⟩, (hsub hx).1⟩
  have hmap : Measure.map (e.val : X → ℂ) (μ.restrict e.val.source) =
      ((volume : Measure ℂ).withDensity (fun z =>
        ENNReal.ofReal ((discCoverAtlasInducedMetric M).density e (e.val.symm z)))).restrict
          e.val.target := originalMetricArea_isothermal_preferred_chart R
            (discCoverAtlasInducedMetric M) harea j
  have he : AEMeasurable (e.val : X → ℂ) (μ.restrict e.val.source) :=
    e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
  have hmu : μ s = ∫⁻ z in T,
      ENNReal.ofReal ((discCoverAtlasInducedMetric M).density e (e.val.symm z))
        ∂(volume : Measure ℂ) := by
    have hh := congrArg (fun ν : Measure ℂ => ν T) hmap
    rw [Measure.map_apply_of_aemeasurable he hT,
      Measure.restrict_apply' e.val.open_source.measurableSet, hpre,
      Measure.restrict_apply hT, Set.inter_eq_left.mpr hTs,
      withDensity_apply _ hT] at hh
    exact hh
  have hTF : T ⊆ F.source := by
    rintro _ ⟨x, hxs, rfl⟩
    have hx := hsub hxs
    change (e.val x ∈ e.val.target ∧ e.val.symm (e.val x) ∈ l.target) ∧
      l.symm (e.val.symm (e.val x)) ∈ discFiniteChart.source
    rw [e.val.left_inv hx.1, discFiniteChart_source]
    exact ⟨⟨e.val.map_source hx.1, hx.2⟩, mem_univ _⟩
  have hF : AnalyticOnNhd ℂ F F.source := discCoverSheetCoordinate_analytic M e l hl
  let D : ℂ → ℂ →L[ℝ] ℂ := fun z =>
    (ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)).restrictScalars ℝ
  have hD (z : ℂ) (hz : z ∈ T) : HasFDerivWithinAt F (D z) T z :=
    ((hF z (hTF hz)).differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet (z : ℂ) : (D z).det = ‖deriv F z‖ ^ 2 := by
    simp only [D, ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
      LinearMap.det_restrictScalars, ContinuousLinearMap.det_toSpanSingleton,
      Algebra.norm_complex_eq]
    exact Complex.normSq_eq_norm_sq _
  have hinj : Set.InjOn F T := F.injOn.mono hTF
  have hFT : MeasurableSet (F '' T) := measurable_image_of_fderivWithin hT hD hinj
  have him : ((↑) : Complex.UnitDisc → ℂ) ''
      ((fun x => discFiniteHomeomorph (l.symm x)) '' s) = F '' T := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, hxs, rfl⟩, rfl⟩
      refine ⟨e.val x, ⟨x, hxs, rfl⟩, ?_⟩
      change discFiniteChart (l.symm (e.val.symm (e.val x))) = _
      rw [e.val.left_inv (hsub hxs).1]
      rfl
    · rintro ⟨_, ⟨x, hxs, rfl⟩, rfl⟩
      refine ⟨discFiniteHomeomorph (l.symm x), ⟨x, hxs, rfl⟩, ?_⟩
      change _ = discFiniteChart (l.symm (e.val.symm (e.val x)))
      rw [e.val.left_inv (hsub hxs).1]
      rfl
  have hweight (z : ℂ) (hz : z ∈ T) :
      ENNReal.ofReal |(D z).det| * ENNReal.ofReal (discAreaDensity (F z)) =
        ENNReal.ofReal ((discCoverAtlasInducedMetric M).density e (e.val.symm z)) := by
    rcases hz with ⟨x, hxs, rfl⟩
    rw [e.val.left_inv (hsub hxs).1]
    have hd : (discCoverAtlasInducedMetric M).density e x =
        discAreaDensity (F (e.val x)) * ‖deriv F (e.val x)‖ ^ 2 := by
      change DiscCoverMetricConstruction.density M e x = _
      rw [DiscCoverMetricConstruction.density_eq_sheet M e l hl x (hsub hxs)]
      rfl
    rw [hdet, abs_of_nonneg (sq_nonneg _),
      ← ENNReal.ofReal_mul (sq_nonneg _), hd]
    congr 1
    exact mul_comm _ _
  have hJ := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hT hD hinj
    (fun z : ℂ => ENNReal.ofReal (discAreaDensity z))
  symm
  calc
    discHyperbolicArea ((fun x => discFiniteHomeomorph (l.symm x)) '' s) =
        ∫⁻ z in F '' T, ENNReal.ofReal (discAreaDensity z) ∂(volume : Measure ℂ) := by
      rw [discHyperbolicArea, him, discAreaMeasure, withDensity_apply _ hFT]
    _ = ∫⁻ z in T, ENNReal.ofReal |(D z).det| *
        ENNReal.ofReal (discAreaDensity (F z)) ∂(volume : Measure ℂ) := hJ
    _ = ∫⁻ z in T,
        ENNReal.ofReal ((discCoverAtlasInducedMetric M).density e (e.val.symm z))
          ∂(volume : Measure ℂ) := setLIntegral_congr_fun hT hweight
    _ = μ s := hmu.symm

/-- The selected native area of the existing disk-cover metric is exactly
the intrinsic hyperbolic area of that same original model. -/
theorem originalMetricArea_discCover_eq_intrinsic
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R
      (discCoverAtlasInducedMetric M).metric) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI : MeasurableSpace X := borel X
    letI : BorelSpace X := ⟨rfl⟩
    harea.exists.choose = M.areaMeasure := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let : SecondCountableTopology (MobiusDomainQuotient
      (unitDiscMobiusInvariantDomain M.group M.invariant)) :=
    discQuotient_secondCountable M.invariant
  let : SecondCountableTopology X := M.homeomorph.secondCountableTopology
  let μ : Measure X := harea.exists.choose
  have hall : μ.restrict Set.univ = M.areaMeasure.restrict Set.univ := by
    apply Auxiliary.Measure.measure_restrict_eq_of_locally_eq
    intro x _hx
    let e := chosenChart R.toRiemannSurface x
    let l := DiscCoverMetricConstruction.chosenSheet M x
    have hl : M.discCover = (l : extendedUnitDisc → X) :=
      DiscCoverMetricConstruction.chosenSheet_eq M x
    have hxE : x ∈ e.val.source := mem_chart_source ℂ x
    have hxL : x ∈ l.target := DiscCoverMetricConstruction.chosenSheet_mem M x
    obtain ⟨P, hxP⟩ := discQuotientAreaPatch_cover M.invariant M.discontinuous M.no_elliptic
      (M.homeomorph x)
    obtain ⟨U, hUo, hxU, hUW, hUc⟩ := R.toRiemannAtlas.exists_simplyConnected_open_subset x
      (e.val.source ∩ (l.target ∩ M.homeomorph ⁻¹' P.carrier))
      (e.val.open_source.inter (l.open_target.inter (P.isOpen.preimage M.homeomorph.continuous)))
      ⟨hxE, hxL, hxP⟩
    let : SimplyConnectedSpace U := hUc
    have hUE : ∀ y ∈ U, y ∈ e.val.source := fun _ hy => (hUW hy).1
    have hUL : ∀ y ∈ U, y ∈ l.target := fun _ hy => (hUW hy).2.1
    have hUP : ∀ y ∈ U, M.homeomorph y ∈ P.carrier := fun _ hy => (hUW hy).2.2
    let α : U → Complex.UnitDisc := M.patchLift P U hUP
    let β : U → Complex.UnitDisc := fun y => discFiniteHomeomorph (l.symm y.val)
    have hα : Continuous α := M.patchLift_continuous P U hUP
    have hβ : Continuous β := discFiniteHomeomorph.continuous.comp
      (l.continuousOn_symm.comp_continuous continuous_subtype_val (fun y => hUL y.val y.property))
    have hπ (y : U) : M.discCover (discFiniteHomeomorph.symm (α y)) =
        M.discCover (discFiniteHomeomorph.symm (β y)) := by
      rw [M.patchLift_projects P U hUP y]
      change y.val = M.discCover (discFiniteHomeomorph.symm
        (discFiniteHomeomorph (l.symm y.val)))
      rw [discFiniteHomeomorph.symm_apply_apply, hl, l.right_inv (hUL y.val y.property)]
    refine ⟨U, hUo, hxU, Set.subset_univ _, ?_⟩
    apply Measure.ext
    intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    have hS : MeasurableSet (α '' (Subtype.val ⁻¹' s)) :=
      (M.patchLift_isOpenEmbedding P U hUo hUP).measurableEmbedding.measurableSet_image.mpr
        (hs.preimage measurable_subtype_coe)
    have hcompare := analytic_discCovers_lifts_area_eq R.toRiemannAtlas
      M.discCover M.discCover M.discCover_covering M.discCover_covering
      M.discCover_analytic M.discCover_analytic α β hα hβ ⟨x, hxU⟩ hπ
      (Subtype.val ⁻¹' s) hS
    have him : (fun y => discFiniteHomeomorph (l.symm y)) '' (s ∩ U) =
        β '' (Subtype.val ⁻¹' s) := by
      ext z
      constructor
      · rintro ⟨y, ⟨hys, hyU⟩, rfl⟩
        exact ⟨⟨y, hyU⟩, hys, rfl⟩
      · rintro ⟨y, hys, rfl⟩
        exact ⟨y.val, ⟨hys, y.property⟩, rfl⟩
    calc
      μ (s ∩ U) = discHyperbolicArea
          ((fun y => discFiniteHomeomorph (l.symm y)) '' (s ∩ U)) :=
        selected_discCover_area_on_sheet R M harea x l hl (s ∩ U) (hs.inter hUo.measurableSet)
          (fun y hy => ⟨hUE y hy.2, hUL y hy.2⟩)
      _ = discHyperbolicArea (β '' (Subtype.val ⁻¹' s)) := congrArg discHyperbolicArea him
      _ = discHyperbolicArea (α '' (Subtype.val ⁻¹' s)) := hcompare
      _ = M.areaMeasure (s ∩ U) := (M.areaMeasure_apply_patchLift P U hUo hUP s hs).symm
  simpa only [Measure.restrict_univ] using hall

end LowDimensionalTopology.Geometry.Teichmuller
