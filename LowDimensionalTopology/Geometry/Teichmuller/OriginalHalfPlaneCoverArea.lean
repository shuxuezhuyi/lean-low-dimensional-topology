module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalDiscCoverMetricArea
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.HalfPlaneUniformization
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.HalfPlaneMeasure
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S27_TeichmullerExistence

/-!
# Fundamental-region area for the original half-plane cover

The genuine hyperbolic area on a fundamental region pushes forward to the
intrinsic area of the same original surface. The comparison uses actual local
inverse sheets and the countable projective action of that same cover.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Manifold ContDiff UpperHalfPlane Pointwise

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Hyperbolic Fuchsian

variable {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)

private theorem halfPlane_region_measure_of_injective_image
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)
    (hp : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (P : HalfPlaneFuchsianGroup (Γ.map realSLMobius))
    {F A : Set ℍ} (hF : IsHalfPlaneFundamentalRegion P F)
    (hA : MeasurableSet A) (hinj : Set.InjOn p A) :
    (volume : Measure ℍ) (p ⁻¹' (p '' A) ∩ F) = volume A := by
  let := R.toRiemannAtlas.toChartedSpace
  let := P.nativeAction
  let H := Γ.map realSLMobius
  let : Countable H := Mobius.discreteMobius_countable _ P.discrete
  let : MeasurableConstSMul H ℍ :=
    ⟨fun a => (P.nativeHom a).continuous.measurable⟩
  let : SMulInvariantMeasure H ℍ volume := ⟨by
    intro a S hS
    exact (nativeIsometry_measurePreserving (P.nativeHom a)).measure_preimage
      hS.nullMeasurableSet⟩
  have hproject (a : H) (z : ℍ) : p (a • z) = p z := by
    obtain ⟨B, hBΓ, hBa⟩ := a.property
    rw [P.nativeAction_realSL a B hBa z]
    exact ((hp.2.2.2 z (B • z)).2 ⟨B, hBΓ, rfl⟩).symm
  have hfree (a : H) (z : ℍ) (hz : a • z = z) : a = 1 := by
    obtain ⟨B, hBΓ, hBa⟩ := a.property
    have hfix : B • z = z := (P.nativeAction_realSL a B hBa z).symm.trans hz
    apply Subtype.ext
    change a.val = 1
    rcases LiZhongQC.s27g_actsFreely hp B hBΓ z hfix with he | he
    · exact hBa.symm.trans (by rw [he, map_one])
    · exact hBa.symm.trans (by rw [he, realSLMobius_neg, map_one])
  have hpre : p ⁻¹' (p '' A) = ⋃ a : H, a • A := by
    ext z
    constructor
    · rintro ⟨w, hw, hwz⟩
      obtain ⟨B, hBΓ, hBz⟩ := (hp.2.2.2 w z).1 hwz
      let a : H := ⟨realSLMobius B, ⟨B, hBΓ, rfl⟩⟩
      refine Set.mem_iUnion.mpr ⟨a, w, hw, ?_⟩
      change a • w = z
      rw [P.nativeAction_realSL a B rfl w]
      exact hBz
    · intro hz
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hz
      rcases ha with ⟨w, hw, rfl⟩
      exact ⟨w, hw, (hproject a w).symm⟩
  have hdisjoint : Pairwise (fun a b : H => Disjoint (a • A) (b • A)) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    rintro z ⟨v, hv, hav⟩ ⟨w, hw, hbw⟩
    have hvw : v = w := hinj hv hw
      ((hproject a v).symm.trans
        ((congrArg p (hav.trans hbw.symm)).trans (hproject b w)))
    have hact : a • w = b • w := by simpa only [hvw] using hav.trans hbw.symm
    have hone : b⁻¹ * a = 1 := hfree (b⁻¹ * a) w (by
      rw [mul_smul, hact, inv_smul_smul])
    exact hab (inv_mul_eq_one.mp hone).symm
  have hpieces : Pairwise (fun a b : H => Disjoint (a • A ∩ F) (b • A ∩ F)) := by
    intro a b hab
    exact (hdisjoint hab).mono Set.inter_subset_left Set.inter_subset_left
  have hmeas (a : H) : MeasurableSet (a • A ∩ F) :=
    ((measurableEmbedding_const_smul a).measurableSet_image.mpr hA).inter hF.1.measurableSet
  calc
    (volume : Measure ℍ) (p ⁻¹' (p '' A) ∩ F) =
        volume (⋃ a : H, a • A ∩ F) := by rw [hpre, Set.iUnion_inter]
    _ = ∑' a : H, (volume : Measure ℍ) (a • A ∩ F) := measure_iUnion hpieces hmeas
    _ = volume A :=
      ((IsHalfPlaneFundamentalRegion.measureFundamentalDomain P hF).measure_eq_tsum A).symm

/-- Hyperbolic area in every genuine fundamental region of the same original
half-plane cover pushes forward to the intrinsic area on that surface. -/
theorem halfPlaneCover_fundamentalRegion_area_eq_intrinsic
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : letI := R.toRiemannAtlas.toChartedSpace;
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (P : HalfPlaneFuchsianGroup (Γ.map realSLMobius))
    {F : Set ℍ} (hF : IsHalfPlaneFundamentalRegion P F) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI : MeasurableSpace X := borel X
    letI : BorelSpace X := ⟨rfl⟩
    Measure.map M.halfPlaneCover ((volume : Measure ℍ).restrict F) = M.areaMeasure := by
  let := R.toRiemannAtlas.toChartedSpace
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let : SecondCountableTopology (MobiusDomainQuotient
      (unitDiscMobiusInvariantDomain M.group M.invariant)) :=
    discQuotient_secondCountable M.invariant
  let : SecondCountableTopology X := M.homeomorph.secondCountableTopology
  let μ : Measure X := Measure.map M.halfPlaneCover ((volume : Measure ℍ).restrict F)
  have hall : μ.restrict Set.univ = M.areaMeasure.restrict Set.univ := by
    apply Auxiliary.Measure.measure_restrict_eq_of_locally_eq
    intro x _hx
    obtain ⟨z, hzx⟩ := M.halfPlaneCover_surjective x
    obtain ⟨l, hzl, hl⟩ := M.halfPlaneCover_covering.isLocalHomeomorph z
    have hxl : x ∈ l.target := by
      rw [← hzx, hl]
      exact l.map_source hzl
    obtain ⟨W, hxW⟩ := discQuotientAreaPatch_cover M.invariant M.discontinuous M.no_elliptic
      (M.homeomorph x)
    obtain ⟨U, hUo, hxU, hUW, hUc⟩ := R.toRiemannAtlas.exists_simplyConnected_open_subset x
      (l.target ∩ M.homeomorph ⁻¹' W.carrier)
      (l.open_target.inter (W.isOpen.preimage M.homeomorph.continuous)) ⟨hxl, hxW⟩
    let : SimplyConnectedSpace U := hUc
    have hUL : ∀ y ∈ U, y ∈ l.target := fun _ hy => (hUW hy).1
    have hUP : ∀ y ∈ U, M.homeomorph y ∈ W.carrier := fun _ hy => (hUW hy).2
    let σ : U → ℍ := fun y => l.symm y.val
    have hσ : Continuous σ :=
      l.continuousOn_symm.comp_continuous continuous_subtype_val
        (fun y => hUL y.val y.property)
    have hσp (y : U) : M.halfPlaneCover (σ y) = y.val := by
      change M.halfPlaneCover (l.symm y.val) = y.val
      rw [hl, l.right_inv (hUL y.val y.property)]
    have hσe : Topology.IsOpenEmbedding σ := by
      apply M.halfPlaneCover_covering.isLocalHomeomorph.isOpenEmbedding_of_comp ?_ hσ
      have he : M.halfPlaneCover ∘ σ = (Subtype.val : U → X) := funext hσp
      rw [he]
      exact hUo.isOpenEmbedding_subtypeVal
    let α : U → Complex.UnitDisc := M.patchLift W U hUP
    let β : U → Complex.UnitDisc := fun y => halfPlaneToDisc (σ y)
    have hα : Continuous α := M.patchLift_continuous W U hUP
    have hβ : Continuous β := cayleyHomeomorph.continuous.comp hσ
    have hπ (y : U) : M.discCover (discFiniteHomeomorph.symm (α y)) =
        M.discCover (discFiniteHomeomorph.symm (β y)) := by
      rw [M.patchLift_projects W U hUP y]
      change y.val = M.halfPlaneCover (σ y)
      exact (hσp y).symm
    refine ⟨U, hUo, hxU, Set.subset_univ _, ?_⟩
    apply Measure.ext
    intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    let A : Set ℍ := σ '' (Subtype.val ⁻¹' s)
    have hA : MeasurableSet A :=
      hσe.measurableEmbedding.measurableSet_image.mpr (hs.preimage measurable_subtype_coe)
    have hinj : Set.InjOn M.halfPlaneCover A := by
      rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ h
      have hvw : v = w := Subtype.ext ((hσp v).symm.trans (h.trans (hσp w)))
      exact congrArg σ hvw
    have hAs : M.halfPlaneCover '' A = s ∩ U := by
      ext y
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        rw [hσp v]
        exact ⟨hv, v.property⟩
      · rintro ⟨hys, hyU⟩
        exact ⟨σ ⟨y, hyU⟩, ⟨⟨y, hyU⟩, hys, rfl⟩, hσp ⟨y, hyU⟩⟩
    have hαS : MeasurableSet (α '' (Subtype.val ⁻¹' s)) :=
      (M.patchLift_isOpenEmbedding W U hUo hUP).measurableEmbedding.measurableSet_image.mpr
        (hs.preimage measurable_subtype_coe)
    have hβS : MeasurableSet (β '' (Subtype.val ⁻¹' s)) := by
      have he : β '' (Subtype.val ⁻¹' s) = cayleyHomeomorph '' A := by
        change β '' (Subtype.val ⁻¹' s) =
          cayleyHomeomorph '' (σ '' (Subtype.val ⁻¹' s))
        rw [Set.image_image]
        rfl
      rw [he]
      exact cayleyHomeomorph.measurableEmbedding.measurableSet_image.mpr hA
    have hCayley : discHyperbolicArea (β '' (Subtype.val ⁻¹' s)) =
        (volume : Measure ℍ) A := by
      rw [discHyperbolicArea_eq_halfPlane_volume _ hβS]
      congr 1
      ext y
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨v, hv, (discToHalfPlane_halfPlaneToDisc (σ v)).symm⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨β v, ⟨v, hv, rfl⟩, discToHalfPlane_halfPlaneToDisc (σ v)⟩
    have hcompare := analytic_discCovers_lifts_area_eq R.toRiemannAtlas
      M.discCover M.discCover M.discCover_covering M.discCover_covering
      M.discCover_analytic M.discCover_analytic α β hα hβ ⟨x, hxU⟩ hπ
      (Subtype.val ⁻¹' s) hαS
    calc
      μ (s ∩ U) = (volume : Measure ℍ) (M.halfPlaneCover ⁻¹' (M.halfPlaneCover '' A) ∩ F) := by
        change Measure.map M.halfPlaneCover ((volume : Measure ℍ).restrict F) (s ∩ U) = _
        rw [Measure.map_apply M.halfPlaneCover_covering.continuous.measurable
          (hs.inter hUo.measurableSet),
          Measure.restrict_apply (M.halfPlaneCover_covering.continuous.measurable
            (hs.inter hUo.measurableSet)), hAs]
      _ = (volume : Measure ℍ) A :=
        halfPlane_region_measure_of_injective_image R M.halfPlaneCover hp P hF hA hinj
      _ = discHyperbolicArea (β '' (Subtype.val ⁻¹' s)) := hCayley.symm
      _ = discHyperbolicArea (α '' (Subtype.val ⁻¹' s)) := hcompare
      _ = M.areaMeasure (s ∩ U) := (M.areaMeasure_apply_patchLift W U hUo hUP s hs).symm
  simpa only [Measure.restrict_univ] using hall

/-- For the existing disk-cover metric, the same genuine region pushes forward
both to its intrinsic area and to its prescribed native metric area. -/
theorem halfPlaneCover_fundamentalRegion_area_eq_selected
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R
      (discCoverAtlasInducedMetric M).metric)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : letI := R.toRiemannAtlas.toChartedSpace;
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (P : HalfPlaneFuchsianGroup (Γ.map realSLMobius))
    {F : Set ℍ} (hF : IsHalfPlaneFundamentalRegion P F) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI : MeasurableSpace X := borel X
    letI : BorelSpace X := ⟨rfl⟩
    Measure.map M.halfPlaneCover ((volume : Measure ℍ).restrict F) = M.areaMeasure ∧
    Measure.map M.halfPlaneCover ((volume : Measure ℍ).restrict F) = harea.exists.choose := by
  let := R.toRiemannAtlas.toChartedSpace
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  have hi := halfPlaneCover_fundamentalRegion_area_eq_intrinsic R M hp P hF
  exact ⟨hi, hi.trans (originalMetricArea_discCover_eq_intrinsic R M harea).symm⟩

end LowDimensionalTopology.Geometry.Teichmuller
