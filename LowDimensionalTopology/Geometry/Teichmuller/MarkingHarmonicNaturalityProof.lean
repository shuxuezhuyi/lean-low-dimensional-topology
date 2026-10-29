module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaMarkingBersDerivative
public import LowDimensionalTopology.Unproved.Teichmuller.MarkingPrecompositionHarmonicNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.SourceFuchsianRegions

/-! Actual target witnesses and the original marking harmonic naturality obligation. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff
namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami BersWeighted NormalizedCoefficientTransport

private theorem region_realMobius_preimage {Δ Δ' : Subgroup Deck} (M : Deck)
    (P : Fuchsian.HalfPlaneFuchsianGroup (Δ.map Hyperbolic.realSLMobius))
    (P' : Fuchsian.HalfPlaneFuchsianGroup (Δ'.map Hyperbolic.realSLMobius))
    (hproj : (LiZhongQC.conjGroup Δ' M).map Hyperbolic.realSLMobius =
      Δ.map Hyperbolic.realSLMobius) (F : Set ℍ)
    (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    Fuchsian.IsHalfPlaneFundamentalRegion P' ((fun z : ℍ => M • z) ⁻¹' F) := by
  let H := Δ.map Hyperbolic.realSLMobius
  let H' := Δ'.map Hyperbolic.realSLMobius
  let Q := Hyperbolic.realSLMobius M
  let := P.nativeAction
  let := P'.nativeAction
  let k : H' → H := fun g => ⟨Q * g.val * Q⁻¹, by
    change Hyperbolic.realSLMobius M * g.val * (Hyperbolic.realSLMobius M)⁻¹ ∈
      Δ.map Hyperbolic.realSLMobius
    rw [← hproj]
    obtain ⟨A, hA, hAg⟩ := Subgroup.mem_map.mp g.property
    refine Subgroup.mem_map.mpr ⟨M * A * M⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨A, hA, rfl⟩
    · simp only [map_mul, map_inv, hAg]⟩
  have hk_ne (g : H') (hg : g ≠ 1) : k g ≠ 1 := by
    intro he
    apply hg
    apply Subtype.ext
    have hv := congrArg Subtype.val he
    change Q * g.val * Q⁻¹ = 1 at hv
    calc
      g.val = Q⁻¹ * (Q * g.val * Q⁻¹) * Q := by simp [mul_assoc]
      _ = 1 := by rw [hv]; simp
  have hkact (g : H') (z : ℍ) : M • (g • z) = k g • (M • z) := by
    obtain ⟨A, hA, hAg⟩ := Subgroup.mem_map.mp g.property
    have hB : Hyperbolic.realSLMobius (M * A * M⁻¹) = (k g).val := by
      change Hyperbolic.realSLMobius (M * A * M⁻¹) =
        Hyperbolic.realSLMobius M * g.val * (Hyperbolic.realSLMobius M)⁻¹
      simp only [map_mul, map_inv, hAg]
    rw [P'.nativeAction_realSL g A hAg, P.nativeAction_realSL (k g) _ hB]
    simp only [mul_smul, inv_smul_smul]
  have hksurj : Function.Surjective k := by
    intro h
    have hh : h.val ∈ (LiZhongQC.conjGroup Δ' M).map Hyperbolic.realSLMobius :=
      hproj.symm ▸ h.property
    obtain ⟨B, hB, hBh⟩ := Subgroup.mem_map.mp hh
    obtain ⟨A, hA, hAB⟩ := Subgroup.mem_map.mp hB
    have hb : B = M * A * M⁻¹ := hAB.symm
    refine ⟨⟨Hyperbolic.realSLMobius A, Subgroup.mem_map.mpr ⟨A, hA, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change Q * Hyperbolic.realSLMobius A * Q⁻¹ = h.val
    simpa only [hb, map_mul, map_inv] using hBh
  let s : ℍ ≃ₜ ℍ := Homeomorph.smul M
  refine ⟨hF.1.preimage s.continuous, ?_, ?_, ?_⟩
  · intro g hg
    apply Set.disjoint_left.mpr
    rintro _ ⟨y, hy, rfl⟩ hx
    exact Set.disjoint_left.mp (hF.2.1 (k g) (hk_ne g hg))
      ⟨M • y, hy, (hkact g y).symm⟩ hx
  · intro x
    obtain ⟨h, y, hy, he⟩ := hF.2.2.1 (M • x)
    obtain ⟨g, hg⟩ := hksurj h
    refine ⟨g, M⁻¹ • y, ?_, ?_⟩
    · change M⁻¹ • y ∈ closure (s ⁻¹' F)
      rw [← s.preimage_closure F]
      change M • (M⁻¹ • y) ∈ closure F
      simpa only [smul_inv_smul] using hy
    · apply s.injective
      change M • (g • (M⁻¹ • y)) = M • x
      rw [hkact, hg, smul_inv_smul]
      exact he
  · have hn : (volume : Measure ℍ) (frontier F) = 0 :=
      (Hyperbolic.halfPlane_volume_eq_zero_iff_planar_volume_eq_zero _).mpr hF.2.2.2
    have hpre := (measurePreserving_deck M).quasiMeasurePreserving.preimage_null hn
    apply (Hyperbolic.halfPlane_volume_eq_zero_iff_planar_volume_eq_zero _).mp
    change (volume : Measure ℍ) (frontier (s ⁻¹' F)) = 0
    rw [← s.preimage_frontier F]
    exact hpre

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : LiZhongQC.IsFuchsian Γ)
local notation "Y" => deformedNativeSurface R hgenus hΓ hp
local notation "q" => deformedTargetCover R hgenus hΓ hp
local notation "eν" => deformedTargetMarking R hgenus hΓ hp

private def markingTargetHomeomorph (e : X ≃ₜ X) (ν ν' : Ball Γ) :
    (deformedTargetSource R hgenus hΓ hp ν').carrier ≃ₜ
      (deformedTargetSource R hgenus hΓ hp ν).carrier :=
  ((eν ν').symm.trans e.symm).trans (eν ν)

private theorem markingTarget_cover (e : X ≃ₜ X) (w : ℍ ≃ₜ ℍ)
    (hw : LiZhongQC.IsLift p p e w) (ν ν' : Ball Γ) (α : Deck)
    (hα : ∀ z : ℍ, normalizedUpperEquiv ν' z = α • normalizedUpperEquiv ν (w.symm z))
    (z : ℍ) : markingTargetHomeomorph R hp hgenus hΓ e ν ν' (q ν' z) = q ν (α⁻¹ • z) := by
  have hpre : w.symm ((normalizedUpperEquiv ν').symm z) =
      (normalizedUpperEquiv ν).symm (α⁻¹ • z) := by
    apply (normalizedUpperEquiv ν).injective
    rw [Equiv.apply_symm_apply]
    have he := congrArg (fun t : ℍ => α⁻¹ • t) (hα ((normalizedUpperEquiv ν').symm z))
    simpa only [Equiv.apply_symm_apply, inv_smul_smul] using he.symm
  have hi (t : ℍ) : e.symm (p t) = p (w.symm t) := by
    have he := congrArg e.symm (hw (w.symm t))
    simpa only [w.apply_symm_apply, e.symm_apply_apply] using he
  change (eν ν) (e.symm ((eν ν').symm ((eν ν')
    (p ((normalizedUpperEquiv ν').symm z))))) =
      (eν ν) (p ((normalizedUpperEquiv ν).symm (α⁻¹ • z)))
  rw [Homeomorph.symm_apply_apply, hi, hpre]

private theorem markingTarget_analytic (e : X ≃ₜ X) (w : ℍ ≃ₜ ℍ)
    (hw : LiZhongQC.IsLift p p e w) (ν ν' : Ball Γ) (α : Deck)
    (hα : ∀ z : ℍ, normalizedUpperEquiv ν' z = α • normalizedUpperEquiv ν (w.symm z)) :
    RiemannAnalyticMap (Y ν').toRiemannAtlas (Y ν).toRiemannAtlas
      (markingTargetHomeomorph R hp hgenus hΓ e ν ν') := by
  let := (Y ν').toRiemannAtlas.toChartedSpace
  let := (Y ν).toRiemannAtlas.toChartedSpace
  let := (Y ν').toRiemannAtlas.isManifold
  let := (Y ν).toRiemannAtlas.isManifold
  let M := α⁻¹
  let c := markingTargetHomeomorph R hp hgenus hΓ e ν ν'
  have hLift : LiZhongQC.IsLift (q ν') (q ν) c (Homeomorph.smul M) := by
    intro z
    exact (markingTarget_cover R hp hgenus hΓ e w hw ν ν' α hα z).symm
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe M
  have hM : LiZhongQC.IsKQC (LiZhongQC.liftToC (Homeomorph.smul M)) LiZhongQC.upperHalf 1 := by
    apply LiZhongQC.ad_isKQC_congr (LiZhongQC.isKQC_one_of_conformal LiZhongQC.isOpen_upperHalf
      (LiZhongQC.isConformalOnto_mobius_upperHalf (by rw [hdet]; exact zero_lt_one)))
    intro z hz
    rw [LiZhongQC.h23l_liftToC_eq _ hz]
    change ((M • UpperHalfPlane.ofComplex z : ℍ) : ℂ) =
      LiZhongQC.mobiusFn (M 0 0) (M 0 1) (M 1 0) (M 1 1) z
    simp only [LiZhongQC.h23l_b_coe_smul,
      UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz), LiZhongQC.mobiusFn]
  have hBi := (LiZhongQC.isKQCRS_one_iff c).mp
    (LiZhongQC.s27v_isKQCRS_of_lift
      (deformedNativeSurface_uniformization R hgenus hΓ hp ν')
      (deformedNativeSurface_uniformization R hgenus hΓ hp ν) hLift hM)
  have hA := (analyticHomeomorph_ofManifold_iff_sourceBiholomorphic c).mpr hBi
  simpa only [RiemannAtlas.ofManifold_toChartedSpace] using hA

include R hp hgenus in
private theorem markingTarget_projectiveImage (e : X ≃ₜ X) (w : ℍ ≃ₜ ℍ)
    (hw : LiZhongQC.IsLift p p e w) (ν ν' : Ball Γ) (α : Deck)
    (hα : ∀ z : ℍ, normalizedUpperEquiv ν' z = α • normalizedUpperEquiv ν (w.symm z)) :
    (LiZhongQC.conjGroup (deformedGroup hΓ ν') α⁻¹).map Hyperbolic.realSLMobius =
      (deformedGroup hΓ ν).map Hyperbolic.realSLMobius := by
  let := (Y ν').toRiemannAtlas.toChartedSpace
  let := (Y ν).toRiemannAtlas.toChartedSpace
  let := (Y ν').toRiemannAtlas.isManifold
  let := (Y ν).toRiemannAtlas.isManifold
  let M := α⁻¹
  let c := markingTargetHomeomorph R hp hgenus hΓ e ν ν'
  have hLift : LiZhongQC.IsLift (q ν') (q ν) c (Homeomorph.smul M) := by
    intro z
    exact (markingTarget_cover R hp hgenus hΓ e w hw ν ν' α hα z).symm
  have hp' := deformedNativeSurface_uniformization R hgenus hΓ hp ν'
  have hp₀ := deformedNativeSurface_uniformization R hgenus hΓ hp ν
  apply realSL_image_eq_of_actions
  · intro B hB
    obtain ⟨A, hA, hAB⟩ := Subgroup.mem_map.mp hB
    obtain ⟨C, hC, hc⟩ := LiZhongQC.h23l_deck hp' hp₀ hLift hA
    refine ⟨C, hC, fun z => ?_⟩
    obtain ⟨t, rfl⟩ := (Homeomorph.smul M).surjective z
    have hb : B = M * A * M⁻¹ := hAB.symm
    rw [hb]
    change (M * A * M⁻¹) • (M • t) = C • (M • t)
    simp only [mul_smul, inv_smul_smul]
    exact hc t
  · intro C hC
    obtain ⟨A, hA, hc⟩ := LiZhongQC.h23l_deck hp₀ hp'
      (LiZhongQC.s27g_isLift_symm hLift) hC
    refine ⟨M * A * M⁻¹, Subgroup.mem_map.mpr ⟨A, hA, rfl⟩, fun z => ?_⟩
    have he := congrArg (fun t : ℍ => M • t) (hc z)
    change M • (M⁻¹ • (C • z)) = M • (A • (M⁻¹ • z)) at he
    simpa only [mul_smul, smul_inv_smul] using he

variable (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
local notation "TI" => 𝓘(ℂ, Fin (3*g-3) → ℂ)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "D" => canonicalGammaDiffeomorph R hp hg hgenus hΓ hfree hsmooth
local notation "T" => gammaWeilPeterssonTangentHarmonicEquiv R hp hg hgenus hΓ hsmooth
local notation "W" => weightedLinearBersCoordinates R hg hgenus hP hΓ hp
local notation "GC" => gammaBersCoordinates R hg hgenus hΓ hfree hp
local notation "coord" => gammaWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ

/-- The original full marking harmonic naturality obligation follows with
only the already explicit original QC smoothing hypothesis. -/
theorem markingPrecompositionHarmonicNaturality_of_smoothing :
    LowDimensionalTopology.Unproved.Teichmuller.MarkingPrecompositionHarmonicNaturality
      R hp hg hgenus hΓ hsmooth := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := C; let := mΓ; let := CG
  intro f ν P F hF
  obtain ⟨w, rfl⟩ := QCNormalizerModular.descentHom_surjective hp f
  let f := QCNormalizerModular.descendedAut hp w.val w.property
  let hw := QCNormalizerModular.descendedAut_isLift hp w.val w.property
  let A := referenceGammaEquiv R R hg hgenus hgenus f.val f.property hΓ hΓ hp hp
  obtain ⟨ρ, N₀, hN₀, hrec⟩ :=
    exists_upperMarkingBersDerivativeAndHarmonicLaw R hp hg hgenus hΓ w
  let G := givenReferenceBersMap hp hp hΓ f.val w.val hw ρ N₀ hN₀
  let ν' := givenReferenceChangedBall hp hp hΓ f.val w.val hw ρ N₀ hN₀ ν
  obtain ⟨α, hα, _, _, haw⟩ := hrec ν
  let M := α⁻¹
  let c := markingTargetHomeomorph R hp hgenus hΓ f.val ν ν'
  let P' := sourceHalfPlaneFuchsianGroup (And.left (deformedGroup_spec hΓ ν'))
  have hF' : Fuchsian.IsHalfPlaneFundamentalRegion P' ((fun z : ℍ => M • z) ⁻¹' F) :=
    region_realMobius_preimage M P P'
      (markingTarget_projectiveImage R hp hgenus hΓ f.val w.val hw ν ν' α hα) F hF
  have hpoint : A (D (β ν.val)) = D (β ν'.val) := by
    rw [canonicalGammaDiffeomorph_projection, canonicalGammaDiffeomorph_projection]
    exact referenceGammaEquiv_coefficientProjection R R hg hgenus hgenus f.val f.property
      hΓ hΓ hp hp w.val hw ρ N₀ hN₀ ν
  refine ⟨ν', M, hpoint, P', hF', c,
    markingTarget_analytic R hp hgenus hΓ f.val w.val hw ν ν' α hα,
    markingTarget_cover R hp hgenus hΓ f.val w.val hw ν ν' α hα, ?_⟩
  intro v
  let a := D (β ν.val)
  let a' := D (β ν'.val)
  let u := mfderiv TI TI A a v
  let u' := tangentSpaceCast TI (A a) a' u
  have hbase : (W).symm (GC a) = baseBersValue hΓ ν := by
    change (W).symm (GC (D (β ν.val))) = baseBersValue hΓ ν
    rw [canonicalGammaDiffeomorph_projection]
    change (W).symm (bersCoordinates R hg hgenus hP hΓ hfree hp
      (coefficientProjectionBall R hg hgenus hP hΓ hfree hp ν)) = _
    rw [coefficientProjectionBall_coordinates, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hframe : (W).symm (coord a' u') =
      fderiv ℂ G (baseBersValue hΓ ν) ((W).symm (coord a v)) := by
    have he := gammaWeilPeterssonCoordinateEquiv_pointEq R hp hg hgenus hΓ hpoint u
    have hd := referenceGammaEquiv_mfderiv_weighted R hp hg hgenus hΓ
      f w.val hw ρ N₀ hN₀ a v
    rw [hbase] at hd
    exact (congrArg (fun z => (W).symm z) he).trans hd
  change (T ν' P' ((fun z : ℍ => M • z) ⁻¹' F) hF' u').val.val =
    pullback M (T ν P F hF v).val.val
  rw [gammaWeilPeterssonTangentHarmonicEquiv_val_eq_ahlforsWeill R hp hg hgenus hΓ hsmooth ν'
      P' _ hF' u',
    gammaWeilPeterssonTangentHarmonicEquiv_val_eq_ahlforsWeill R hp hg hgenus hΓ hsmooth ν P F hF v,
    hframe]
  exact haw ((W).symm (coord a v))

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
