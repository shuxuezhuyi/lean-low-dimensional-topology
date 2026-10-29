module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientTranslationHolomorphic
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersTranslationGlobalImage
public import LowDimensionalTopology.Geometry.Teichmuller.NativeNonzeroBersDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersProjectionTopology
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedNativeTarget
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.S34mOsgood
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Fixed normalized Bers translation on its entire original Bers domain

At every original coefficient, the genuine local inverse section gives an
actual coefficient lift. Composing its actual normalized pullback with the
fixed normalized translation and the deformed Bers projection proves
complex differentiability at every Bers image point. The domain is the
whole original coefficient image. Its openness follows from the existing
original Bers coordinates and the full coefficient projection, and Osgood
then gives several-variable analyticity in the original weighted norm.

Only the actual symmetric normalized upper-half-plane maps enter these
coefficient translations. No nonsymmetric zero-extension solution is
identified with them. This file proves the forward fixed-base map; it does
not assert the still separate global inverse analyticity or the four
original maps for an arbitrary supplied change of reference surface.

The source Bers dependence and Osgood arguments are due to Wu Xiaobin's
Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Surfaces

variable {Γ : Subgroup Deck}

/-- The actual inverse coefficient section has the original base value. -/
theorem gammaPullback_zero (hΓ : LiZhongQC.IsFuchsian Γ) (μ : Ball Γ) :
    gammaPullback hΓ μ 0 = μ.val := by
  apply Subtype.ext
  exact pullback_base μ

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)

include R hp hg hgenus in
/-- The fixed translated Bers composite is differentiable at every original coefficient. -/
theorem differentiableAt_translatedBersProjection_everyCoefficient
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) :
    DifferentiableAt ℂ (translatedBersProjection hΓ ν) μ.val := by
  let Y := deformedNativeSurface R hgenus hΓ hp ν
  have hY : Y.HasGenus g := deformedNativeSurface_hasGenus R hgenus hΓ hp ν
  have hpY := deformedNativeSurface_uniformization R hgenus hΓ hp ν
  have hP := (hasFDerivAt_automorphicProjection_nonzero Y hpY hg hY
    (deformedGroup_spec hΓ ν).1 (translatedBall hΓ ν μ)).differentiableAt
  change DifferentiableAt ℂ
    (BersWeighted.automorphicProjection (deformedGroup_spec hΓ ν).1 ∘
      gammaTranslation hΓ ν) μ.val
  exact hP.comp μ.val (hasFDerivAt_gammaTranslation_at hΓ ν μ).differentiableAt

include R hp hg hgenus in
/-- At every original coefficient, the genuine local inverse section makes
fixed-base translation a differentiable map at the section origin. -/
theorem differentiableAt_bersTranslation_inverseBersGerm_zero
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) :
    DifferentiableAt ℂ
      (fun q : BersWeighted.Automorphic (deformedGroup hΓ μ) =>
        bersTranslation hΓ ν (inverseBersGerm hΓ μ q)) 0 := by
  let C : BersWeighted.Automorphic (deformedGroup hΓ μ) → Space Γ :=
    fun q => gammaPullback hΓ μ (BersWeighted.ahlforsWeill q)
  have hC0 : C 0 = μ.val := by
    dsimp only [C]
    rw [map_zero, gammaPullback_zero]
  have hPB : DifferentiableAt ℂ (gammaPullback hΓ μ)
      (BersWeighted.ahlforsWeill (0 : BersWeighted.Automorphic (deformedGroup hΓ μ))) := by
    rw [map_zero]
    exact (hasFDerivAt_gammaPullback hΓ μ).differentiableAt
  have hC : DifferentiableAt ℂ C 0 :=
    hPB.comp 0 (BersWeighted.ahlforsWeill (Γ := deformedGroup hΓ μ)).differentiableAt
  have hT : DifferentiableAt ℂ (translatedBersProjection hΓ ν) (C 0) := by
    rw [hC0]
    exact differentiableAt_translatedBersProjection_everyCoefficient R hp hg hgenus hΓ ν μ
  have h := hT.comp 0 hC
  apply h.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro q
  let μq : Ball Γ := ⟨C q, by
    rw [Metric.mem_ball, dist_zero_right]
    change ‖pullback μ (BersWeighted.ahlforsWeill q).val‖ < 1
    exact norm_pullback_lt_one μ _⟩
  exact bersTranslation_automorphicProjection hΓ ν μq

include R hp hg hgenus in
/-- Fixed-base translation is complex differentiable at every actual source Bers point. -/
theorem differentiableAt_bersTranslation_everyCoefficient
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) :
    DifferentiableAt ℂ (bersTranslation hΓ ν) (baseBersValue hΓ μ) := by
  have hE := differentiableAt_bersTranslation_inverseBersGerm_zero R hp hg hgenus hΓ ν μ
  have hE' : DifferentiableAt ℂ
      (fun q : BersWeighted.Automorphic (deformedGroup hΓ μ) =>
        bersTranslation hΓ ν (inverseBersGerm hΓ μ q))
      (bersTranslation hΓ μ (baseBersValue hΓ μ)) := by
    rw [bersTranslation_base]
    exact hE
  have h := hE'.comp (baseBersValue hΓ μ)
    (hasFDerivAt_bersTranslation R hp hg hgenus hΓ μ).differentiableAt
  apply h.congr_of_eventuallyEq
  filter_upwards [inverseBersGerm_bersTranslation_eventually hΓ μ] with φ hφ
  change bersTranslation hΓ ν φ =
    bersTranslation hΓ ν (inverseBersGerm hΓ μ (bersTranslation hΓ μ φ))
  exact congrArg (bersTranslation hΓ ν) hφ.symm

include R hp hg hgenus in
/-- The full actual coefficient Bers image is open in its faithful original norm. -/
theorem isOpen_coefficientBersImage (hΓ : LiZhongQC.IsFuchsian Γ) :
    IsOpen (coefficientBersImage hΓ) := by
  have hfree : LiZhongQC.ActsFreely Γ := by
    let := R.toRiemannAtlas.toChartedSpace
    exact LiZhongQC.s27g_actsFreely hp
  let W := TeichmullerSpace.weightedLinearBersCoordinates R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hp
  let BC := TeichmullerSpace.bersCoordinates R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp
  have he : coefficientBersImage hΓ = W ⁻¹' range BC := by
    ext φ
    rw [mem_coefficientBersImage_iff_coefficient]
    change φ ∈ Set.range (fun μ : Ball Γ => BersWeighted.automorphicProjection hΓ μ.val) ↔
      W φ ∈ Set.range BC
    constructor
    · rintro ⟨μ, rfl⟩
      refine ⟨TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp μ, ?_⟩
      exact TeichmullerSpace.coefficientProjectionBall_coordinates R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp μ
    · rintro ⟨a, ha⟩
      obtain ⟨μ, hμ⟩ := TeichmullerSpace.coefficientProjectionBall_surjective R hg hgenus hΓ hfree hp a
      refine ⟨μ, W.injective ?_⟩
      have hc := TeichmullerSpace.coefficientProjectionBall_coordinates R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp μ
      rw [hμ] at hc
      exact hc.symm.trans ha
  rw [he]
  exact (TeichmullerSpace.isOpen_range_bersCoordinates R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp).preimage W.continuous

include R hp hg hgenus in
/-- The fixed normalized Bers translation is holomorphic on the whole original domain. -/
theorem differentiableOn_bersTranslation_coefficientBersImage
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    DifferentiableOn ℂ (bersTranslation hΓ ν) (coefficientBersImage hΓ) := by
  intro φ hφ
  obtain ⟨μ, rfl⟩ := (mem_coefficientBersImage_iff_coefficient hΓ φ).mp hφ
  exact (differentiableAt_bersTranslation_everyCoefficient R hp hg hgenus hΓ ν μ).differentiableWithinAt

include R hp hg hgenus in
/-- All image points, rather than only the fixed base, have genuine
several-variable analytic neighborhoods in the original weighted norm. -/
theorem analyticOnNhd_bersTranslation_coefficientBersImage
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    AnalyticOnNhd ℂ (bersTranslation hΓ ν) (coefficientBersImage hΓ) := by
  classical
  let : ContinuousAdd (BersWeighted.Automorphic (deformedGroup hΓ ν)) :=
    (Submodule.isTopologicalAddGroup
      (BersWeighted.automorphicSubmodule (deformedGroup hΓ ν))).toContinuousAdd
  let : CompleteSpace (BersWeighted.Automorphic (deformedGroup hΓ ν)) :=
    BersWeighted.automorphic_completeSpace (deformedGroup hΓ ν)
  let e := TeichmullerSpace.weightedLinearBersCoordinates R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hp
  let U := e.symm ⁻¹' coefficientBersImage hΓ
  have hU : IsOpen U := (isOpen_coefficientBersImage R hp hg hgenus hΓ).preimage e.symm.continuous
  have hd : DifferentiableOn ℂ (fun v => bersTranslation hΓ ν (e.symm v)) U := by
    intro v hv
    have hpoint : DifferentiableAt ℂ (bersTranslation hΓ ν) (e.symm v) := by
      change e.symm v ∈ coefficientBersImage hΓ at hv
      obtain ⟨μ, hμ⟩ := (mem_coefficientBersImage_iff_coefficient hΓ (e.symm v)).mp hv
      rw [← hμ]
      exact differentiableAt_bersTranslation_everyCoefficient R hp hg hgenus hΓ ν μ
    exact (hpoint.comp v e.symm.toContinuousLinearMap.differentiableAt).differentiableWithinAt
  have ha : AnalyticOnNhd ℂ (fun v => bersTranslation hΓ ν (e.symm v)) U := by
    apply LiZhongQC.s34m_osgood hU hd.continuousOn
    intro v hv i
    have hpoint : DifferentiableAt ℂ
        (fun w => bersTranslation hΓ ν (e.symm w)) (Function.update v i (v i)) := by
      rw [Function.update_eq_self]
      exact (hd v hv).differentiableAt (hU.mem_nhds hv)
    exact hpoint.comp (v i) (hasDerivAt_update v i (v i)).differentiableAt
  intro φ hφ
  have hmem : e φ ∈ U := by
    change e.symm (e φ) ∈ coefficientBersImage hΓ
    rw [e.symm_apply_apply]
    exact hφ
  have h := (ha (e φ) hmem).comp (e.toContinuousLinearMap.analyticAt φ)
  apply h.congr
  exact Eventually.of_forall fun ψ => by
    simp only [Function.comp_apply, e.symm_apply_apply]

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
