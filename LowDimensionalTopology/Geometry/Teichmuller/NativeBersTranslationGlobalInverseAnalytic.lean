module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientPullbackHolomorphic
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersTranslationGlobalAnalytic

/-!
# The actual global inverse Bers translation is analytic everywhere

The inverse is the inverse of the already proved full-domain equivalence,
extended by zero only to state analyticity in the ambient weighted norm.
On every actual target coefficient point it is exactly the original Bers
projection of the actual normalized pullback. At every such point the
existing local coefficient section, the all-center pullback derivative,
and the original Bers derivative prove differentiability. The target image
is genuinely open and Osgood proves analyticity on the whole image.

This avoids any supplied nonvanishing-Jacobian theorem for an injective
holomorphic map. All maps retain their original coefficient classes,
weighted norms and exact normalized deformed group. The separate original
four-map identification for an arbitrary reference marking is not asserted.

Osgood's theorem is reused from Wu Xiaobin's Li-Zhong-QC-formalization,
commit `1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
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

/-- The actual whole-domain inverse, with zero extension outside its open domain. -/
def inverseBersTranslation (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (ψ : BersWeighted.Automorphic (deformedGroup hΓ ν)) : BersWeighted.Automorphic Γ := by
  classical
  exact if hψ : ψ ∈ coefficientBersImage (deformedGroup_spec hΓ ν).1 then
    ((coefficientBersTranslationEquiv hΓ ν).symm ⟨ψ, hψ⟩).val
  else 0

/-- At every original target coefficient, this is the literal normalized pullback Bers value. -/
theorem inverseBersTranslation_automorphicProjection
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) (κ : Ball (deformedGroup hΓ ν)) :
    inverseBersTranslation hΓ ν
        (BersWeighted.automorphicProjection (deformedGroup_spec hΓ ν).1 κ.val) =
      BersWeighted.automorphicProjection hΓ (gammaPullback hΓ ν κ.val) := by
  rw [inverseBersTranslation, dite_eq_left (show
    BersWeighted.automorphicProjection (deformedGroup_spec hΓ ν).1 κ.val ∈
      coefficientBersImage (deformedGroup_spec hΓ ν).1 from by
        exact (mem_coefficientBersImage_iff_coefficient _ _).mpr ⟨κ, rfl⟩)]
  simpa only [pulledBackBall_val] using
    coefficientBersTranslationEquiv_symm_coefficient hΓ ν κ

/-- The inverse is precisely the inverse of the full equivalence at every target image point. -/
theorem inverseBersTranslation_eq_equiv_symm
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (ψ : coefficientBersImage (deformedGroup_spec hΓ ν).1) :
    inverseBersTranslation hΓ ν ψ.val = ((coefficientBersTranslationEquiv hΓ ν).symm ψ).val := by
  unfold inverseBersTranslation
  exact dite_eq_left ψ.property

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)

include R hp hg hgenus in
/-- The actual inverse composite is differentiable at every deformed coefficient. -/
theorem differentiableAt_pullbackBersProjection_everyCoefficient
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) (κ : Ball (deformedGroup hΓ ν)) :
    DifferentiableAt ℂ
      (fun η : Space (deformedGroup hΓ ν) =>
        BersWeighted.automorphicProjection hΓ (gammaPullback hΓ ν η)) κ.val := by
  let μ : Ball Γ := ⟨gammaPullback hΓ ν κ.val, by
    rw [Metric.mem_ball, dist_zero_right]
    change ‖pullback ν κ.val.val‖ < 1
    exact norm_pullback_lt_one ν _⟩
  have hP := (hasFDerivAt_automorphicProjection_nonzero R hp hg hgenus hΓ μ).differentiableAt
  exact hP.comp κ.val (hasFDerivAt_gammaPullback_at hΓ ν κ).differentiableAt

include R hp hg hgenus in
/-- Every deformed coefficient has a genuine local section on which the
actual global inverse has the original coefficient-composition derivative. -/
theorem differentiableAt_inverseBersTranslation_inverseBersGerm_zero
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) (κ : Ball (deformedGroup hΓ ν)) :
    DifferentiableAt ℂ
      (fun q : BersWeighted.Automorphic (deformedGroup (deformedGroup_spec hΓ ν).1 κ) =>
        inverseBersTranslation hΓ ν (inverseBersGerm (deformedGroup_spec hΓ ν).1 κ q)) 0 := by
  let C : BersWeighted.Automorphic (deformedGroup (deformedGroup_spec hΓ ν).1 κ) →
      Space (deformedGroup hΓ ν) :=
    fun q => gammaPullback (deformedGroup_spec hΓ ν).1 κ (BersWeighted.ahlforsWeill q)
  have hC0 : C 0 = κ.val := by
    dsimp only [C]
    rw [map_zero, gammaPullback_zero]
  have hPB : DifferentiableAt ℂ (gammaPullback (deformedGroup_spec hΓ ν).1 κ)
      (BersWeighted.ahlforsWeill
        (0 : BersWeighted.Automorphic (deformedGroup (deformedGroup_spec hΓ ν).1 κ))) := by
    rw [map_zero]
    exact (hasFDerivAt_gammaPullback (deformedGroup_spec hΓ ν).1 κ).differentiableAt
  have hC : DifferentiableAt ℂ C 0 := hPB.comp 0
    (BersWeighted.ahlforsWeill
      (Γ := deformedGroup (deformedGroup_spec hΓ ν).1 κ)).differentiableAt
  have hT : DifferentiableAt ℂ
      (fun η : Space (deformedGroup hΓ ν) =>
        BersWeighted.automorphicProjection hΓ (gammaPullback hΓ ν η)) (C 0) := by
    rw [hC0]
    exact differentiableAt_pullbackBersProjection_everyCoefficient R hp hg hgenus hΓ ν κ
  have h := hT.comp 0 hC
  apply h.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro q
  let κq : Ball (deformedGroup hΓ ν) := ⟨C q, by
    rw [Metric.mem_ball, dist_zero_right]
    change ‖pullback κ (BersWeighted.ahlforsWeill q).val‖ < 1
    exact norm_pullback_lt_one κ _⟩
  exact inverseBersTranslation_automorphicProjection hΓ ν κq

include R hp hg hgenus in
/-- The global inverse is complex differentiable at every point of the whole target image. -/
theorem differentiableAt_inverseBersTranslation_everyCoefficient
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) (κ : Ball (deformedGroup hΓ ν)) :
    DifferentiableAt ℂ (inverseBersTranslation hΓ ν)
      (baseBersValue (deformedGroup_spec hΓ ν).1 κ) := by
  let Y := deformedNativeSurface R hgenus hΓ hp ν
  have hY : Y.HasGenus g := deformedNativeSurface_hasGenus R hgenus hΓ hp ν
  have hpY := deformedNativeSurface_uniformization R hgenus hΓ hp ν
  have hE := differentiableAt_inverseBersTranslation_inverseBersGerm_zero R hp hg hgenus hΓ ν κ
  have hE' : DifferentiableAt ℂ
      (fun q : BersWeighted.Automorphic (deformedGroup (deformedGroup_spec hΓ ν).1 κ) =>
        inverseBersTranslation hΓ ν (inverseBersGerm (deformedGroup_spec hΓ ν).1 κ q))
      (bersTranslation (deformedGroup_spec hΓ ν).1 κ
        (baseBersValue (deformedGroup_spec hΓ ν).1 κ)) := by
    rw [bersTranslation_base]
    exact hE
  have h := hE'.comp (baseBersValue (deformedGroup_spec hΓ ν).1 κ)
    (hasFDerivAt_bersTranslation Y hpY hg hY (deformedGroup_spec hΓ ν).1 κ).differentiableAt
  apply h.congr_of_eventuallyEq
  filter_upwards [inverseBersGerm_bersTranslation_eventually (deformedGroup_spec hΓ ν).1 κ]
    with ψ hψ
  change inverseBersTranslation hΓ ν ψ = inverseBersTranslation hΓ ν
    (inverseBersGerm (deformedGroup_spec hΓ ν).1 κ (bersTranslation (deformedGroup_spec hΓ ν).1 κ ψ))
  exact congrArg (inverseBersTranslation hΓ ν) hψ.symm

include R hp hg hgenus in
/-- Every point of the actual target domain is covered, with no small-section radius restriction. -/
theorem differentiableOn_inverseBersTranslation_coefficientBersImage
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    DifferentiableOn ℂ (inverseBersTranslation hΓ ν)
      (coefficientBersImage (deformedGroup_spec hΓ ν).1) := by
  intro ψ hψ
  obtain ⟨κ, rfl⟩ := (mem_coefficientBersImage_iff_coefficient _ ψ).mp hψ
  exact (differentiableAt_inverseBersTranslation_everyCoefficient R hp hg hgenus hΓ ν κ).differentiableWithinAt

include R hp hg hgenus in
/-- The actual global inverse is analytic on the entire original target Bers image. -/
theorem analyticOnNhd_inverseBersTranslation_coefficientBersImage
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    AnalyticOnNhd ℂ (inverseBersTranslation hΓ ν)
      (coefficientBersImage (deformedGroup_spec hΓ ν).1) := by
  classical
  let : ContinuousAdd (BersWeighted.Automorphic Γ) :=
    (Submodule.isTopologicalAddGroup (BersWeighted.automorphicSubmodule Γ)).toContinuousAdd
  let : CompleteSpace (BersWeighted.Automorphic Γ) := BersWeighted.automorphic_completeSpace Γ
  let Y := deformedNativeSurface R hgenus hΓ hp ν
  have hY : Y.HasGenus g := deformedNativeSurface_hasGenus R hgenus hΓ hp ν
  have hpY := deformedNativeSurface_uniformization R hgenus hΓ hp ν
  let e := deformedWeightedCoordinates R hg hgenus hΓ hp ν
  let U := e.symm ⁻¹' coefficientBersImage (deformedGroup_spec hΓ ν).1
  have hU : IsOpen U :=
    (isOpen_coefficientBersImage Y hpY hg hY (deformedGroup_spec hΓ ν).1).preimage e.symm.continuous
  have hd : DifferentiableOn ℂ (fun v => inverseBersTranslation hΓ ν (e.symm v)) U := by
    intro v hv
    have hpoint : DifferentiableAt ℂ (inverseBersTranslation hΓ ν) (e.symm v) := by
      change e.symm v ∈ coefficientBersImage (deformedGroup_spec hΓ ν).1 at hv
      obtain ⟨κ, hκ⟩ := (mem_coefficientBersImage_iff_coefficient _ (e.symm v)).mp hv
      rw [← hκ]
      exact differentiableAt_inverseBersTranslation_everyCoefficient R hp hg hgenus hΓ ν κ
    exact (hpoint.comp v e.symm.toContinuousLinearMap.differentiableAt).differentiableWithinAt
  have ha : AnalyticOnNhd ℂ (fun v => inverseBersTranslation hΓ ν (e.symm v)) U := by
    apply LiZhongQC.s34m_osgood hU hd.continuousOn
    intro v hv i
    have hpoint : DifferentiableAt ℂ
        (fun w => inverseBersTranslation hΓ ν (e.symm w)) (Function.update v i (v i)) := by
      rw [Function.update_eq_self]
      exact (hd v hv).differentiableAt (hU.mem_nhds hv)
    exact hpoint.comp (v i) (hasDerivAt_update v i (v i)).differentiableAt
  intro ψ hψ
  have hmem : e ψ ∈ U := by
    change e.symm (e ψ) ∈ coefficientBersImage (deformedGroup_spec hΓ ν).1
    rw [e.symm_apply_apply]
    exact hψ
  have h := (ha (e ψ) hmem).comp (e.toContinuousLinearMap.analyticAt ψ)
  apply h.congr
  exact Eventually.of_forall fun η => by
    simp only [Function.comp_apply, e.symm_apply_apply]

include R hp hg hgenus in
/-- Both genuine whole-domain coordinate maps are analytic in their original weighted norms.
The inverse is identified with the original full equivalence by
`inverseBersTranslation_eq_equiv_symm`. -/
theorem bersTranslation_analytic_bothDirections
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    AnalyticOnNhd ℂ (bersTranslation hΓ ν) (coefficientBersImage hΓ) ∧
      AnalyticOnNhd ℂ (inverseBersTranslation hΓ ν)
        (coefficientBersImage (deformedGroup_spec hΓ ν).1) := by
  exact ⟨analyticOnNhd_bersTranslation_coefficientBersImage R hp hg hgenus hΓ ν,
    analyticOnNhd_inverseBersTranslation_coefficientBersImage R hp hg hgenus hΓ ν⟩

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
