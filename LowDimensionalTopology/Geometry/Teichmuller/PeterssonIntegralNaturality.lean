module
public import LowDimensionalTopology.Unproved.Teichmuller.SamePointPeterssonIntegralNaturality
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.HalfPlaneMeasure
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticPointwisePairing
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate
namespace LowDimensionalTopology.Geometry.Teichmuller
open GammaMeasurableBeltrami
/-- Equality of the actual actions identifies the projective images, allowing central signs. -/
theorem realSL_image_eq_of_actions {Γ Γ' : Subgroup Deck}
    (h : ∀ A ∈ Γ, ∃ B ∈ Γ', ∀ z : ℍ, A • z = B • z)
    (h' : ∀ B ∈ Γ', ∃ A ∈ Γ, ∀ z : ℍ, B • z = A • z) :
    Γ.map Hyperbolic.realSLMobius = Γ'.map Hyperbolic.realSLMobius := by
  have hincl {Δ Δ' : Subgroup Deck}
      (ha : ∀ A ∈ Δ, ∃ B ∈ Δ', ∀ z : ℍ, A • z = B • z) :
      Δ.map Hyperbolic.realSLMobius ≤ Δ'.map Hyperbolic.realSLMobius := by
    rintro _ ⟨A, hA, rfl⟩
    obtain ⟨B, hB, hact⟩ := ha A hA
    refine ⟨B, hB, ?_⟩
    rcases LiZhongQC.b33_d_eq_or_eq_neg hact with he | he
    · rw [he]
    · rw [he, Hyperbolic.realSLMobius_neg]
  exact le_antisymm (hincl h) (hincl h')

/-- Changing only the proofs of half-plane preservation and discreteness changes no region. -/
theorem halfPlaneRegion_of_same_group
    {H : Subgroup Mobius.complexMobiusGroup} (P P' : Fuchsian.HalfPlaneFuchsianGroup H)
    {F : Set ℍ} (hF : Fuchsian.IsHalfPlaneFundamentalRegion P' F) :
    Fuchsian.IsHalfPlaneFundamentalRegion P F := by
  have hP : P' = P := by
    cases P
    cases P'
    rfl
  exact hP ▸ hF

/-- Equality of the actual projective subgroup preserves the original region predicate. -/
theorem halfPlaneRegion_of_group_eq {H H' : Subgroup Mobius.complexMobiusGroup}
    (h : H = H') (P : Fuchsian.HalfPlaneFuchsianGroup H)
    (P' : Fuchsian.HalfPlaneFuchsianGroup H') {F : Set ℍ}
    (hF : Fuchsian.IsHalfPlaneFundamentalRegion P' F) :
    Fuchsian.IsHalfPlaneFundamentalRegion P F := by
  cases h
  exact halfPlaneRegion_of_same_group P P' hF

open Surfaces WeilPetersson NormalizedCoefficientTransport
universe u

/-- The literal harmonic Beltrami integral is independent of the genuine fundamental region. -/
theorem harmonicBeltramiPairing_eq_of_regions
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {F F' : Set ℍ} (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (hF' : Fuchsian.IsHalfPlaneFundamentalRegion P F')
    (η ξ : NativePetersson.Harmonic R P p hp F hF) :
    beltramiPairing F η.val.val ξ.val.val = beltramiPairing F' η.val.val ξ.val.val := by
  obtain ⟨q, hq⟩ :=
    (NativePetersson.mem_harmonicSubmodule_iff_exists_quadratic R P p hp F hF η.val).mp η.property
  obtain ⟨r, hr⟩ :=
    (NativePetersson.mem_harmonicSubmodule_iff_exists_quadratic R P p hp F hF ξ.val).mp ξ.property
  have hη : η.val.val =ᵐ[(volume : Measure ℍ)] NativeHarmonicBeltrami.coefficient R p q := by
    simpa only [hq] using NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp q
  have hξ : ξ.val.val =ᵐ[(volume : Measure ℍ)] NativeHarmonicBeltrami.coefficient R p r := by
    simpa only [hr] using NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp r
  let f : ℍ → ℂ := quadraticPointwiseLift R p r q
  have he (S : Set ℍ) (hS : MeasurableSet S) :
      beltramiPairing S η.val.val ξ.val.val = ∫ z in S, f z ∂(volume : Measure ℍ) := by
    rw [beltramiPairing_eq_hyperbolicIntegral S hS]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hη, ae_restrict_of_ae hξ] with z hηz hξz
    rw [hηz, hξz]
    exact (mul_comm _ _).trans (quadraticPointwiseLift_eq_coefficients R p r q z).symm
  let := P.nativeAction
  let : Countable (Γ.map Hyperbolic.realSLMobius) :=
    Mobius.discreteMobius_countable _ P.discrete
  let : MeasurableConstSMul (Γ.map Hyperbolic.realSLMobius) ℍ :=
    ⟨fun a => (P.nativeHom a).continuous.measurable⟩
  let : SMulInvariantMeasure (Γ.map Hyperbolic.realSLMobius) ℍ volume := ⟨by
    intro a S hS
    exact (Hyperbolic.nativeIsometry_measurePreserving (P.nativeHom a)).measure_preimage
      hS.nullMeasurableSet⟩
  have hi : ∀ (a : Γ.map Hyperbolic.realSLMobius) (z : ℍ), f (a • z) = f z := by
    intro a z
    obtain ⟨A, hA, hAa⟩ := a.property
    rw [P.nativeAction_realSL a A hAa z]
    exact quadraticPointwiseLift_invariant R p hp r q A hA z
  have hI :=
    (Fuchsian.IsHalfPlaneFundamentalRegion.measureFundamentalDomain P hF).setIntegral_eq
      (Fuchsian.IsHalfPlaneFundamentalRegion.measureFundamentalDomain P hF') hi
  exact (he F hF.1.measurableSet).trans (hI.trans (he F' hF'.1.measurableSet).symm)

/-- Same-point harmonic identification preserves every literal Petersson integral. -/
theorem samePointPeterssonIntegralNaturality
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ) :
    LowDimensionalTopology.Unproved.Teichmuller.SamePointPeterssonIntegralNaturality R hp hg hgenus hΓ hfree := by
  intro ν ν' hpoint P F hF P' F' hF' η ξ
  simp only [nativePointDeformedHarmonicEquiv_val, nativePointDeformedCoefficientEquiv_val]
  have hs := sourcePoint_eq_of_sameNativePoint R hp hg hgenus hΓ hfree ν ν' hpoint
  have hproj := realSL_image_eq_of_actions
    (deformedGroup_actions_of_samePoint hΓ (native_fixedPoints_dense R hp) ν ν' hs)
    (deformedGroup_actions_of_samePoint hΓ (native_fixedPoints_dense R hp) ν' ν hs.symm)
  have hF'' : Fuchsian.IsHalfPlaneFundamentalRegion P F' :=
    halfPlaneRegion_of_group_eq hproj P P' hF'
  exact harmonicBeltramiPairing_eq_of_regions
    (deformedNativeSurface R hgenus hΓ hp ν) P
    (deformedTargetCover R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) hF hF'' η ξ
end LowDimensionalTopology.Geometry.Teichmuller
