module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonLocalCoefficients
public import LowDimensionalTopology.Geometry.Teichmuller.BasePointHarmonicTangent
public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientRealMobiusNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceHarmonicAmbient
public import LowDimensionalTopology.Geometry.Teichmuller.PeterssonIntegralNaturality

/-!
# The selected original Weil–Petersson form at the identity marking

At the actual zero coefficient, the normalized map is the identity and the
literal derivative transport preserves every ambient coefficient class.
The existing harmonic projection formula identifies the deformed and original
harmonic representatives without identifying their surface carriers.
The selected native form therefore has the original full-region integral.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ENNReal UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport NativePetersson

private theorem ambientDerivative_zeroCoefficient {Γ : Subgroup Deck} (μ : Ambient) :
    ambientDerivative (zeroCoefficient Γ) μ = μ := by
  have hu (z : ℍ) : normalizedUpperEquiv (zeroCoefficient Γ) z = z := by
    apply UpperHalfPlane.ext
    change normalizedMap (zeroCoefficient Γ) (z : ℂ) = (z : ℂ)
    rw [normalizedMap_zeroCoefficient]
    rfl
  have hi (z : ℍ) : (normalizedUpperEquiv (zeroCoefficient Γ)).symm z = z := by
    apply (normalizedUpperEquiv (zeroCoefficient Γ)).injective
    rw [Equiv.apply_symm_apply, hu]
  have hd (z : ℍ) : LiZhongQC.dz (normalizedMap (zeroCoefficient Γ)) z = 1 := by
    rw [normalizedMap_zeroCoefficient]
    simp only [LiZhongQC.dz, fderiv_id, ContinuousLinearMap.id_apply]
    rw [Complex.I_mul_I]
    norm_num
  have hp (z : ℍ) : derivativePhase (zeroCoefficient Γ) z = 1 := by
    simp only [derivativePhase, hd, map_one, div_one]
  apply Lp.ext
  filter_upwards [ambientDerivative_weighted_coe_ae (zeroCoefficient Γ) μ,
    Lp.coeFn_zero ℂ (⊤ : ℝ≥0∞) (volume : Measure ℍ)] with z hz hzero
  rw [hz, hi, derivativeWeight, hp, coefficientDenominator]
  change (1 : ℂ) / (1 - conj ((0 : Ambient) z) * (0 : Ambient) z) * μ z = μ z
  rw [hzero, Pi.zero_apply, map_zero, zero_mul, sub_zero, div_one, one_mul]

private theorem deformedGroup_zeroCoefficient_projective
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) :
    (deformedGroup hΓ (zeroCoefficient Γ)).map Hyperbolic.realSLMobius =
      Γ.map Hyperbolic.realSLMobius := by
  apply realSL_image_eq_of_actions
  · intro B hB
    obtain ⟨A, hA, hrel⟩ := (deformedGroup_spec hΓ (zeroCoefficient Γ)).2.2 B hB
    refine ⟨A, hA, fun z => ?_⟩
    apply UpperHalfPlane.ext
    have h := hrel (z : ℂ) z.im_pos
    simpa only [normalizedMap_zeroCoefficient, id_eq, LiZhongQC.b33_d_mobiusFn_smul]
      using h.symm
  · intro A hA
    obtain ⟨B, hB, hrel⟩ := (deformedGroup_spec hΓ (zeroCoefficient Γ)).2.1 A hA
    refine ⟨B, hB, fun z => ?_⟩
    apply UpperHalfPlane.ext
    have h := hrel (z : ℂ) z.im_pos
    simpa only [normalizedMap_zeroCoefficient, id_eq, LiZhongQC.b33_d_mobiusFn_smul]
      using h

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

local notation "ν₀" => zeroCoefficient Γ
local notation "R₀" => deformedNativeSurface R hgenus hΓ hp ν₀
local notation "p₀" => deformedTargetCover R hgenus hΓ hp ν₀
local notation "hp₀" => deformedNativeSurface_uniformization R hgenus hΓ hp ν₀
local notation "TI" => 𝓘(ℂ, Fin (3*g-3) → ℂ)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "β" => baseCoefficientProjection R hg hgenus hΓ hfree hp
local notation "BH" => baseTangentHarmonicEquiv R hg hgenus hΓ hfree hp hsmooth P F hF

private theorem harmonicProjection_zeroCoefficient_ambient
    (P₀ : Fuchsian.HalfPlaneFuchsianGroup
      ((deformedGroup hΓ ν₀).map Hyperbolic.realSLMobius))
    (hF₀ : Fuchsian.IsHalfPlaneFundamentalRegion P₀ F) (μ : GammaMeasurableBeltrami.Space Γ) :
    (harmonicProjection R₀ P₀ p₀ hp₀ F hF₀ (gammaDerivative hΓ ν₀ μ)).val =
      (harmonicProjection R P p hp F hF μ).val := by
  rw [harmonicProjection_eq_ahlforsWeill_integral R₀ P₀ p₀ hp₀ F hF₀
    (deformedGroup_spec hΓ ν₀).1,
    harmonicProjection_eq_ahlforsWeill_integral R P p hp F hF hΓ]
  apply ahlforsWeill_ambient_of_val_eq
  simp only [BersWeighted.automorphicIntegralOperator_val]
  apply lp.ext
  funext z
  rw [BersWeighted.integralOperator_apply, BersWeighted.integralOperator_apply,
    gammaDerivative_val, ambientDerivative_zeroCoefficient]

/-- The selected original native WP form is the literal first-linear pairing
of its original harmonic tangent representatives in every genuine region. -/
theorem nativeWeilPeterssonCore_basePoint_integral :
    letI := C
    ∀ v w : TangentSpace TI (basePoint R),
      (nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth (basePoint R)).inner w v =
        WeilPetersson.beltramiPairing F (BH v).val.val (BH w).val.val := by
  let := C
  have hgroup := deformedGroup_zeroCoefficient_projective hΓ
  let P₀ : Fuchsian.HalfPlaneFuchsianGroup
      ((deformedGroup hΓ ν₀).map Hyperbolic.realSLMobius) := by
    rw [hgroup]
    exact P
  have hF₀ : Fuchsian.IsHalfPlaneFundamentalRegion P₀ F :=
    halfPlaneRegion_of_group_eq hgroup P₀ P hF
  have hd (v : TangentSpace TI (basePoint R)) :
      mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) TI β 0 (BH v).val = v := by
    apply (BH).injective
    rw [baseTangentHarmonicEquiv_derivative]
    apply Subtype.ext
    exact (mem_harmonicSubmodule_iff R P p hp F hF (BH v).val).mp (BH v).property
  have hh (v : TangentSpace TI (basePoint R)) :
      (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν₀ P₀ F hF₀ hsmooth v).val.val =
        (BH v).val.val := by
    have h := congrArg (fun η : Harmonic R₀ P₀ p₀ hp₀ F hF₀ => η.val.val)
      (nonzeroTangentHarmonicEquiv_derivative R hp hg hgenus hΓ hfree ν₀
        P₀ F hF₀ hsmooth (BH v).val)
    change
      (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν₀ P₀ F hF₀ hsmooth
        (mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) TI β 0 (BH v).val)).val.val =
      (harmonicProjection R₀ P₀ p₀ hp₀ F hF₀ (gammaDerivative hΓ ν₀ (BH v).val)).val at h
    rw [hd] at h
    exact h.trans ((harmonicProjection_zeroCoefficient_ambient R hp hgenus hΓ P F hF
      P₀ hF₀ (BH v).val).trans
        (congrArg Subtype.val ((mem_harmonicSubmodule_iff R P p hp F hF (BH v).val).mp
          (BH v).property)))
  intro v w
  have hi :
      (nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth (basePoint R)).inner w v =
        WeilPetersson.beltramiPairing F
          (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν₀ P₀ F hF₀ hsmooth v).val.val
          (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν₀ P₀ F hF₀ hsmooth w).val.val := by
    have hzero : β ((ν₀).val) = basePoint R := by
      change β 0 = basePoint R
      exact baseCoefficientProjection_zero R hg hgenus hΓ hfree hp
    have hpoint := congrArg (fun a : TeichmullerSpace.{0, 0} R =>
      (nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth a).inner w v) hzero
    exact hpoint.symm.trans
      (nativeWeilPeterssonCore_integral R hp hg hgenus hΓ hfree hsmooth ν₀ P₀ F hF₀ v w)
  exact hi.trans (congrArg₂
    (fun μ ν : Ambient => WeilPetersson.beltramiPairing F μ ν) (hh v) (hh w))

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
