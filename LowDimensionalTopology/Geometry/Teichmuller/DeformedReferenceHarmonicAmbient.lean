module

public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceChangeDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.BersTranslationCocycleDerivative

/-!
# The actual reference differential preserves the literal ambient harmonic class

The derivative cocycle is compared in the unchanged weighted target. The
actual harmonic inverses then give the same original L-infinity class, for
every original coefficient and every genuine choice of the two regions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

/-- Equal weighted Bers values give the same literal section class in the ambient space. -/
theorem ahlforsWeill_ambient_of_val_eq {Γ₁ Γ₂ : Subgroup Deck}
    (φ : BersWeighted.Automorphic Γ₁) (ψ : BersWeighted.Automorphic Γ₂)
    (h : φ.val = ψ.val) :
    (BersWeighted.ahlforsWeill φ).val = (BersWeighted.ahlforsWeill ψ).val := by
  apply Lp.ext
  filter_upwards [BersWeighted.ahlforsWeill_coe_ae φ,
    BersWeighted.ahlforsWeill_coe_ae ψ] with z hz hz'
  rw [hz, hz', BersWeighted.ahlforsWeillCoefficient,
    BersWeighted.ahlforsWeillCoefficient, BersWeighted.Automorphic.toSource_apply,
    BersWeighted.Automorphic.toSource_apply, h]

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0}) (ν μ : Ball Γ)

local notation "hP" => canonicalHandleGroupPresentation g
local notation "TI" => 𝓘(ℂ, Fin (3*g-3) → ℂ)
local notation "Y" => deformedNativeSurface R hgenus hΓ hp ν
local notation "hY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "Δ" => deformedGroup hΓ ν
local notation "hΔ" => And.left (deformedGroup_spec hΓ ν)
local notation "hfY" => deformedNativeSurface_actsFreely R hgenus hΓ hp ν
local notation "κ" => translatedBall hΓ ν μ
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "βY" => coefficientProjection Y hg hY hP hΔ hfY hpY
local notation "Aν" => deformedReferenceChangeEquiv R hp hg hgenus hΓ ν

/-- At every original coefficient the actual reference differential has the
same ambient harmonic class. Only the genuine equality of its target point
is used; no chosen target surfaces or matrix-lift groups are identified. -/
theorem deformedReferenceChangeEquiv_harmonic_ambient
    (P : Fuchsian.HalfPlaneFuchsianGroup
      ((deformedGroup hΓ μ).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (P' : Fuchsian.HalfPlaneFuchsianGroup
      ((deformedGroup hΔ κ).map Hyperbolic.realSLMobius))
    (F' : Set ℍ) (hF' : Fuchsian.IsHalfPlaneFundamentalRegion P' F') :
    letI := canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
    letI := canonicalComplexChartedSpace Y hg hY hP hΔ hfY hpY hsmooth
    ∀ v : TangentSpace TI (β μ.val),
      (nonzeroTangentHarmonicEquiv Y hpY hg hY hΔ hfY κ P' F' hF' hsmooth
        (tangentSpaceCast TI (Aν (β μ.val)) (βY (κ).val)
          (mfderiv TI TI Aν (β μ.val) v))).val.val =
        (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree μ P F hF hsmooth v).val.val := by
  let := canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
  let := canonicalComplexChartedSpace Y hg hY hP hΔ hfY hpY hsmooth
  intro v
  let u := mfderiv TI TI Aν (β μ.val) v
  let w := tangentSpaceCast TI (Aν (β μ.val)) (βY (κ).val) u
  let f := canonicalBersTangentEquiv R hg hgenus hP hΓ hfree hp hsmooth (β μ.val)
  let fY := canonicalBersTangentEquiv Y hg hY hP hΔ hfY hpY hsmooth (βY (κ).val)
  let φ := (inverseBersDerivativeEquiv R hp hg hgenus hΓ μ).symm (f v)
  let ψ := (inverseBersDerivativeEquiv Y hpY hg hY hΔ κ).symm (fY w)
  have hpoint : Aν (β μ.val) = βY (κ).val := by
    rw [coefficientProjection_ball R hg hgenus hΓ hfree hp μ,
      coefficientProjection_ball Y hg hY hΔ hfY hpY κ]
    exact deformedReferenceChangeEquiv_coefficientProjection R hp hg hgenus hΓ hfree ν μ
  have hbase :
      (weightedLinearBersCoordinates R hg hgenus hP hΓ hp).symm
        (bersCoordinates R hg hgenus hP hΓ hfree hp (β μ.val)) = baseBersValue hΓ μ := by
    rw [coefficientProjection_ball, coefficientProjectionBall_coordinates,
      ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hframe : fY w = fderiv ℂ (bersTranslation hΓ ν) (baseBersValue hΓ μ) (f v) := by
    have ht := canonicalBersTangentEquiv_pointEq Y hpY hg hY hΔ hfY hsmooth hpoint u
    rw [canonicalTangentEquivOfPointEq_eq_tangentSpaceCast] at ht
    have hd := deformedReferenceChangeEquiv_mfderiv_bersCoordinates
      R hp hg hgenus hΓ hfree ν hsmooth (β μ.val) v
    rw [hbase] at hd
    exact ht.trans hd
  have hψφ : ψ.val = φ.val := by
    have hc := congrArg
      (fun L : BersWeighted.Automorphic Γ →L[ℂ] BersWeighted.Target => L (f v))
      (bersTranslation_recentring_fderiv R hp hg hgenus hΓ ν μ)
    change ((inverseBersDerivativeEquiv Y hpY hg hY hΔ κ).symm
      (fderiv ℂ (bersTranslation hΓ ν) (baseBersValue hΓ μ) (f v))).val = φ.val at hc
    exact (congrArg (fun b : BersWeighted.Automorphic Δ =>
      ((inverseBersDerivativeEquiv Y hpY hg hY hΔ κ).symm b).val) hframe).trans hc
  have hR :
      (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree μ P F hF hsmooth v).val =
        BersWeighted.ahlforsWeill φ :=
    (congrArg Subtype.val (nonzeroTangentHarmonicEquiv_apply
      R hp hg hgenus hΓ hfree hsmooth μ P F hF v)).trans
        (NativePetersson.harmonicDerivativeEquiv_symm_val_eq_ahlforsWeill
          (deformedNativeSurface R hgenus hΓ hp μ) P
          (deformedTargetCover R hgenus hΓ hp μ)
          (deformedNativeSurface_uniformization R hgenus hΓ hp μ)
          F hF (And.left (deformedGroup_spec hΓ μ)) φ)
  have hY' :
      (nonzeroTangentHarmonicEquiv Y hpY hg hY hΔ hfY κ P' F' hF' hsmooth w).val =
        BersWeighted.ahlforsWeill ψ :=
    (congrArg Subtype.val (nonzeroTangentHarmonicEquiv_apply
      Y hpY hg hY hΔ hfY hsmooth κ P' F' hF' w)).trans
        (NativePetersson.harmonicDerivativeEquiv_symm_val_eq_ahlforsWeill
          (deformedNativeSurface Y hY hΔ hpY κ) P'
          (deformedTargetCover Y hY hΔ hpY κ)
          (deformedNativeSurface_uniformization Y hY hΔ hpY κ)
          F' hF' (And.left (deformedGroup_spec hΔ κ)) ψ)
  exact (congrArg Subtype.val hY').trans
    ((ahlforsWeill_ambient_of_val_eq ψ φ hψφ).trans (congrArg Subtype.val hR).symm)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
