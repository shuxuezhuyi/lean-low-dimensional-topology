module

public import LowDimensionalTopology.Unproved.Teichmuller.DeformedReferenceHarmonicNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonRealForm
public import LowDimensionalTopology.Geometry.Teichmuller.BeltramiHermitianRealMobius

/-!
# The original WP tensor under the actual local reference change

The independent input concerns actual harmonic coefficients and covers only.
The unchanged full-region integral specifications and actual Mobius change
of variables then give the original selected WP family's local tensor law.
No smoothness input at the deformed references is used here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "TI" => 𝓘(ℂ, Fin (3*g-3) → ℂ)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "H" => nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree

private theorem nativeReferenceCore_pointEq :
    letI := C
    ∀ {a b : TeichmullerSpace.{0,0} R} (_h : a = b) (v w : TangentSpace TI a),
      (H b).inner (tangentSpaceCast TI a b w) (tangentSpaceCast TI a b v) =
        (H a).inner w v := by
  let := C
  intro a b h v w
  subst b
  rfl

variable (ν : Ball Γ)

local notation "Y" => deformedNativeSurface R hgenus hΓ hp ν
local notation "hY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "Δ" => deformedGroup hΓ ν
local notation "hΔ" => And.left (deformedGroup_spec hΓ ν)
local notation "hfY" => deformedNativeSurface_actsFreely R hgenus hΓ hp ν
local notation "CY" => canonicalComplexChartedSpace Y hg hY hP hΔ hfY hpY hsmooth
local notation "βY" => coefficientProjection Y hg hY hP hΔ hfY hpY
local notation "HY" => nativeWeilPeterssonCore Y hpY hg hY hΔ hfY hsmooth
local notation "A" => deformedReferenceChangeEquiv R hp hg hgenus hΓ ν

/-- Near each actual original centre, the differential of the genuine
reference change preserves the unchanged selected integral WP tensor. -/
theorem nativeWeilPeterssonCore_deformedReference_local_pullback
    (hnat : Unproved.Teichmuller.DeformedReferenceHarmonicNaturality
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C
    letI := CY
    ∃ V : Set (TeichmullerSpace.{0,0} R), IsOpen V ∧ β ν.val ∈ V ∧
      ∀ (a : TeichmullerSpace.{0,0} R), a ∈ V → ∀ (v w : TangentSpace TI a),
        (HY (A a)).inner (mfderiv TI TI A a w) (mfderiv TI TI A a v) =
          (H a).inner w v := by
  let := C
  let := CY
  obtain ⟨V, hVo, hν, hV⟩ := hnat ν
  refine ⟨V, hVo, hν, ?_⟩
  intro a ha
  obtain ⟨μ, hμ⟩ := coefficientProjectionBall_surjective R hg hgenus hΓ hfree hp a
  have hμa : β μ.val = a :=
    (coefficientProjection_ball R hg hgenus hΓ hfree hp μ).trans hμ
  rw [← hμa] at ha ⊢
  intro v w
  obtain ⟨P, F, hF⟩ := exists_deformedHalfPlaneFundamentalRegion R hgenus hΓ hp μ
  obtain ⟨M, hpoint, P', hF', c, hc, hcover, ht⟩ := hV μ ha P F hF
  let κ := translatedBall hΓ ν μ
  let J := tangentSpaceCast TI (A (β μ.val)) (βY κ.val)
  calc
    (HY (A (β μ.val))).inner
        (mfderiv TI TI A (β μ.val) w) (mfderiv TI TI A (β μ.val) v) =
        (HY (βY κ.val)).inner
          (J (mfderiv TI TI A (β μ.val) w))
          (J (mfderiv TI TI A (β μ.val) v)) :=
      (nativeReferenceCore_pointEq Y hpY hg hY hΔ hfY hsmooth hpoint _ _).symm
    _ = WeilPetersson.beltramiPairing ((fun z : ℍ => M • z) ⁻¹' F)
        (pullback M (TH μ P F hF hsmooth v).val.val)
        (pullback M (TH μ P F hF hsmooth w).val.val) := by
      rw [nativeWeilPeterssonCore_integral Y hpY hg hY hΔ hfY hsmooth κ P' _ hF', ht v, ht w]
    _ = WeilPetersson.beltramiPairing F
        (TH μ P F hF hsmooth v).val.val (TH μ P F hF hsmooth w).val.val :=
      WeilPetersson.beltramiPairing_realMobiusPullback M F hF.1.measurableSet _ _
    _ = (H (β μ.val)).inner w v :=
      (nativeWeilPeterssonCore_integral R hp hg hgenus hΓ hfree hsmooth μ P F hF v w).symm

/-- The same actual local tensor law gives the English-normalized fundamental
form pullback by the real restriction of the genuine complex differential. -/
theorem nativeWeilPeterssonFundamentalForm_deformedReference_local_pullback
    (hnat : Unproved.Teichmuller.DeformedReferenceHarmonicNaturality
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C
    letI := CY
    ∃ V : Set (TeichmullerSpace.{0,0} R), IsOpen V ∧ β ν.val ∈ V ∧
      ∀ (a : TeichmullerSpace.{0,0} R), a ∈ V →
        (nativeWeilPeterssonFundamentalForm Y hpY hg hY hΔ hfY hsmooth (A a)).compContinuousLinearMap
            ((mfderiv TI TI A a).restrictScalars ℝ) =
          nativeWeilPeterssonFundamentalForm R hp hg hgenus hΓ hfree hsmooth a := by
  let := C
  let := CY
  obtain ⟨V, hVo, hν, hV⟩ := nativeWeilPeterssonCore_deformedReference_local_pullback
    R hp hg hgenus hΓ hfree hsmooth ν hnat
  refine ⟨V, hVo, hν, ?_⟩
  intro a ha
  apply ContinuousAlternatingMap.ext
  intro v
  change -2 * ((HY (A a)).inner
      (mfderiv TI TI A a (v 1)) (mfderiv TI TI A a (v 0))).im =
    -2 * ((H a).inner (v 1) (v 0)).im
  exact congrArg (fun z : ℂ => -2 * z.im) (hV a ha (v 0) (v 1))

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
