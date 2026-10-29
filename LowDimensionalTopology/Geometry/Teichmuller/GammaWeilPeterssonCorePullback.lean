module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaWeilPeterssonCore
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonLocalCoefficients

/-! The original selected group and native WP values agree under the actual inverse differential. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport NativePetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "D" => canonicalGammaDiffeomorph R hp hg hgenus hΓ hfree hsmooth
local notation "HN" => nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth
local notation "HG" => gammaWeilPeterssonCore R hp hg hgenus hΓ hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree

/-- On every original group tangent pair, the independently selected full integral
families agree by the actual inverse complex manifold differential. Core slots
are exchanged here to retain the source's first-linear convention. -/
theorem gammaWeilPeterssonCore_inner_eq_nativeCore (a : LiZhongQC.TeichGamma Γ) :
    letI := C
    letI := mΓ
    letI := CG
    ∀ v w : TangentSpace TI a,
      (HG a).inner w v =
        (HN ((D).symm a)).inner
          (mfderiv TI TI (D).symm a w) (mfderiv TI TI (D).symm a v) := by
  let := C
  let := mΓ
  let := CG
  obtain ⟨b, rfl⟩ := (D).toEquiv.surjective a
  obtain ⟨ν, hν⟩ := coefficientProjectionBall_surjective R hg hgenus hΓ hfree hp b
  have hβ : β ν.val = b :=
    (coefficientProjection_ball R hg hgenus hΓ hfree hp ν).trans hν
  rw [← hβ]
  intro v w
  obtain ⟨P, F, hF⟩ := exists_deformedHalfPlaneFundamentalRegion R hgenus hΓ hp ν
  let L := (D).symm.mfderivToContinuousLinearEquiv (by decide) (D (β ν.val))
  let J := canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth
    ((D).symm_apply_apply (β ν.val))
  have hcast {x y : TeichmullerSpace.{0,0} R} (h : x = y)
      (u z : TangentSpace TI x) :
      (HN x).inner u z =
        (HN y).inner
          (canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth h u)
          (canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth h z) := by
    subst y
    rfl
  have hgroup := gammaWeilPeterssonCore_integral R hp hg hgenus hΓ hsmooth
    ν P F hF v w
  have hnative := nativeWeilPeterssonCore_integral R hp hg hgenus hΓ hfree hsmooth
    ν P F hF (J (L v)) (J (L w))
  have hL (u : TangentSpace TI (D (β ν.val))) :
      L u = mfderiv TI TI (D).symm (D (β ν.val)) u :=
    congrArg
      (fun A : TangentSpace TI (D (β ν.val)) →L[ℂ]
        TangentSpace TI ((D).symm (D (β ν.val))) => A u)
      ((D).symm.mfderivToContinuousLinearEquiv_coe (by decide))
  calc
    (HG (D (β ν.val))).inner w v =
        WeilPetersson.beltramiPairing F
          (TH ν P F hF hsmooth (J (L v))).val.val
          (TH ν P F hF hsmooth (J (L w))).val.val := hgroup
    _ = (HN (β ν.val)).inner (J (L w)) (J (L v)) := hnative.symm
    _ = (HN ((D).symm (D (β ν.val)))).inner (L w) (L v) :=
      (hcast ((D).symm_apply_apply (β ν.val)) (L w) (L v)).symm
    _ = (HN ((D).symm (D (β ν.val)))).inner
        (mfderiv TI TI (D).symm (D (β ν.val)) w)
        (mfderiv TI TI (D).symm (D (β ν.val)) v) :=
      congrArg₂ ((HN ((D).symm (D (β ν.val)))).inner) (hL w) (hL v)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
