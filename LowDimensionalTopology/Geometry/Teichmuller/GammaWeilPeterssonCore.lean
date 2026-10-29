module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonMetric

/-!
# The original group Weil–Petersson family and its actual harmonic representatives

This selects the existing complete integral family on the original `T(Gamma)`.
The harmonic identification uses the actual inverse differential of the
unchanged normalized-lift biholomorphism. No new tangent norm is installed.
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
    (hΓ : LiZhongQC.IsFuchsian Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

include R hp in
/-- The deck action of the given original closed-surface uniformization is free. -/
theorem closedUniformization_deckActsFreely : LiZhongQC.ActsFreely Γ := by
  let := R.toRiemannAtlas.toChartedSpace
  exact LiZhongQC.s27g_actsFreely hp

local notation "TI" => 𝓘(ℂ, Fin (3*g-3) → ℂ)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "D" => canonicalGammaDiffeomorph R hp hg hgenus hΓ hfree hsmooth

/-- The previously constructed original group WP family, with its complete
all-coefficient, all-region integral specification retained below. -/
@[instance_reducible] def gammaWeilPeterssonCore :
    letI := C
    letI := mΓ
    letI := CG
    ∀ a : LiZhongQC.TeichGamma Γ, InnerProductSpace.Core ℂ (TangentSpace TI a) := by
  letI := C
  letI := mΓ
  letI := CG
  exact Classical.choose
    (exists_gammaWeilPeterssonFamily_of_smoothing R hp hg hgenus hΓ hfree hsmooth)

/-- Actual group tangent vectors are identified with harmonic coefficients by
the inverse differential of the original normalized-lift biholomorphism. -/
def gammaWeilPeterssonTangentHarmonicEquiv (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    letI := C
    letI := mΓ
    letI := CG
    TangentSpace TI (D (β ν.val)) ≃L[ℂ]
      NativePetersson.Harmonic (deformedNativeSurface R hgenus hΓ hp ν) P
        (deformedTargetCover R hgenus hΓ hp ν)
        (deformedNativeSurface_uniformization R hgenus hΓ hp ν) F hF := by
  letI := C
  letI := mΓ
  letI := CG
  let J := canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth
    ((D).symm_apply_apply (β ν.val))
  exact (((D).symm.mfderivToContinuousLinearEquiv (by decide) (D (β ν.val))).trans J).trans
    (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth)

/-- This is the source's first-linear Hermitian integral on every original
group tangent fibre; the two Mathlib Core slots are exchanged. -/
theorem gammaWeilPeterssonCore_integral :
    letI := C
    letI := mΓ
    letI := CG
    ∀ (ν : Ball Γ)
      (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
      (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
      (v w : TangentSpace TI (D (β ν.val))),
      (gammaWeilPeterssonCore R hp hg hgenus hΓ hsmooth (D (β ν.val))).inner w v =
        WeilPetersson.beltramiPairing F
          (gammaWeilPeterssonTangentHarmonicEquiv R hp hg hgenus hΓ hsmooth ν P F hF v).val.val
          (gammaWeilPeterssonTangentHarmonicEquiv R hp hg hgenus hΓ hsmooth ν P F hF w).val.val := by
  let := C
  let := mΓ
  let := CG
  exact Classical.choose_spec
    (exists_gammaWeilPeterssonFamily_of_smoothing R hp hg hgenus hΓ hfree hsmooth)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
