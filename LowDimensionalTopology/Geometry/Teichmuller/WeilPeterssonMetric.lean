module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonFamily
public import LowDimensionalTopology.Geometry.Teichmuller.PeterssonIntegralNaturality

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport NativePetersson
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})

local notation "TI" => 𝓘(ℂ, Fin (3*g-3) → ℂ)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "D" => canonicalGammaDiffeomorph R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree

/-- Every original marked-surface tangent fibre has its positive Hermitian form
computed by the literal source integral for every coefficient and genuine region. -/
theorem exists_nativeWeilPeterssonFamily_of_smoothing :
    letI := C
    ∃ H : ∀ a : TeichmullerSpace.{u,u} R, InnerProductSpace.Core ℂ (TangentSpace TI a),
      ∀ (ν : Ball Γ)
        (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
        (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
        (v w : TangentSpace TI (β ν.val)),
        (H (β ν.val)).inner w v = WeilPetersson.beltramiPairing F
          (TH ν P F hF hsmooth v).val.val (TH ν P F hF hsmooth w).val.val :=
  exists_nativeWeilPeterssonFamily R hp hg hgenus hΓ hfree hsmooth
    (samePointPeterssonIntegralNaturality R hp hg hgenus hΓ hfree)

/-- The full original T(Gamma) tangent family is computed in every coefficient
and region using the actual inverse differential of the same biholomorphism. -/
theorem exists_gammaWeilPeterssonFamily_of_smoothing :
    letI := C
    letI := mΓ
    letI := CG
    ∃ H : ∀ q : LiZhongQC.TeichGamma Γ, InnerProductSpace.Core ℂ (TangentSpace TI q),
      ∀ (ν : Ball Γ)
        (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
        (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
        (v w : TangentSpace TI (D (β ν.val))),
        let J := canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth
          ((D).symm_apply_apply (β ν.val))
        let L := (D).symm.mfderivToContinuousLinearEquiv (by decide) (D (β ν.val))
        (H (D (β ν.val))).inner w v = WeilPetersson.beltramiPairing F
          (TH ν P F hF hsmooth (J (L v))).val.val
          (TH ν P F hF hsmooth (J (L w))).val.val :=
  exists_gammaWeilPeterssonFamily R hp hg hgenus hΓ hfree hsmooth
    (samePointPeterssonIntegralNaturality R hp hg hgenus hΓ hfree)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
