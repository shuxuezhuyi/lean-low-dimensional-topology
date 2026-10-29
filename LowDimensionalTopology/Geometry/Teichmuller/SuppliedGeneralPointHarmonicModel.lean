module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeGeneralPointHarmonicModel
public import LowDimensionalTopology.Geometry.Teichmuller.SourceFuchsianRegions

/-!
# Original general-point harmonic models with their geometric data supplied

Only original uniformization data, coefficient classes and the existing
explicit smoothing statement are inputs. Genuine native group and open-region
data for each exact deformed group come from their proved source existence.
The original arbitrary-region interfaces remain available independently.
-/

public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces NormalizedCoefficientTransport

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})
    (ν : GammaMeasurableBeltrami.Ball Γ)

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "RY" => deformedNativeSurface R hgenus hΓ hp ν
local notation "pY" => deformedTargetCover R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "hY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν
local notation "hfY" => deformedNativeSurface_actsFreely R hgenus hΓ hp ν
local notation "N" => nonzeroInfinitesimalSubmodule R hp hg hgenus hΓ ν
local notation "Q" => NonzeroTangentQuotient R hp hg hgenus hΓ ν
local notation "L" => gammaDerivative hΓ ν
local notation "QT" => nonzeroDerivativeQuotientTangentEquiv R hp hg hgenus hΓ hfree ν hsmooth
local notation "DΠ" => mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) 𝓘(ℂ, E)
  (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp) ν.val
local notation "DΠ₀" => mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space (deformedGroup hΓ ν)) 𝓘(ℂ, E)
  (baseCoefficientProjection RY hg hY (And.left (deformedGroup_spec hΓ ν)) hfY hpY) 0

/-- Every original coefficient has its complete literal harmonic quotient and
original tangent model; the required geometric regions are proved to exist. -/
theorem exists_generalPoint_harmonic_tangent_model :
    ∃ (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
      (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F),
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    letI := canonicalComplexChartedSpace RY hg hY (canonicalHandleGroupPresentation g)
      (deformedGroup_spec hΓ ν).1 hfY hpY hsmooth
    let H := NativePetersson.harmonicProjection RY P pY hpY F hF
    let HL := harmonicTransport R hp hgenus hΓ ν P F hF
    let QH := nonzeroQuotientHarmonicEquiv R hp hg hgenus hΓ ν P F hF
    let TH := nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth
    let TB := nonzeroTangentToDeformedBaseEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth
    gammaEquiv R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val) =
        (Quotient.mk _ (GammaMeasurableBeltrami.toSourceGamma ν) : LiZhongQC.TeichGamma Γ) ∧
      gammaEquiv RY hg hY (canonicalHandleGroupPresentation g)
        (deformedGroup_spec hΓ ν).1 hfY hpY (basePoint RY) =
          LiZhongQC.TeichGamma.origin (deformedGroup hΓ ν) ∧
      HL.ker = N ∧ Function.Surjective HL ∧
      HL = QH.toContinuousLinearMap.comp (N).mkQL ∧
      (∀ μ : GammaMeasurableBeltrami.Space Γ,
        (HL μ).val = BersWeighted.ahlforsWeill
          (BersWeighted.automorphicIntegralOperator (deformedGroup_spec hΓ ν).1 (L μ))) ∧
      (∀ μ : GammaMeasurableBeltrami.Space Γ,
        (QH (Submodule.Quotient.mk μ)).val = H (L μ)) ∧
      (∀ μ : GammaMeasurableBeltrami.Space Γ, QT (Submodule.Quotient.mk μ) = DΠ μ) ∧
      (∀ ξ : Q, TH (QT ξ) = QH ξ) ∧
      (∀ μ : GammaMeasurableBeltrami.Space Γ,
        TH (DΠ μ) = (⟨H (L μ), ⟨L μ, rfl⟩⟩ : NativePetersson.Harmonic RY P pY hpY F hF)) ∧
      (∀ μ : GammaMeasurableBeltrami.Space Γ, TB (DΠ μ) = DΠ₀ (L μ)) := by
  obtain ⟨P, F, hF⟩ := exists_deformedHalfPlaneFundamentalRegion R hgenus hΓ hp ν
  exact ⟨P, F, hF, generalPoint_harmonic_tangent_model R hp hg hgenus hΓ hfree hsmooth ν P F hF⟩

/-- Representatives of the same actual original point have supplied harmonic
models with the intrinsic quotient comparison induced by that common tangent.
No equality of raw operators on a fixed direction at different bases is used. -/
theorem exists_generalPoint_harmonic_models_independent
    (ν' : GammaMeasurableBeltrami.Ball Γ)
    (hpoint : coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ hfree hp ν =
      coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ hfree hp ν') :
    ∃ (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
      (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
      (P' : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν').map Hyperbolic.realSLMobius))
      (F' : Set ℍ) (hF' : Fuchsian.IsHalfPlaneFundamentalRegion P' F'),
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    let J := canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth
      (coefficientProjection_eq_of_sameNativePoint R hp hg hgenus hΓ hfree ν ν' hpoint)
    let QT' := nonzeroDerivativeQuotientTangentEquiv R hp hg hgenus hΓ hfree ν' hsmooth
    let transition := ((QT).trans J).trans QT'.symm
    (Quotient.mk _ (GammaMeasurableBeltrami.toSourceGamma ν) : LiZhongQC.TeichGamma Γ) =
        Quotient.mk _ (GammaMeasurableBeltrami.toSourceGamma ν') ∧
      (∀ ξ : Q, QT' (transition ξ) = J (QT ξ)) ∧
      (∀ ξ : Q,
        nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint
          P F hF P' F' hF'
          (nonzeroQuotientHarmonicEquiv R hp hg hgenus hΓ ν P F hF ξ) =
        nonzeroQuotientHarmonicEquiv R hp hg hgenus hΓ ν' P' F' hF' (transition ξ)) := by
  obtain ⟨P, F, hF⟩ := exists_deformedHalfPlaneFundamentalRegion R hgenus hΓ hp ν
  obtain ⟨P', F', hF'⟩ := exists_deformedHalfPlaneFundamentalRegion R hgenus hΓ hp ν'
  have hsource := (coefficientProjectionBall_eq_iff_sourcePoint
    R hp hg hgenus hΓ hfree ν ν').mp hpoint
  refine ⟨P, F, hF, P', F', hF', hsource, ?_⟩
  exact generalPoint_harmonic_quotient_independent R hp hg hgenus hΓ hfree hsmooth
    ν P F hF ν' hsource P' F' hF'

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
