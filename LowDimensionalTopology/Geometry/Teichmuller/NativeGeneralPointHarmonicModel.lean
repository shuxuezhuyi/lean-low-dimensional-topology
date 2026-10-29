module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeNonzeroTangentNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.GammaSourcePointRepresentability

/-!
# The literal harmonic transport models every original general-point tangent

The actual source group classes and normalized-lift equivalence identify the
original marked point. The quotient model is induced by the literal harmonic
projection after the actual all-coefficient derivative transport. Its two
original tangent identifications commute with the genuine coefficient
projection derivatives. Changing a representative compares quotient directions
through their actual common tangent, independently of the harmonic map.
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

/-- Source group-point equality is exactly equality of the actual native
coefficient points under the normalized-lift equivalence. -/
theorem coefficientProjectionBall_eq_iff_sourcePoint
    (ν ν' : GammaMeasurableBeltrami.Ball Γ) :
    coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ hfree hp ν =
      coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ hfree hp ν' ↔
    (Quotient.mk _ (GammaMeasurableBeltrami.toSourceGamma ν) : LiZhongQC.TeichGamma Γ) =
      Quotient.mk _ (GammaMeasurableBeltrami.toSourceGamma ν') := by
  exact (gammaEquiv R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp).symm.injective.eq_iff

/-- Every original group point is represented by a genuine compatible
coefficient class, at precisely the corresponding native marked point. -/
theorem exists_nativeCoefficientPoint_for_source (q : LiZhongQC.TeichGamma Γ) :
    ∃ ν : GammaMeasurableBeltrami.Ball Γ,
      (Quotient.mk _ (GammaMeasurableBeltrami.toSourceGamma ν) : LiZhongQC.TeichGamma Γ) = q ∧
      coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ hfree hp ν =
        (gammaEquiv R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp).symm q := by
  obtain ⟨ν, hν⟩ := GammaMeasurableBeltrami.exists_nativeBall_sourcePoint q
  exact ⟨ν, hν, congrArg
    (gammaEquiv R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp).symm hν⟩

/-- The actual native coordinates are exactly the original source Bers
coordinates, rather than coordinates of a separately selected model. -/
theorem bersCoordinates_gammaEquiv_symm (q : LiZhongQC.TeichGamma Γ) :
    bersCoordinates R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp
      ((gammaEquiv R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp).symm q) =
    linearBersCoordinates R hg hgenus (canonicalHandleGroupPresentation g) hΓ hp
      ⟨LiZhongQC.bersMapGamma Γ q, (LiZhongQC.bersMapGamma_mem hΓ q).1⟩ := by
  simp only [bersCoordinates, Equiv.apply_symm_apply]

/-- The independently defined original projection has the exact source group
point even when expressed on its derivative's ambient domain. -/
theorem coefficientProjection_gammaSourcePoint (ν : GammaMeasurableBeltrami.Ball Γ) :
    gammaEquiv R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp
      (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val) =
    (Quotient.mk _ (GammaMeasurableBeltrami.toSourceGamma ν) : LiZhongQC.TeichGamma Γ) := by
  rw [coefficientProjection_ball R hg hgenus hΓ hfree hp ν]
  exact (gammaEquiv R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp).apply_symm_apply _

variable (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})
    (ν : GammaMeasurableBeltrami.Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "RY" => deformedNativeSurface R hgenus hΓ hp ν
local notation "pY" => deformedTargetCover R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "hY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν
local notation "hfY" => deformedNativeSurface_actsFreely R hgenus hΓ hp ν
local notation "N" => nonzeroInfinitesimalSubmodule R hp hg hgenus hΓ ν
local notation "Q" => NonzeroTangentQuotient R hp hg hgenus hΓ ν
local notation "HB" => NativePetersson.Harmonic RY P pY hpY F hF
local notation "L" => gammaDerivative hΓ ν
local notation "H" => NativePetersson.harmonicProjection RY P pY hpY F hF
local notation "HL" => harmonicTransport R hp hgenus hΓ ν P F hF
local notation "QH" => nonzeroQuotientHarmonicEquiv R hp hg hgenus hΓ ν P F hF
local notation "QT" => nonzeroDerivativeQuotientTangentEquiv R hp hg hgenus hΓ hfree ν hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth
local notation "TB" => nonzeroTangentToDeformedBaseEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth
local notation "DΠ" => mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) 𝓘(ℂ, E)
  (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp) ν.val
local notation "DΠ₀" => mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space (deformedGroup hΓ ν)) 𝓘(ℂ, E)
  (baseCoefficientProjection RY hg hY (And.left (deformedGroup_spec hΓ ν)) hfY hpY) 0

/-- The literal full coefficient operator, exact original quotient, actual
original point tangent, and actual deformed identity tangent form the complete
commuting harmonic model. Only their original manifold atlases use smoothing. -/
theorem generalPoint_harmonic_tangent_model :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    letI := canonicalComplexChartedSpace RY hg hY (canonicalHandleGroupPresentation g)
      (deformedGroup_spec hΓ ν).1 hfY hpY hsmooth
    gammaEquiv R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val) =
        (Quotient.mk _ (GammaMeasurableBeltrami.toSourceGamma ν) : LiZhongQC.TeichGamma Γ) ∧
      gammaEquiv RY hg hY (canonicalHandleGroupPresentation g)
        (deformedGroup_spec hΓ ν).1 hfY hpY (basePoint RY) =
          LiZhongQC.TeichGamma.origin (deformedGroup hΓ ν) ∧
      (HL).ker = N ∧ Function.Surjective HL ∧
      HL = (QH).toContinuousLinearMap.comp (N).mkQL ∧
      (∀ μ : GammaMeasurableBeltrami.Space Γ,
        (HL μ).val = BersWeighted.ahlforsWeill
          (BersWeighted.automorphicIntegralOperator (deformedGroup_spec hΓ ν).1 (L μ))) ∧
      (∀ μ : GammaMeasurableBeltrami.Space Γ,
        (QH (Submodule.Quotient.mk μ)).val = H (L μ)) ∧
      (∀ μ : GammaMeasurableBeltrami.Space Γ, QT (Submodule.Quotient.mk μ) = DΠ μ) ∧
      (∀ ξ : Q, TH (QT ξ) = QH ξ) ∧
      (∀ μ : GammaMeasurableBeltrami.Space Γ,
        TH (DΠ μ) = (⟨H (L μ), ⟨L μ, rfl⟩⟩ : HB)) ∧
      (∀ μ : GammaMeasurableBeltrami.Space Γ, TB (DΠ μ) = DΠ₀ (L μ)) := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  let := canonicalComplexChartedSpace RY hg hY (canonicalHandleGroupPresentation g)
    (deformedGroup_spec hΓ ν).1 hfY hpY hsmooth
  exact ⟨coefficientProjection_gammaSourcePoint R hp hg hgenus hΓ hfree ν,
    gammaEquiv_basePoint RY hg hY (canonicalHandleGroupPresentation g)
      (deformedGroup_spec hΓ ν).1 hfY hpY,
    harmonicTransport_ker R hp hg hgenus hΓ ν P F hF,
    harmonicTransport_surjective R hp hg hgenus hΓ ν P F hF,
    harmonicTransport_eq_quotient R hp hg hgenus hΓ ν P F hF,
    fun μ => (harmonicTransport_val R hp hgenus hΓ ν P F hF μ).trans
      (NativePetersson.harmonicProjection_eq_ahlforsWeill_integral
        RY P pY hpY F hF (deformedGroup_spec hΓ ν).1 (L μ)),
    nonzeroQuotientHarmonicEquiv_apply_mk R hp hg hgenus hΓ ν P F hF,
    nonzeroDerivativeQuotientTangentEquiv_apply_mk R hp hg hgenus hΓ hfree ν hsmooth,
    nonzeroTangentHarmonicEquiv_quotient R hp hg hgenus hΓ hfree ν P F hF hsmooth,
    nonzeroTangentHarmonicEquiv_derivative R hp hg hgenus hΓ hfree ν P F hF hsmooth,
    nonzeroTangentToDeformedBaseEquiv_derivative R hp hg hgenus hΓ hfree ν P F hF hsmooth⟩

variable (ν' : GammaMeasurableBeltrami.Ball Γ)
    (hsource : (Quotient.mk _ (GammaMeasurableBeltrami.toSourceGamma ν) :
        LiZhongQC.TeichGamma Γ) = Quotient.mk _ (GammaMeasurableBeltrami.toSourceGamma ν'))
    (P' : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν').map Hyperbolic.realSLMobius))
    (F' : Set ℍ) (hF' : Fuchsian.IsHalfPlaneFundamentalRegion P' F')

/-- The quotient harmonic maps agree for every pair of representatives of the
same original group point. The domain comparison is induced by their actual
projection derivatives and equality of the original point, independently of H. -/
theorem generalPoint_harmonic_quotient_independent :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    let hpoint := (coefficientProjectionBall_eq_iff_sourcePoint
      R hp hg hgenus hΓ hfree ν ν').mpr hsource
    let J := canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth
      (coefficientProjection_eq_of_sameNativePoint R hp hg hgenus hΓ hfree ν ν' hpoint)
    let QT' := nonzeroDerivativeQuotientTangentEquiv R hp hg hgenus hΓ hfree ν' hsmooth
    let transition := ((QT).trans J).trans QT'.symm
    (∀ ξ : Q, QT' (transition ξ) = J (QT ξ)) ∧
      (∀ ξ : Q,
        nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint
          P F hF P' F' hF' (QH ξ) =
        nonzeroQuotientHarmonicEquiv R hp hg hgenus hΓ ν' P' F' hF' (transition ξ)) := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  have hpoint := (coefficientProjectionBall_eq_iff_sourcePoint
    R hp hg hgenus hΓ hfree ν ν').mpr hsource
  let J := canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth
    (coefficientProjection_eq_of_sameNativePoint R hp hg hgenus hΓ hfree ν ν' hpoint)
  let QT' := nonzeroDerivativeQuotientTangentEquiv R hp hg hgenus hΓ hfree ν' hsmooth
  let transition := ((QT).trans J).trans QT'.symm
  constructor
  · intro ξ
    exact QT'.apply_symm_apply (J (QT ξ))
  · intro ξ
    have hT : QT' (transition ξ) = J (QT ξ) := QT'.apply_symm_apply (J (QT ξ))
    have hNat := nonzeroTangentHarmonicEquiv_natural
      R hp hg hgenus hΓ hfree hsmooth ν ν' hpoint P F hF P' F' hF' (QT ξ)
    have hQ := nonzeroTangentHarmonicEquiv_quotient
      R hp hg hgenus hΓ hfree ν P F hF hsmooth ξ
    have hQ' := nonzeroTangentHarmonicEquiv_quotient
      R hp hg hgenus hΓ hfree ν' P' F' hF' hsmooth (transition ξ)
    exact (congrArg
      (nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint
        P F hF P' F' hF') hQ).symm.trans
          (hNat.trans ((congrArg
            (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν' P' F' hF' hsmooth) hT).symm.trans hQ'))

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
