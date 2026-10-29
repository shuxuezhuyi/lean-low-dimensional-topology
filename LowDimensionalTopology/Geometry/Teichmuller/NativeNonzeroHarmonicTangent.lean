module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeNonzeroTangentQuotient
public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicAhlforsWeill

/-!
# The actual nonzero tangent has its literal transported harmonic representative

The original derivative quotient carries its original L-infinity quotient
norm. Its actual nonzero derivative, the genuine coordinate-translation
derivative and the existing harmonic inverse identify it with the unchanged
harmonic space of the actual normalized deformed compact surface. On every
original coefficient direction the result is precisely H composed with L.

The original marked-surface tangent identification is induced by the actual
manifold derivative of its independently defined coefficient projection.
Only the existing canonical manifold atlas uses quantitative smoothing.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

local notation "RY" => deformedNativeSurface R hgenus hΓ hp ν
local notation "pY" => deformedTargetCover R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "HB" => NativePetersson.Harmonic RY P pY hpY F hF

/-- The actual nonzero quotient, through genuine coordinate derivatives, has unique harmonic representatives. -/
def nonzeroQuotientHarmonicEquiv :
    NonzeroTangentQuotient R hp hg hgenus hΓ ν ≃L[ℂ] HB :=
  ((nonzeroDerivativeQuotientEquiv R hp hg hgenus hΓ ν).trans
    (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm).trans
      (NativePetersson.harmonicDerivativeEquiv RY P pY hpY F hF (deformedGroup_spec hΓ ν).1).symm

/-- Every original direction is sent to the literal harmonic projection of its actual coefficient transport. -/
theorem nonzeroQuotientHarmonicEquiv_apply_mk (μ : Space Γ) :
    (nonzeroQuotientHarmonicEquiv R hp hg hgenus hΓ ν P F hF
      (Submodule.Quotient.mk μ)).val =
      NativePetersson.harmonicProjection RY P pY hpY F hF (gammaDerivative hΓ ν μ) := by
  have hc := congrArg (fun T : Space Γ →L[ℂ] BersWeighted.Automorphic (deformedGroup hΓ ν) => T μ)
    (nonzeroBersDerivative_commutation R hp hg hgenus hΓ ν)
  change (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm
      (nonzeroBersDerivative R hp hg hgenus hΓ ν μ) =
    BersWeighted.automorphicIntegralOperator (deformedGroup_spec hΓ ν).1
      (gammaDerivative hΓ ν μ) at hc
  change ((NativePetersson.harmonicDerivativeEquiv RY P pY hpY F hF
    (deformedGroup_spec hΓ ν).1).symm
      ((inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm
        (nonzeroDerivativeQuotientEquiv R hp hg hgenus hΓ ν
          (Submodule.Quotient.mk μ)))).val = _
  rw [nonzeroDerivativeQuotientEquiv_apply_mk, hc,
    NativePetersson.harmonicDerivativeEquiv_symm_val_eq_ahlforsWeill]
  exact (NativePetersson.harmonicProjection_eq_ahlforsWeill_integral
    RY P pY hpY F hF (deformedGroup_spec hΓ ν).1 (gammaDerivative hΓ ν μ)).symm


/-- The literal bounded H composed with L, in the existing harmonic subspace. -/
def harmonicTransport : Space Γ →L[ℂ] HB :=
  ((NativePetersson.harmonicProjection RY P pY hpY F hF).comp (gammaDerivative hΓ ν)).codRestrict
    (NativePetersson.harmonicSubmodule RY P pY hpY F hF)
    (fun μ => ⟨gammaDerivative hΓ ν μ, rfl⟩)

@[simp] theorem harmonicTransport_val (μ : Space Γ) :
    (harmonicTransport R hp hgenus hΓ ν P F hF μ).val =
      NativePetersson.harmonicProjection RY P pY hpY F hF (gammaDerivative hΓ ν μ) := rfl

/-- The equivalence is induced by the literal operator on the exact original quotient. -/
theorem harmonicTransport_eq_quotient :
    harmonicTransport R hp hgenus hΓ ν P F hF =
      (nonzeroQuotientHarmonicEquiv R hp hg hgenus hΓ ν P F hF).toContinuousLinearMap.comp
        (nonzeroInfinitesimalSubmodule R hp hg hgenus hΓ ν).mkQL := by
  apply ContinuousLinearMap.ext
  intro μ
  apply Subtype.ext
  exact (nonzeroQuotientHarmonicEquiv_apply_mk R hp hg hgenus hΓ ν P F hF μ).symm

/-- The kernel of the actual H L operator is exactly the genuine nonzero Bers derivative kernel. -/
theorem harmonicTransport_ker :
    (harmonicTransport R hp hgenus hΓ ν P F hF).ker =
      nonzeroInfinitesimalSubmodule R hp hg hgenus hΓ ν := by
  ext μ
  change harmonicTransport R hp hgenus hΓ ν P F hF μ = 0 ↔
    μ ∈ nonzeroInfinitesimalSubmodule R hp hg hgenus hΓ ν
  rw [harmonicTransport_eq_quotient]
  change nonzeroQuotientHarmonicEquiv R hp hg hgenus hΓ ν P F hF
      (Submodule.Quotient.mk μ) = 0 ↔
    μ ∈ nonzeroInfinitesimalSubmodule R hp hg hgenus hΓ ν
  rw [ContinuousLinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]

include hg in
/-- The literal transported harmonic projection reaches every original harmonic direction. -/
theorem harmonicTransport_surjective :
    Function.Surjective (harmonicTransport R hp hgenus hΓ ν P F hF) := by
  intro η
  obtain ⟨ξ, hξ⟩ := (nonzeroQuotientHarmonicEquiv R hp hg hgenus hΓ ν P F hF).surjective η
  obtain ⟨μ, rfl⟩ := Submodule.Quotient.mk_surjective
    (nonzeroInfinitesimalSubmodule R hp hg hgenus hΓ ν) ξ
  refine ⟨μ, ?_⟩
  rw [harmonicTransport_eq_quotient]
  exact hξ

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces NormalizedCoefficientTransport

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (ν : GammaMeasurableBeltrami.Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})

local notation "RY" => deformedNativeSurface R hgenus hΓ hp ν
local notation "pY" => deformedTargetCover R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "HB" => NativePetersson.Harmonic RY P pY hpY F hF
local notation "a" => coefficientProjection R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val
local notation "E" => Fin (3 * g - 3) → ℂ

/-- The actual original tangent at the actual marked point has its literal deformed harmonic model. -/
def nonzeroTangentHarmonicEquiv :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    TangentSpace 𝓘(ℂ, E) a ≃L[ℂ] HB :=
  ((canonicalBersTangentEquiv R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth a).trans
      (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm).trans
        (NativePetersson.harmonicDerivativeEquiv RY P pY hpY F hF (deformedGroup_spec hΓ ν).1).symm

/-- This is the same isomorphism induced by the exact original nonzero derivative quotient. -/
theorem nonzeroTangentHarmonicEquiv_quotient
    (ξ : NonzeroTangentQuotient R hp hg hgenus hΓ ν) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth
      (nonzeroDerivativeQuotientTangentEquiv R hp hg hgenus hΓ hfree ν hsmooth ξ) =
        nonzeroQuotientHarmonicEquiv R hp hg hgenus hΓ ν P F hF ξ := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  let e := canonicalBersTangentEquiv R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth a
  change (NativePetersson.harmonicDerivativeEquiv RY P pY hpY F hF
    (deformedGroup_spec hΓ ν).1).symm
      ((inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm
        (e (e.symm (nonzeroDerivativeQuotientEquiv R hp hg hgenus hΓ ν ξ)))) = _
  exact congrArg (fun φ : BersWeighted.Automorphic Γ =>
    (NativePetersson.harmonicDerivativeEquiv RY P pY hpY F hF (deformedGroup_spec hΓ ν).1).symm
      ((inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm φ))
    (e.apply_symm_apply (nonzeroDerivativeQuotientEquiv R hp hg hgenus hΓ ν ξ))

/-- The original projection's genuine manifold derivative is represented by the exact H L coefficient. -/
theorem nonzeroTangentHarmonicEquiv_derivative (μ : GammaMeasurableBeltrami.Space Γ) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth
      (mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) 𝓘(ℂ, E)
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp)
          ν.val μ) =
      (⟨NativePetersson.harmonicProjection RY P pY hpY F hF (gammaDerivative hΓ ν μ),
        ⟨gammaDerivative hΓ ν μ, rfl⟩⟩ : HB) := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  rw [← nonzeroDerivativeQuotientTangentEquiv_apply_mk R hp hg hgenus hΓ hfree ν hsmooth μ,
    nonzeroTangentHarmonicEquiv_quotient]
  apply Subtype.ext
  exact nonzeroQuotientHarmonicEquiv_apply_mk R hp hg hgenus hΓ ν P F hF μ

/-- The target is the actual identity tangent of the same normalized deformed compact surface. -/
def nonzeroTangentToDeformedBaseEquiv :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    letI := canonicalComplexChartedSpace RY hg
      (deformedNativeSurface_hasGenus R hgenus hΓ hp ν) (canonicalHandleGroupPresentation g)
      (deformedGroup_spec hΓ ν).1 (deformedNativeSurface_actsFreely R hgenus hΓ hp ν) hpY hsmooth
    TangentSpace 𝓘(ℂ, E) a ≃L[ℂ] TangentSpace 𝓘(ℂ, E) (basePoint RY) :=
  (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth).trans
    (deformedBaseTangentHarmonicEquiv R hgenus hΓ hp ν hg P F hF hsmooth).symm

/-- Actual coefficient projection derivatives on both original surfaces are intertwined by this tangent equivalence. -/
theorem nonzeroTangentToDeformedBaseEquiv_derivative (μ : GammaMeasurableBeltrami.Space Γ) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    letI := canonicalComplexChartedSpace RY hg
      (deformedNativeSurface_hasGenus R hgenus hΓ hp ν) (canonicalHandleGroupPresentation g)
      (deformedGroup_spec hΓ ν).1 (deformedNativeSurface_actsFreely R hgenus hΓ hp ν) hpY hsmooth
    nonzeroTangentToDeformedBaseEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth
      (mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) 𝓘(ℂ, E)
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp)
          ν.val μ) =
      mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space (deformedGroup hΓ ν)) 𝓘(ℂ, E)
        (baseCoefficientProjection RY hg (deformedNativeSurface_hasGenus R hgenus hΓ hp ν)
          (deformedGroup_spec hΓ ν).1 (deformedNativeSurface_actsFreely R hgenus hΓ hp ν) hpY)
        0 (gammaDerivative hΓ ν μ) := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  let := canonicalComplexChartedSpace RY hg
    (deformedNativeSurface_hasGenus R hgenus hΓ hp ν) (canonicalHandleGroupPresentation g)
    (deformedGroup_spec hΓ ν).1 (deformedNativeSurface_actsFreely R hgenus hΓ hp ν) hpY hsmooth
  let e := deformedBaseTangentHarmonicEquiv R hgenus hΓ hp ν hg P F hF hsmooth
  dsimp only [nonzeroTangentToDeformedBaseEquiv, ContinuousLinearEquiv.trans_apply]
  apply e.symm_apply_eq.mpr
  exact (nonzeroTangentHarmonicEquiv_derivative R hp hg hgenus hΓ hfree ν P F hF hsmooth μ).trans
    (deformedBaseTangentHarmonicEquiv_derivative R hgenus hΓ hp ν hg P F hF hsmooth
      (gammaDerivative hΓ ν μ)).symm

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
