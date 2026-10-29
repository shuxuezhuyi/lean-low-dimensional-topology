module

public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalBersTangent
public import LowDimensionalTopology.Geometry.Teichmuller.BersDerivativeQuotient

/-!
# The actual base-point tangent fibre and the full Petersson continuous dual

The tangent space is the genuine fibre of the existing canonical complex atlas
on the realized coefficient quotient topology. Its identification with the
automorphic model is the differential of the actual Bers chart. The quotient
identification uses the actual surjective Bers Fréchet derivative, and the
dual identification is induced by the literal fundamental-region pairing.
All existing atlas hypotheses, including quantitative QC smoothing, remain explicit.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hPresentation : Unproved.HandleGroupPresentation g)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : UpperHalfPlane → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})

/-- The actual closed-kernel quotient is identified with the actual base-point
tangent fibre through the original chart differential and true Bers derivative. -/
def canonicalDerivativeQuotientTangentEquiv :
    letI := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
    NativePetersson.TangentQuotient Γ ≃L[ℂ]
      TangentSpace 𝓘(ℂ, Fin (3 * g - 3) → ℂ) (basePoint R) := by
  letI := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
  exact (BersWeighted.derivativeQuotientEquiv R p hp hΓ).trans
    (canonicalBaseTangentEquiv R hg hgenus hPresentation hΓ hfree hp hsmooth).symm

/-- The genuine base-point tangent space is continuously complex-linearly
isomorphic to the continuous dual of the full original Petersson Hilbert space. -/
def canonicalBasePeterssonDuality
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    letI := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
    TangentSpace 𝓘(ℂ, Fin (3 * g - 3) → ℂ) (basePoint R) ≃L[ℂ]
      StrongDual ℂ (NativePetersson.Space R P p hp F hF) := by
  letI := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
  exact (canonicalBaseTangentEquiv R hg hgenus hPresentation hΓ hfree hp hsmooth).trans
    (BersWeighted.automorphicPeterssonDuality R p hp hΓ P F hF)

/-- On every original Beltrami direction, the chart differential of the
corresponding tangent vector is exactly the already proved Bers derivative. -/
theorem canonicalDerivativeQuotientTangentEquiv_coordinate_apply
    (μ : GammaMeasurableBeltrami.Space Γ) :
    letI := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
    (NormedSpace.fromTangentSpace
      (bersCoordinates R hg hgenus hPresentation hΓ hfree hp (basePoint R)))
      (mfderiv 𝓘(ℂ, Fin (3 * g - 3) → ℂ) 𝓘(ℂ, Fin (3 * g - 3) → ℂ)
        (bersCoordinates R hg hgenus hPresentation hΓ hfree hp) (basePoint R)
        (canonicalDerivativeQuotientTangentEquiv R hg hgenus hPresentation hΓ hfree hp hsmooth
          (Submodule.Quotient.mk μ))) =
      weightedLinearBersCoordinates R hg hgenus hPresentation hΓ hp
        (BersWeighted.automorphicIntegralOperator hΓ μ) := by
  let := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
  have he := canonicalBersTangentEquiv_coordinate_apply R hg hgenus hPresentation hΓ hfree hp
    hsmooth (basePoint R)
    (canonicalDerivativeQuotientTangentEquiv R hg hgenus hPresentation hΓ hfree hp hsmooth
      (Submodule.Quotient.mk μ))
  change weightedLinearBersCoordinates R hg hgenus hPresentation hΓ hp
    ((canonicalBaseTangentEquiv R hg hgenus hPresentation hΓ hfree hp hsmooth)
      ((canonicalBaseTangentEquiv R hg hgenus hPresentation hΓ hfree hp hsmooth).symm
        (BersWeighted.derivativeQuotientEquiv R p hp hΓ (Submodule.Quotient.mk μ)))) = _ at he
  rw [ContinuousLinearEquiv.apply_symm_apply,
    BersWeighted.derivativeQuotientEquiv_apply_mk] at he
  exact he.symm

/-- The tangent-to-dual identification is induced by the exact original
fundamental-region integral. The quotient tangent equivalence is onto, so this
identity describes its value on every actual base-point tangent vector. -/
theorem canonicalBasePeterssonDuality_apply_quotient
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (μ : GammaMeasurableBeltrami.Space Γ)
    (q : NativePetersson.Space R P p hp F hF) :
    letI := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
    canonicalBasePeterssonDuality R hg hgenus hPresentation hΓ hfree hp hsmooth P F hF
      (canonicalDerivativeQuotientTangentEquiv R hg hgenus hPresentation hΓ hfree hp hsmooth
        (Submodule.Quotient.mk μ)) q =
      ∫ z in UpperHalfPlane.coe '' F,
        GammaMeasurableBeltrami.planeRepresentative μ.val z *
          QuadraticBergman.uniformizedQuadratic R p
            (NativePetersson.toQuadratic R P p hp F hF q) z := by
  let := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
  change BersWeighted.automorphicPeterssonDuality R p hp hΓ P F hF
    ((canonicalBaseTangentEquiv R hg hgenus hPresentation hΓ hfree hp hsmooth)
      ((canonicalBaseTangentEquiv R hg hgenus hPresentation hΓ hfree hp hsmooth).symm
        (BersWeighted.derivativeQuotientEquiv R p hp hΓ (Submodule.Quotient.mk μ)))) q = _
  rw [ContinuousLinearEquiv.apply_symm_apply, BersWeighted.derivativeQuotientEquiv_apply_mk]
  exact BersWeighted.automorphicPeterssonDuality_apply_derivative R p hp hΓ P F hF μ q

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
