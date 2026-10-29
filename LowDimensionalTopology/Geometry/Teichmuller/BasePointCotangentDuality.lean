module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientProjectionDerivative
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge

/-!
# The canonical base-point cotangent duality on the original Teichmuller space

The original identity-marked base point, actual compatible-coefficient
projection, actual chart differential, and full Petersson continuous dual are
retained. The canonical handle-group presentation is the proved theorem;
it is not an outstanding hypothesis. Quantitative QC smoothing is precisely
the existing explicit analytic input for the canonical quotient complex atlas.
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
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : UpperHalfPlane → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

/-- The actual coefficient projection, using the proved native handle presentation. -/
def baseCoefficientProjection : GammaMeasurableBeltrami.Space Γ → TeichmullerSpace.{u, u} R :=
  coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp

/-- The original zero coefficient maps to the original identity marking. -/
theorem baseCoefficientProjection_zero :
    baseCoefficientProjection R hg hgenus hΓ hfree hp 0 = basePoint R :=
  coefficientProjection_zero R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp

variable (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})

/-- The original base-point tangent space is the continuous dual of the full
native quadratic Hilbert space with its actual Petersson norm. -/
def baseTangentPeterssonDuality
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    TangentSpace 𝓘(ℂ, Fin (3 * g - 3) → ℂ) (basePoint R) ≃L[ℂ]
      StrongDual ℂ (NativePetersson.Space R P p hp F hF) :=
  canonicalBasePeterssonDuality R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth P F hF

/-- This is the derivative of the actual coefficient quotient projection,
for the original canonical topology and its existing analytic atlas input. -/
theorem mdifferentiableAt_baseCoefficientProjection_zero :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    MDifferentiableAt 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ)
      𝓘(ℂ, Fin (3 * g - 3) → ℂ)
      (baseCoefficientProjection R hg hgenus hΓ hfree hp) 0 :=
  mdifferentiableAt_coefficientProjection_zero R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth

/-- The identification is induced by the literal Beltrami-quadratic integral
on the actual derivative of the actual coefficient projection at the original
identity marking. The target has the actual Petersson operator dual norm. -/
theorem baseTangentPeterssonDuality_derivative
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (μ : GammaMeasurableBeltrami.Space Γ)
    (q : NativePetersson.Space R P p hp F hF) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    baseTangentPeterssonDuality R hg hgenus hΓ hfree hp hsmooth P F hF
      (mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) 𝓘(ℂ, Fin (3 * g - 3) → ℂ)
        (baseCoefficientProjection R hg hgenus hΓ hfree hp) 0 μ) q =
      ∫ z in UpperHalfPlane.coe '' F,
        GammaMeasurableBeltrami.planeRepresentative μ.val z *
          QuadraticBergman.uniformizedQuadratic R p
            (NativePetersson.toQuadratic R P p hp F hF q) z :=
  canonicalBasePeterssonDuality_mfderiv_coefficientProjection R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth P F hF μ q

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
