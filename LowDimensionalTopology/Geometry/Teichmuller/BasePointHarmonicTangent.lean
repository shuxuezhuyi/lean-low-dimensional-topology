module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicDecomposition
public import LowDimensionalTopology.Geometry.Teichmuller.BasePointCotangentDuality

/-!
# Harmonic representatives of the original base-point tangent space

The genuine derivative restriction on harmonic classes and the literal
Petersson pairing identify the actual tangent fibre at the original identity
marking. Quantitative quasiconformal smoothing is precisely the existing
explicit premise for the canonical atlas on the original quotient topology.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NativePetersson

open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

/-- The actual harmonic class has the functional given by the literal full-region integral. -/
def harmonicPeterssonEquiv (hΓ : LiZhongQC.IsFuchsian Γ) :
    Harmonic R P p hp F hF ≃L[ℂ] StrongDual ℂ (Space R P p hp F hF) :=
  (harmonicDerivativeEquiv R P p hp F hF hΓ).trans
    (BersWeighted.automorphicPeterssonDuality R p hp hΓ P F hF)

/-- Every original vector and the unchanged planar pairing are retained. -/
theorem harmonicPeterssonEquiv_apply (hΓ : LiZhongQC.IsFuchsian Γ)
    (μ : Harmonic R P p hp F hF) (q : Space R P p hp F hF) :
    harmonicPeterssonEquiv R P p hp F hF hΓ μ q =
      ∫ z in UpperHalfPlane.coe '' F,
        GammaMeasurableBeltrami.planeRepresentative μ.val.val z *
          QuadraticBergman.uniformizedQuadratic R p
            (toQuadratic R P p hp F hF q) z := by
  rw [harmonicPeterssonEquiv, ContinuousLinearEquiv.trans_apply,
    harmonicDerivativeEquiv_apply]
  exact BersWeighted.automorphicPeterssonDuality_apply_derivative R p hp hΓ P F hF μ.val q

end LowDimensionalTopology.Geometry.Teichmuller.NativePetersson

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})

/-- The tangent fibre at the original identity marking has unique literal harmonic representatives. -/
def baseTangentHarmonicEquiv
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    TangentSpace 𝓘(ℂ, Fin (3 * g - 3) → ℂ) (basePoint R) ≃L[ℂ]
      NativePetersson.Harmonic R P p hp F hF :=
  (baseTangentPeterssonDuality R hg hgenus hΓ hfree hp hsmooth P F hF).trans
    (NativePetersson.harmonicPeterssonEquiv R P p hp F hF hΓ).symm

/-- The actual coefficient projection derivative is represented by its literal harmonic part. -/
theorem baseTangentHarmonicEquiv_derivative
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (μ : GammaMeasurableBeltrami.Space Γ) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    baseTangentHarmonicEquiv R hg hgenus hΓ hfree hp hsmooth P F hF
        (mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) 𝓘(ℂ, Fin (3 * g - 3) → ℂ)
          (baseCoefficientProjection R hg hgenus hΓ hfree hp) 0 μ) =
      (⟨NativePetersson.harmonicProjection R P p hp F hF μ, ⟨μ, rfl⟩⟩ :
        NativePetersson.Harmonic R P p hp F hF) := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  apply (NativePetersson.harmonicPeterssonEquiv R P p hp F hF hΓ).injective
  change NativePetersson.harmonicPeterssonEquiv R P p hp F hF hΓ
    ((NativePetersson.harmonicPeterssonEquiv R P p hp F hF hΓ).symm
      (baseTangentPeterssonDuality R hg hgenus hΓ hfree hp hsmooth P F hF
        (mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) 𝓘(ℂ, Fin (3 * g - 3) → ℂ)
          (baseCoefficientProjection R hg hgenus hΓ hfree hp) 0 μ))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply ContinuousLinearMap.ext
  intro q
  rw [baseTangentPeterssonDuality_derivative, NativePetersson.harmonicPeterssonEquiv_apply]
  exact NativePetersson.planar_pairing_harmonicProjection R P p hp F hF μ
    (NativePetersson.toQuadratic R P p hp F hF q)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
