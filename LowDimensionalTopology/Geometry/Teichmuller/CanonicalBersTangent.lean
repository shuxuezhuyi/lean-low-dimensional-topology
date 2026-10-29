module

public import LowDimensionalTopology.Geometry.Teichmuller.BersWeightedCoordinates
public import LowDimensionalTopology.Geometry.Teichmuller.ComplexCanonicalAtlas
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# The actual canonical-atlas tangent fibre in the weighted Bers space

Use the differential of the existing Bers chart on the original realized
coefficient quotient topology. Its inverse coordinate map takes values in the
literal bounded automorphic normed space. The quantitative smoothing premise
is exactly the one already required for this canonical atlas.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
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

/-- The actual differential of the canonical Bers chart identifies each tangent
fibre with the full bounded holomorphic automorphic Bers space. -/
def canonicalBersTangentEquiv (a : TeichmullerSpace.{u, u} R) :
    letI := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
    TangentSpace 𝓘(ℂ, Fin (3 * g - 3) → ℂ) a ≃L[ℂ] BersWeighted.Automorphic Γ := by
  letI := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
  letI : IsManifold 𝓘(ℂ, Fin (3 * g - 3) → ℂ) ω (TeichmullerSpace.{u, u} R) :=
    canonicalComplex_isManifold R hg hgenus hPresentation hΓ hfree hp hsmooth
  let e := (mdifferentiable_chart (I := 𝓘(ℂ, Fin (3 * g - 3) → ℂ)) a).mfderiv
    (mem_chart_source (Fin (3 * g - 3) → ℂ) a)
  exact (e.trans (NormedSpace.fromTangentSpace _)).trans
    (weightedLinearBersCoordinates R hg hgenus hPresentation hΓ hp).symm

/-- This is the actual base-point tangent fibre of the canonical native atlas. -/
def canonicalBaseTangentEquiv :
    letI := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
    TangentSpace 𝓘(ℂ, Fin (3 * g - 3) → ℂ) (basePoint R) ≃L[ℂ]
      BersWeighted.Automorphic Γ :=
  canonicalBersTangentEquiv R hg hgenus hPresentation hΓ hfree hp hsmooth (basePoint R)

/-- In the original coordinates this equivalence is exactly the manifold
differential of the actual Bers coordinate function at the actual source point. -/
theorem canonicalBersTangentEquiv_coordinate_apply (a : TeichmullerSpace.{u, u} R) :
    letI := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
    ∀ v : TangentSpace 𝓘(ℂ, Fin (3 * g - 3) → ℂ) a,
      weightedLinearBersCoordinates R hg hgenus hPresentation hΓ hp
        (canonicalBersTangentEquiv R hg hgenus hPresentation hΓ hfree hp hsmooth a v) =
      (NormedSpace.fromTangentSpace
        (bersCoordinates R hg hgenus hPresentation hΓ hfree hp a))
        (mfderiv 𝓘(ℂ, Fin (3 * g - 3) → ℂ) 𝓘(ℂ, Fin (3 * g - 3) → ℂ)
          (bersCoordinates R hg hgenus hPresentation hΓ hfree hp) a v) := by
  let := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
  intro v
  change weightedLinearBersCoordinates R hg hgenus hPresentation hΓ hp
    ((weightedLinearBersCoordinates R hg hgenus hPresentation hΓ hp).symm
      ((NormedSpace.fromTangentSpace _)
        (mfderiv 𝓘(ℂ, Fin (3 * g - 3) → ℂ) 𝓘(ℂ, Fin (3 * g - 3) → ℂ)
          (chartAt (Fin (3 * g - 3) → ℂ) a) a v))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]; rfl

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
