module

public import LowDimensionalTopology.Geometry.Teichmuller.ComplexCanonicalAtlas
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalGlobalFricke

/-!
# Real analyticity of the existing Fricke coordinates in the native Bers atlas

This concrete classical prerequisite compares the literal finite Fricke map
with the same canonical native Bers atlas. Importing this proposition proves
nothing. Only the forward map is asserted. The quotient and atlas are unchanged;
no length regularity, differential or cotangent field is an input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller Geometry.Surfaces.HandlePresentation

/-- The literal finite Fricke coordinate map is real analytic in the same
canonical native Bers atlas. No inverse-map compatibility is assumed. -/
def NativeFrickeBersRealAnalyticCompatibility
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (hsmooth : QuasiconformalSmoothing.{0})
    {e : X ≃ₜ PolygonQuotient g}
    (hA : CanonicalNormalizedModelsAvailable R hg e) : Prop :=
  letI := TeichmullerSpace.canonicalComplexChartedSpace R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
  ContMDiff 𝓘(ℝ, Fin (3 * g - 3) → ℂ) 𝓘(ℝ, Fin (6 * g - 6) → ℝ) ω
    (finiteFrickeCoordinates hA)

end LowDimensionalTopology.Unproved.Teichmuller
