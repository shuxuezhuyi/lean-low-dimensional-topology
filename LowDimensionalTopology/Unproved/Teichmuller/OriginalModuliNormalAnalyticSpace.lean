module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalModuliNormalAnalyticDefinition

/-!
# Normal analytic structure on the full original moduli quotient

This proposition records the complete external analytic-space assertion.
It has no theorem that restates the proposition as a proved conclusion.
-/

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces

/-- The specified singular normal analytic presentation exists on the full
original quotient in every original reference-surface and covering context. -/
def OriginalModuliNormalAnalyticSpace : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) {p : UpperHalfPlane → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace;
      LiZhongQC.IsUniformization Γ p),
    Geometry.Teichmuller.HasOriginalModuliNormalAnalyticPresentation R hg hgenus hΓ hp

end LowDimensionalTopology.Unproved.Teichmuller
