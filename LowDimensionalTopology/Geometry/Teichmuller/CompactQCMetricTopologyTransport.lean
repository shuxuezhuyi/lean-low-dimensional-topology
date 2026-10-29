module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCMetric
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCClosedCompatibility
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersProjectionTopology

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
open Surfaces GammaMeasurableBeltrami TeichmullerSpace
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

/-- For the original compact reference, its actual normalized-lift identification
is a homeomorphism for the original full-log topology and its group transport. -/
def closedGammaHomeomorph :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := distanceTopology.{u,u} (Surface.ofRiemannSurface R.toRiemannSurface)
    letI := gammaQCMetricSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
    ClosedSpace R ≃ₜ LiZhongQC.TeichGamma Γ := by
  letI := R.toRiemannAtlas.toChartedSpace
  letI := pseudoMetricSpace.{u,u} (Surface.ofRiemannSurface R.toRiemannSurface)
  letI := gammaQCMetricSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let S := sourceGammaEquiv R hg hgenus (canonicalHandleGroupPresentation g) hΓ
    (LiZhongQC.s27g_actsFreely hp) hp
  let E := (closedSourceEquiv R).trans S.symm
  have hE : Isometry (E : ClosedSpace R → LiZhongQC.TeichGamma Γ) := by
    apply isometry_iff_dist_eq.mpr
    intro a b
    rw [gammaQCMetricSpace_dist R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp]
    have hS := sourceGammaEquiv_distance R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ (LiZhongQC.s27g_actsFreely hp) hp (E a) (E b)
    change LiZhongQC.teichDistanceGamma (E a) (E b) =
      LiZhongQC.teichDistance (S (E a)) (S (E b)) at hS
    rw [hS]
    change 2 * LiZhongQC.teichDistance
      (S (S.symm (closedSourceEquiv R a))) (S (S.symm (closedSourceEquiv R b))) =
        distance a b
    rw [S.apply_symm_apply, S.apply_symm_apply]
    exact (closedSourceEquiv_distance R a b).symm
  exact { E with
    continuous_toFun := hE.continuous
    continuous_invFun := (hE.right_inv E.right_inv).continuous }

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
