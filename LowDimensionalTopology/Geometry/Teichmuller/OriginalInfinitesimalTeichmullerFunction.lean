module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientProjection
public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalQCMetric
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Infinitesimal full-log distance along an actual coefficient direction

Use the original marked-surface coefficient projection and the full-log
Teichmuller distance. The positive-direction limit is a totalized function;
its existence and descent to tangent classes are separate assertions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

local notation "π" => coefficientProjection R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp

/-- The positive-direction first variation of the original full-log distance,
written on the actual Beltrami coefficient ball and its vector space. -/
def coefficientInfinitesimalTeichmullerFunction (ξ : Ball Γ) (η : Space Γ) : ℝ :=
  Filter.limUnder (𝓝[>] (0 : ℝ))
    (fun t : ℝ => fromQCDistance R (π ξ.val) (π (ξ.val + (t : ℂ) • η)) / t)

/-- A genuine positive-direction distance limit determines this function.
No existence of the limit or norm property is asserted by this implication. -/
theorem coefficientInfinitesimalTeichmullerFunction_eq_of_tendsto
    (ξ : Ball Γ) (η : Space Γ) (L : ℝ)
    (hL : Tendsto
      (fun t : ℝ => fromQCDistance R (π ξ.val) (π (ξ.val + (t : ℂ) • η)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    coefficientInfinitesimalTeichmullerFunction R hg hgenus hΓ hfree hp ξ η = L := by
  exact hL.limUnder_eq

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
