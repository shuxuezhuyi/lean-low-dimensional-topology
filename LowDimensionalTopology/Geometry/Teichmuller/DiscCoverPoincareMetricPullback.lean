module

public import LowDimensionalTopology.Geometry.Teichmuller.DiscCoverPoincareMetric
public import LowDimensionalTopology.Geometry.Teichmuller.DiscCoverPoincarePullback

/-!
# The prescribed pullback identity for the constructed Poincaré metric

The constructed native metric satisfies its prescribed inverse-sheet formula.
Applying the same-cover tangent cancellation gives the complete two-slot identity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Hyperbolic

variable {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}

/-- The constructed metric pulls back along the same specified disk covering to
the disk Poincaré tensor, with both vectors in the original source tangent fiber. -/
theorem discCoverAtlasInducedMetric_pullback (M : HyperbolicSurfaceModel R) :
    let := discRiemannSurface.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ (z : extendedUnitDisc) (v w : RealSurfaceTangent discRiemannSurface z),
      (discCoverAtlasInducedMetric M).metric.inner (M.discCover z)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) M.discCover z v)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) M.discCover z w) =
        discPoincareTensor (discFiniteChart z)
          (mvfderiv 𝓘(ℝ, ℂ) (discFiniteChart : extendedUnitDisc → ℂ) z v)
          (mvfderiv 𝓘(ℝ, ℂ) (discFiniteChart : extendedUnitDisc → ℂ) z w) := by
  exact discCover_pullback_of_local_sheet_tensor M
    (discCoverAtlasInducedMetric M).metric
    (discCoverAtlasInducedMetric_inner_eq_sheet_tensor M)

end LowDimensionalTopology.Geometry.Teichmuller
