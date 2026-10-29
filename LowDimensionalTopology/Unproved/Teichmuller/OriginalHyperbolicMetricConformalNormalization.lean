module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricGaussianCurvature
public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricEquivalence
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed

/-!
# Native negative-curvature normalization in one conformal class

The existing native genus and compact uniformization already supply genuine
hyperbolic conformal models. This classical metric prerequisite is precisely
the unique smooth native Gaussian-curvature-minus-one representative in each
same-identity conformal class. It contains no quotient or orbit comparison.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller
universe u

/-- Every native conformal class in the existing higher-genus regime has one
unique actual Gaussian-curvature-minus-one metric, with a global smooth
exponential factor on all original tangent slots. No quotient is assumed. -/
def OriginalHyperbolicMetricConformalNormalization : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (R : ClosedRiemannSurface X)
      (hreg : Quasiconformal.SmoothCompactBeltramiRegularity)
      (hcurv : OriginalSmoothMetricGaussianCurvature.{u})
      (genus : ℕ), R.HasGenus genus → 1 < genus →
    ∀ g : SmoothSurfaceMetric R.toRiemannSurface,
      ∃! h : SmoothSurfaceMetric R.toRiemannSurface,
        h ∈ curvatureMinusOneMetrics R hreg hcurv ∧
          IsRawMetricConformal g h (SmoothSurfaceEquiv.refl R.toRiemannSurface)

end LowDimensionalTopology.Unproved.Teichmuller
