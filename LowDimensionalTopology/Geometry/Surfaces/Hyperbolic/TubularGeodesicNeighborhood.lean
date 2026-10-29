module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedGeodesicTraceUniqueness
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.RectifiableCurves

/-!
# The actual intrinsic tube around an original closed geodesic

Distance to the geometric trace is the infimum of full hyperbolic lengths of
all original-atlas rectifiable curves joining the supplied point to that trace.
The radius is a radial half-width on the original surface.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal unitInterval

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
  {M : HyperbolicSurfaceModel R}

/-- Intrinsic hyperbolic distance from the original point to the entire actual
geodesic trace, taking the infimum over all original-atlas rectifiable paths. -/
def OriginalClosedGeodesic.distanceToTrace (q : OriginalClosedGeodesic M) (p : X) : ℝ≥0∞ :=
  ⨅ c : RiemannSurfaceRectifiableCurvePiece R,
    ⨅ (_hstart : c.curve 0 = p) (_hend : c.curve 1 ∈ Set.range q.curve),
      M.rectifiableCurveLength c

/-- The strict intrinsic tube of the given radial half-width around the actual
original geometric closed geodesic. -/
def OriginalClosedGeodesic.tubularNeighborhood (q : OriginalClosedGeodesic M) (δ : ℝ) : Set X :=
  {p | q.distanceToTrace p < ENNReal.ofReal δ}

end LowDimensionalTopology.Geometry.Surfaces
