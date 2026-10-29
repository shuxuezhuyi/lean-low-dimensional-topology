module

public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalQCMetric
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalGlobalFricke

/-!
# Continuity of the actual book Fricke coordinates

This independent continuity obligation concerns the original QC metric and
the literal finite book coordinates. Importing it supplies no proof.
-/

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller Geometry.Surfaces.HandlePresentation

/-- The book Fricke map is continuous from the actual full-log QC metric
to its literal finite Euclidean coordinates. -/
def NativeFrickeCoordinateContinuity
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) {g : ℕ}
    (hg : 1 < g) (hgenus : R.HasGenus g) (e : X ≃ₜ PolygonQuotient g)
    (hA : CanonicalNormalizedModelsAvailable R hg e) : Prop :=
  letI : MetricSpace (TeichmullerSpace.{0, 0} R) :=
    TeichmullerSpace.qcMetricSpace R hg hgenus
  Continuous (finiteFrickeCoordinates hA)

end LowDimensionalTopology.Unproved.Teichmuller
