module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge
public import LowDimensionalTopology.Geometry.Teichmuller.NativeTeichmullerMetric

/-!
# The complete QC metric in the native handle genus

The proved canonical handle presentation gives the actual equivalence between
native smooth-marked classes and QC-marked source classes. Pulling back the
full-log QC metric gives explicit complete metric data on the native quotient.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u

namespace TeichmullerSpace

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The actual native smooth-marked quotient is equivalent to the QC-marked quotient. -/
def qcEquiv {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) :
    TeichmullerSpace.{u, u} R ≃
      letI := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.TeichSpace X :=
  sourceEquiv R hg hgenus (canonicalHandleGroupPresentation g)

/-- Explicit metric data from genuine marking-compatible QC homeomorphisms. -/
@[instance_reducible] def qcMetricSpace {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) :
    MetricSpace (TeichmullerSpace.{u, u} R) :=
  fromQCMetricSpace R hg hgenus (canonicalHandleGroupPresentation g)

/-- The metric distance is the actual full-log QC infimum on source representatives. -/
theorem qcMetricSpace_dist {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (p q : TeichmullerSpace.{u, u} R) :
    let : MetricSpace (TeichmullerSpace.{u, u} R) := qcMetricSpace R hg hgenus
    dist p q = fromQCDistance R p q := by
  exact fromQCMetricSpace_dist R hg hgenus (canonicalHandleGroupPresentation g) p q

/-- The explicit QC metric on the native smooth-marked quotient is complete. -/
theorem qcMetricSpace_complete {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) :
    let : MetricSpace (TeichmullerSpace.{u, u} R) := qcMetricSpace R hg hgenus
    CompleteSpace (TeichmullerSpace.{u, u} R) := by
  exact fromQCMetricSpace_complete R hg hgenus (canonicalHandleGroupPresentation g)

end TeichmullerSpace

end LowDimensionalTopology.Geometry.Teichmuller
