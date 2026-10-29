module

public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalQCMetric
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Isometric real lines for the quasiconformal distance

Distance preservation on the real line is expressed using the actual
quasiconformal infimum metric on the marked quotient.
-/

public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces
universe u

/-- An isometric real line preserves the full quasiconformal distance. -/
theorem isometry_iff_fromQCDistance_eq_abs
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (f : ℝ → TeichmullerSpace.{u, u} R) :
    letI := qcMetricSpace R hg hgenus
    Isometry f ↔ ∀ s t, fromQCDistance R (f s) (f t) = |s - t| := by
  let := qcMetricSpace R hg hgenus
  rw [isometry_iff_dist_eq]
  simp only [qcMetricSpace_dist R hg hgenus, Real.dist_eq]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
