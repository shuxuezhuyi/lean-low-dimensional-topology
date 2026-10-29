module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed
public import LowDimensionalTopology.External.Jacobians.Forms.Genus

/-!
# Comparison of analytic and topological genus

This file states the outstanding comparison for the actual complex atlas of a
closed Riemann surface. Its proposition supplies no proof of that comparison.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Surfaces

open Geometry.Surfaces

universe u

/-- The dimension of holomorphic one-forms equals the topological handle genus,
using precisely the complex atlas of the given closed Riemann surface. -/
def GenusComparison {X : Type u} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) (g : ℕ) : Prop :=
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  R.HasGenus g → _root_.genus X = g

end LowDimensionalTopology.Unproved.Surfaces
