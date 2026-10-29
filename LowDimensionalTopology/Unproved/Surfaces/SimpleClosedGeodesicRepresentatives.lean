module

public import LowDimensionalTopology.Geometry.Surfaces.EssentialSimpleFreeClasses
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedGeodesicExistence
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed
public import LowDimensionalTopology.Geometry.Teichmuller.CircleRepresentativeLoops

/-!
# Simple geodesic representatives on the original closed surface

The condition assigns a closed geodesic in the same full free homotopy class
to every essential embedded circle. Its actual period-circle map is injective,
so the complete period traverses the simple geodesic once.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Surfaces

open Geometry.Surfaces Geometry.Teichmuller

/-- Every actual essential simple circle on the original closed genus-at-least-two
surface has an actual single-traversal simple geodesic representative. -/
def SimpleClosedGeodesicRepresentatives
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) (g : ℕ)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) : Prop :=
  2 ≤ g → R.HasGenus g → ∀ c : EssentialSimpleCircle X,
    ∃ q : OriginalClosedGeodesic M,
      LiZhongQC.FreelyHomotopic (circleRepresentativeLoop c.val) q.toLoop ∧
        Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)

end LowDimensionalTopology.Unproved.Surfaces
