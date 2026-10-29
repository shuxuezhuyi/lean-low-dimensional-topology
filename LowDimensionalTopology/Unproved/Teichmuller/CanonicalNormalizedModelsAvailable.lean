module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalFuchsianModel

/-!
# Availability of actual normalized canonical models

This concrete existence obligation concerns every native marking with the same
prescribed ordered polygon homeomorphism. Importing it supplies no proof;
availability is not asserted for arbitrary polygon homeomorphisms.
-/

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller Geometry.Surfaces.HandlePresentation

/-- Actual normalized models for every native marked point with the same
prescribed ordered polygon marking. This is a concrete unproved existence fact. -/
def CanonicalNormalizedModelsAvailable
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) {g : ℕ}
    (hg : 1 < g) (e : X ≃ₜ PolygonQuotient g) : Prop :=
  ∀ m : MarkedRiemannSurface.{0, 0} R,
    Nonempty (NormalizedCanonicalFuchsianModel hg e m)

end LowDimensionalTopology.Unproved.Teichmuller
