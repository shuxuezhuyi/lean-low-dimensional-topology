module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.GeodesicPantsDecomposition
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed
public import Mathlib.Data.Set.Card

/-!
# Cardinalities of an original closed-surface decomposing system

The cutting argument uses boundary incidence and genus/component counts
for the original surface. The current native predicates provide the actual
maximal geodesic family and its full complement components, but no existing
implementation of those cutting identities was found. The whole exact
conclusion is therefore named here as an unproved proposition. No
surface-classification or new cutting theory is constructed, and no purely
numerical substitute replaces the original family or its components.
-/

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Surfaces

open Geometry.Surfaces

/-- Every actual maximal disjoint simple-geodesic family on the given original
closed genus-at-least-two surface is finite, its entire complement-component
family is finite, and their cardinalities are respectively `3g-3` and `2g-2`.
The component family is the already defined literal family of connected
components of the original complement. -/
def ClosedDecomposingSystemCardinalities
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) {g : ℕ}
    (_hg : 2 ≤ g) (_hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) : Prop :=
  ∀ L : Set (Set X), IsGeodesicDecomposingSystem M L →
    L.Finite ∧ (geodesicComplementComponents L).Finite ∧
      L.ncard = 3 * g - 3 ∧ (geodesicComplementComponents L).ncard = 2 * g - 2

end LowDimensionalTopology.Unproved.Surfaces
