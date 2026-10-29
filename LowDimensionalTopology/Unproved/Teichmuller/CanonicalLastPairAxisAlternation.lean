module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalFuchsianModel

/-!
# Alternation of the actual final canonical pair

The missing geometric fact is narrowly about a supplied normalized model's
actual canonical endpoint decks. Importing this proposition supplies no proof
and asserts no availability of a polygon marking or normalized model.
-/

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller Geometry.Surfaces.HandlePresentation

/-- The final canonical a/b axes cross: after the actual b-endpoints are
normalized to zero and infinity, the a-matrix has positive off-diagonal product.
This is the concrete original-surface geometric obligation, not coordinate
separation. Negating an individual determinant-one lift preserves the product. -/
def CanonicalLastPairAxisAlternation
    {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
    {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g} {m : MarkedRiemannSurface.{0, 0} R}
    (P : NormalizedCanonicalFuchsianModel hg e m) : Prop :=
  0 < P.matrices (finalHandle hg, 0) 0 1 * P.matrices (finalHandle hg, 0) 1 0

end LowDimensionalTopology.Unproved.Teichmuller
