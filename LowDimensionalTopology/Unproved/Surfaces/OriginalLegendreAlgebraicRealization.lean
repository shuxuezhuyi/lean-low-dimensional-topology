module

public import LowDimensionalTopology.Geometry.Surfaces.OriginalLegendreIntegralData

/-!
# Analytic realization of the concrete Legendre cubic

The realization retains the given topological carrier, its finite algebraic
coordinates and the normalized differential. No analytic surface or genus
structure is inferred merely from its one-point-compactification topology.
-/

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Surfaces

open Geometry.Surfaces

/-- Existence of the actual compact analytic cubic and its regular dz/w form. -/
def OriginalLegendreAlgebraicRealization : Prop :=
  ∀ l : LegendreParameter, Nonempty (OriginalLegendreRealization l)

end LowDimensionalTopology.Unproved.Surfaces
