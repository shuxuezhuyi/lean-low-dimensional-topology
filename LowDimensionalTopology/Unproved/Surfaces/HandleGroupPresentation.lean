module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CanonicalHandleBasePoint
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S22_RiemannSurfaces

@[expose] public section

noncomputable section

namespace LowDimensionalTopology.Unproved

open Geometry.Surfaces

/-- Outstanding presentation theorem for the actual canonical closed handle
surface at its specified point. This definition supplies no proof. In
particular it does not posit a generating tuple in some unrelated group. -/
def HandleGroupPresentation (g : ℕ) : Prop :=
  Nonempty (FundamentalGroup (CanonicalHandleSurface g) (canonicalHandleBasePoint g) ≃*
    LiZhongQC.surfaceGroup g)

end LowDimensionalTopology.Unproved
