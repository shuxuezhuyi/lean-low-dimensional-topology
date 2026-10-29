module

public import LowDimensionalTopology.Geometry.Teichmuller.CompactGenusModuli
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalSystole

/-!
# The hyperbolically thick subset of the literal compact-genus quotient

The subset is the quotient image of all actual compact genus-g surfaces
whose original closed-geodesic systole is at least the given threshold.
Every target retains its original carrier, topology, atlas and genuine
hyperbolic model. No marking or topology on the moduli set is needed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

/-- The full quotient image of actual compact genus-g surfaces satisfying
the original hyperbolic systole threshold. -/
def compactGenusThickPart {g : ℕ} (hg : 2 ≤ g) (ε : ℝ) :
    Set (CompactGenusModuliSpace g) :=
  CompactGenusModuliSpace.mk ''
    {S : CompactGenusSurface g |
      ε ≤ originalHyperbolicSystole S.surface
        (S.surface.hyperbolicOfGenusGeTwo hg S.hasGenus).model}

end LowDimensionalTopology.Geometry.Teichmuller
