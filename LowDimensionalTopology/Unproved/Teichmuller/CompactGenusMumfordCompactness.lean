module

public import LowDimensionalTopology.Geometry.Teichmuller.CompactGenusModuliTopology
public import LowDimensionalTopology.Geometry.Teichmuller.CompactGenusThickPart

/-!
# Compactness of the original thick subset of the full moduli quotient

The full compact-genus quotient carries the topology coinduced by the actual
native QC metric for the fixed reference. The independent positive smooth
markability premise is explicit, so the projection covers every original
compact target. This is a concrete unresolved compactness proposition;
its definition supplies no compactness proof.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)

/-- Every positive original systole threshold defines a compact subset of
the full compact-genus moduli quotient with the actual QC quotient topology.
The independent marking premise makes this quotient cover all targets. -/
def CompactGenusMumfordCompactness : Prop :=
  PositiveSmoothMarkability R →
    letI : TopologicalSpace (CompactGenusModuliSpace g) :=
      CompactGenusModuliSpace.qcTopology R hg hgenus
    ∀ ε : ℝ, 0 < ε → IsCompact (compactGenusThickPart (Nat.succ_le_of_lt hg) ε)

end LowDimensionalTopology.Unproved.Teichmuller
