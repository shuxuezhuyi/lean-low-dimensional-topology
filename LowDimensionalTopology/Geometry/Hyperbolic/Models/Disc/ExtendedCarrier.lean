module
public import LowDimensionalTopology.Geometry.Mobius.FractionalLinear

/-!
# Open and closed discs in the extended complex plane.

The finite points of norm less than, or at most, one define the open and closed unit
discs in the one-point compactification. The closed disc is closed in this topology.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped OnePoint Topology

namespace LowDimensionalTopology.Geometry.Hyperbolic

def extendedUnitDisc : Set Mobius.ExtendedComplex :=
  (OnePoint.some : ℂ → Mobius.ExtendedComplex) '' {z : ℂ | ‖z‖ < 1}

def extendedClosedUnitDisc : Set Mobius.ExtendedComplex :=
  (OnePoint.some : ℂ → Mobius.ExtendedComplex) '' {z : ℂ | ‖z‖ ≤ 1}

theorem coe_mem_extendedUnitDisc (z : ℂ) :
    (z : Mobius.ExtendedComplex) ∈ extendedUnitDisc ↔ ‖z‖ < 1 := by
  simp [extendedUnitDisc]

theorem coe_mem_extendedClosedUnitDisc (z : ℂ) :
    (z : Mobius.ExtendedComplex) ∈ extendedClosedUnitDisc ↔ ‖z‖ ≤ 1 := by
  simp [extendedClosedUnitDisc]

theorem extendedUnitDisc_subset_closed : extendedUnitDisc ⊆ extendedClosedUnitDisc := by
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z, (show ‖z‖ < 1 from hz).le, rfl⟩

theorem isClosed_extendedClosedUnitDisc : IsClosed extendedClosedUnitDisc := by
  have hcompact : IsCompact {z : ℂ | ‖z‖ ≤ 1} := by
    simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : ℂ) 1
  exact (hcompact.image OnePoint.continuous_coe).isClosed

end LowDimensionalTopology.Geometry.Hyperbolic
