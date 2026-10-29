module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed
public import LowDimensionalTopology.Geometry.Teichmuller.Marking

/-!
# Positive smooth markability from a fixed closed reference surface

This proposition concerns one fixed reference surface and targets in the same
universe. Importing its definition supplies no proof of the general smooth
classification bridge. The proved genus-zero special case remains separate.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller

universe u

/-- Every original closed target of the same handle genus as the fixed
reference admits a positive real smooth marking, with no prescribed map. -/
def PositiveSmoothMarkability {X : Type u} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) : Prop :=
  ∀ {Y : Type u} [TopologicalSpace Y] (S : ClosedRiemannSurface Y) (g : ℕ),
    R.HasGenus g → S.HasGenus g →
      ∃ F : SmoothSurfaceEquiv R.toRiemannSurface S.toRiemannSurface,
        PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas F.toHomeomorph

end LowDimensionalTopology.Unproved.Teichmuller
