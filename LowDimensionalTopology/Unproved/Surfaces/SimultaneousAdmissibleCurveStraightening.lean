module

public import LowDimensionalTopology.Geometry.Surfaces.AdmissibleReduction
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed

/-!
# Simultaneous straightening of two original admissible curve families

The two families consist of actual embedded essential circles on the same
original surface. Their supplied index equivalence matches unoriented free
classes. The conclusion retains an actual correcting homeomorphism,
homotopic to the identity, and each individual geometric image equality.
This is an independent unresolved classical input, not a reducibility
conclusion or a definition of ambient isotopy.
-/

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Surfaces

open Geometry.Surfaces

/-- Two actual finite nonempty admissible circle families with matching
unoriented free classes can be aligned simultaneously by an actual
homeomorphism homotopic to the identity. -/
def SimultaneousAdmissibleCurveStraightening
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) (g : ℕ) : Prop :=
  1 < g → R.HasGenus g →
    ∀ C D : AdmissibleMulticurve X, ∀ e : C.curves ≃ D.curves,
      (∀ c : C.curves, c.val.freeClass = (e c).val.freeClass) →
      ∃ h : X ≃ₜ X,
        ContinuousMap.Homotopic (_root_.toContinuousMap h) (ContinuousMap.id X) ∧
          ∀ c : C.curves, h '' Set.range c.val.val = Set.range (e c).val.val

end LowDimensionalTopology.Unproved.Surfaces
