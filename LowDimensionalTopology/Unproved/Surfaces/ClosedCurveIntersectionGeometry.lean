module

public import LowDimensionalTopology.Geometry.Surfaces.EssentialSimpleFreeClasses
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed

/-!
# Representative geometry for closed-surface intersection counts

This independent classical obligation concerns only actual simple circles on
the original surface. Importing the proposition supplies no proof.
-/

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Surfaces

open Geometry.Surfaces

/-- Every pair of original classes has finitely intersecting representatives;
each class has two disjoint representatives; and each class has a dual class
whose original representatives always intersect it. -/
def ClosedCurveIntersectionGeometry
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) {g : ℕ}
    (_hg : 2 ≤ g) (_hgenus : R.HasGenus g) : Prop :=
  (∀ a b : EssentialSimpleFreeClass X,
    ∃ c d : EssentialSimpleCircle X,
      c.freeClass = a ∧ d.freeClass = b ∧
        (Set.range c.val ∩ Set.range d.val).Finite) ∧
  (∀ a : EssentialSimpleFreeClass X,
    ∃ c d : EssentialSimpleCircle X,
      c.freeClass = a ∧ d.freeClass = a ∧
        Disjoint (Set.range c.val) (Set.range d.val)) ∧
  ∀ a : EssentialSimpleFreeClass X,
    ∃ b : EssentialSimpleFreeClass X,
      ∀ c d : EssentialSimpleCircle X,
        c.freeClass = a → d.freeClass = b →
          (Set.range c.val ∩ Set.range d.val).Nonempty

end LowDimensionalTopology.Unproved.Surfaces
