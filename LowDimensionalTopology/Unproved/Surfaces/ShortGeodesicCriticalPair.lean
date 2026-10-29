module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.ShortOriginalClosedGeodesics
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# A fixed geometric witness for the sharp short-geodesic cutoff

Two simple closed geodesics on one whole-disc-quotient hyperbolic surface
have distinct intersecting images and both original lengths equal to the
critical cutoff. The native model fixes the Poincaré metric and BV lengths.
-/

@[expose] public section
noncomputable section

namespace LowDimensionalTopology.Unproved.Surfaces
open LowDimensionalTopology.Geometry.Surfaces

/-- Two distinct intersecting simple geodesics on one actual complete
disc-quotient surface, both with the fixed critical original length. -/
def ShortGeodesicCriticalPair : Prop :=
  ∃ (X : Type) (t : TopologicalSpace X),
    letI : TopologicalSpace X := t
    ∃ (R : RiemannSurface X) (M : HyperbolicSurfaceModel R)
      (q r : OriginalClosedGeodesic M),
      Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X) ∧
      Function.Injective (r.periodic.lift : AddCircle (1 : ℝ) → X) ∧
      Set.range q.curve ≠ Set.range r.curve ∧
      ¬ Disjoint (Set.range q.curve) (Set.range r.curve) ∧
      q.length.toReal = shortClosedGeodesicCutoff ∧
      r.length.toReal = shortClosedGeodesicCutoff

end LowDimensionalTopology.Unproved.Surfaces
