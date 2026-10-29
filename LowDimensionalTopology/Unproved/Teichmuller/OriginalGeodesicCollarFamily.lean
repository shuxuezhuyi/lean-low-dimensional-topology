module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.EmbeddedDeltaCollar
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegion.CollarWidth

/-!
# Prescribed intrinsic collars of original disjoint geodesic families

The actual geodesic family can be finite or infinite. Each prescribed radial
half-width uses the full original single-traversal geodesic length. The
statement retains both the actual complete-cylinder intrinsic collar property
and disjointness of the literal original distance tubes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Unproved.Teichmuller
open LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Hyperbolic

/-- Disjoint original simple closed geodesics have the prescribed embedded
intrinsic collars, and their whole original open tubes are pairwise disjoint. -/
def OriginalGeodesicCollarFamily
    {X : Type*} [TopologicalSpace X] (R : RiemannSurface X)
    (M : HyperbolicSurfaceModel R) : Prop :=
  ∀ Γ : Set (OriginalClosedGeodesic M),
    (∀ q ∈ Γ, Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) →
    Γ.PairwiseDisjoint (fun q => Set.range q.curve) →
    (∀ q ∈ Γ, q.AdmitsEmbeddedDeltaCollar (collarHalfWidth q.length.toReal)) ∧
      Γ.PairwiseDisjoint (fun q => q.tubularNeighborhood (collarHalfWidth q.length.toReal))

end LowDimensionalTopology.Unproved.Teichmuller
