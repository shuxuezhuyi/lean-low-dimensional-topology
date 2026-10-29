module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.HyperbolicPairOfPants
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Closed
public import Mathlib.Order.Minimal

/-!
# Decomposing curve systems on the same original hyperbolic surface

The book's definition is maximality under inclusion among pairwise disjoint
simple closed geodesic images. Existence and the cardinality formula are separate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
variable (M : HyperbolicSurfaceModel R.toRiemannSurface)

/-- Pairwise disjoint simple closed geodesic images in the original surface.
Simplicity uses the actual original period-circle map, as in the pants definition.
Taking geometric images removes parametrization and orientation duplicates. -/
def IsSimpleGeodesicFamily (L : Set (Set X)) : Prop :=
  (∀ C ∈ L, ∃ q : OriginalClosedGeodesic M,
    Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X) ∧ range q.curve = C) ∧
    L.Pairwise Disjoint

/-- An inclusion-maximal family of mutually disjoint simple closed geodesics,
the system of decomposing curves on the fixed surface. -/
def IsGeodesicDecomposingSystem (L : Set (Set X)) : Prop :=
  Maximal (IsSimpleGeodesicFamily M) L

variable {M} {L N : Set (Set X)}

/-- Every member retains an actual simple original closed geodesic witness. -/
theorem IsGeodesicDecomposingSystem.exists_geodesic
    (hL : IsGeodesicDecomposingSystem M L) {C : Set X} (hC : C ∈ L) :
    ∃ q : OriginalClosedGeodesic M,
      Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X) ∧ range q.curve = C := by
  exact hL.1.1 C hC

/-- Distinct members are disjoint as actual subsets of the original surface. -/
theorem IsGeodesicDecomposingSystem.pairwise_disjoint
    (hL : IsGeodesicDecomposingSystem M L) : L.Pairwise Disjoint := by
  exact hL.1.2

/-- Any family of the same kind containing the system equals it. -/
theorem IsGeodesicDecomposingSystem.eq_of_subset
    (hL : IsGeodesicDecomposingSystem M L)
    (hN : IsSimpleGeodesicFamily M N) (hLN : L ⊆ N) : N = L := by
  exact Set.Subset.antisymm (hL.2 hN hLN) hLN

end LowDimensionalTopology.Geometry.Surfaces
