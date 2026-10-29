module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.GeodesicPantsDecomposition
public import Mathlib.Data.Set.Pairwise.Basic

/-! A maximal disjoint simple geodesic family leaves no further simple
closed geodesic inside its complement or any complement component. -/

public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
variable {M : HyperbolicSurfaceModel R.toRiemannSurface} {L : Set (Set X)}

/-- An actual single-traversal closed geodesic cannot lie in the whole complement
of a maximal family on the same original surface. -/
theorem IsGeodesicDecomposingSystem.not_simple_closed_geodesic_subset_complement
    (hL : IsGeodesicDecomposingSystem M L) (q : OriginalClosedGeodesic M)
    (hq : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) :
    ¬ range q.curve ⊆ (⋃₀ L)ᶜ := by
  intro hsub
  have hdisjoint (C : Set X) (hC : C ∈ L) : Disjoint (range q.curve) C := by
    apply Set.disjoint_left.mpr
    intro x hxq hxC
    exact hsub hxq (Set.mem_sUnion.mpr ⟨C, hC, hxC⟩)
  have hfamily : IsSimpleGeodesicFamily M (insert (range q.curve) L) := by
    constructor
    · intro C hC
      rcases Set.mem_insert_iff.mp hC with rfl | hC
      · exact ⟨q, hq, rfl⟩
      · exact hL.exists_geodesic hC
    · apply hL.pairwise_disjoint.insert
      intro C hC _hne
      exact ⟨hdisjoint C hC, (hdisjoint C hC).symm⟩
  have hqL : range q.curve ∈ L := Maximal.mem_of_prop_insert hL hfamily
  exact Set.disjoint_left.mp (hdisjoint (range q.curve) hqL)
    (Set.mem_range_self (0 : ℝ)) (Set.mem_range_self (0 : ℝ))

/-- Each actual component in the existing associated family contains no original
simple closed geodesic, as used in the source's pants-classification argument. -/
theorem IsGeodesicDecomposingSystem.not_simple_closed_geodesic_subset_pantsComponent
    (hL : IsGeodesicDecomposingSystem M L) {P : Set X}
    (hP : P ∈ hL.pantsDecomposition) (q : OriginalClosedGeodesic M)
    (hq : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) :
    ¬ range q.curve ⊆ P := by
  intro hsub
  apply hL.not_simple_closed_geodesic_subset_complement q hq
  rcases hP with ⟨x, _hx, rfl⟩
  exact hsub.trans (connectedComponentIn_subset _ _)

end LowDimensionalTopology.Geometry.Surfaces
