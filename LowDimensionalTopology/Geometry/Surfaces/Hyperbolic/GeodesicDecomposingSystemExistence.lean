module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.GeodesicDecomposingSystem
public import Mathlib.Order.Zorn

/-!
# Maximal families of actual original simple closed geodesics

Chain unions preserve the original single-traversal geodesic witnesses and
pairwise disjointness. Zorn extends every such family to a decomposing system.
This proves existence of the existing maximal-family predicate only; finiteness
and the geometric type of the complement require separate theorems.
-/

public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
variable {M : HyperbolicSurfaceModel R.toRiemannSurface}

/-- The union of an inclusion chain preserves actual simple geodesic images. -/
theorem IsSimpleGeodesicFamily.sUnion_of_isChain
    {c : Set (Set (Set X))} (hchain : IsChain (· ⊆ ·) c)
    (hc : ∀ L ∈ c, IsSimpleGeodesicFamily M L) :
    IsSimpleGeodesicFamily M (⋃₀ c) := by
  constructor
  · intro C hC
    obtain ⟨L, hL, hCL⟩ := Set.mem_sUnion.mp hC
    exact (hc L hL).1 C hCL
  · intro C hC D hD hCD
    obtain ⟨L, hL, hCL⟩ := Set.mem_sUnion.mp hC
    obtain ⟨N, hN, hDN⟩ := Set.mem_sUnion.mp hD
    rcases hchain.total hL hN with hLN | hNL
    · exact (hc N hN).2 (hLN hCL) hDN hCD
    · exact (hc L hL).2 hCL (hNL hDN) hCD

/-- Every given family of the original kind extends to an actual maximal one. -/
theorem IsSimpleGeodesicFamily.exists_decomposingSystem_superset
    {L₀ : Set (Set X)} (hL₀ : IsSimpleGeodesicFamily M L₀) :
    ∃ L : Set (Set X), L₀ ⊆ L ∧ IsGeodesicDecomposingSystem M L := by
  classical
  refine zorn_subset_nonempty
    {L : Set (Set X) | IsSimpleGeodesicFamily M L} ?_ L₀ hL₀
  intro c hc hchain _hcne
  refine ⟨⋃₀ c, ?_, ?_⟩
  · exact IsSimpleGeodesicFamily.sUnion_of_isChain hchain (fun L hL => hc hL)
  · intro L hL
    exact Set.subset_sUnion_of_mem hL

/-- The existing maximal-family definition is inhabited on the same surface. -/
theorem HyperbolicSurfaceModel.exists_geodesicDecomposingSystem
    (M : HyperbolicSurfaceModel R.toRiemannSurface) :
    ∃ L : Set (Set X), IsGeodesicDecomposingSystem M L := by
  have hempty : IsSimpleGeodesicFamily M (∅ : Set (Set X)) := by
    simp [IsSimpleGeodesicFamily]
  obtain ⟨L, _hEL, hL⟩ :=
    IsSimpleGeodesicFamily.exists_decomposingSystem_superset hempty
  exact ⟨L, hL⟩

end LowDimensionalTopology.Geometry.Surfaces
