module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.PairOfPantsModel
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Data.Set.Card

/-!
# The three connected components of the standard planar model's frontier

The circles are connected by Mathlib's sphere theorem. Closed separation shows
that each is an entire component of the actual ambient frontier, giving an
exact census for the open region and its closed carrier.
-/

public section
open Set Metric

namespace LowDimensionalTopology.Geometry.Surfaces

/-- Each of the three actual Euclidean boundary circles is connected. -/
theorem isConnected_pantsModelBoundaryCircle (i : Fin 3) :
    IsConnected (pantsModelBoundaryCircle i) := by
  have hdim : 1 < Module.rank ℝ ℂ := by simp
  fin_cases i
  · simpa using isConnected_sphere hdim (0 : ℂ) (by norm_num : 0 ≤ (2 : ℝ))
  · simpa using isConnected_sphere hdim (-1 : ℂ) (by norm_num : 0 ≤ (1 : ℝ) / 2)
  · simpa using isConnected_sphere hdim (1 : ℂ) (by norm_num : 0 ≤ (1 : ℝ) / 2)

private theorem connectedComponentIn_union_eq_left {A B : Set ℂ}
    (hA : IsClosed A) (hB : IsClosed B) (hd : Disjoint A B)
    (hc : IsPreconnected A) {x : ℂ} (hx : x ∈ A) :
    connectedComponentIn (A ∪ B) x = A := by
  apply Subset.antisymm
  · intro y hy
    by_contra hya
    have hyb : y ∈ B := (connectedComponentIn_subset _ _ hy).resolve_left hya
    have hxC : x ∈ connectedComponentIn (A ∪ B) x := mem_connectedComponentIn (Or.inl hx)
    have hC : IsPreconnected (connectedComponentIn (A ∪ B) x) :=
      isPreconnected_connectedComponentIn
    obtain ⟨z, _, hza, hzb⟩ := (isPreconnected_closed_iff.mp hC) A B hA hB
      (connectedComponentIn_subset _ _) ⟨x, hxC, hx⟩ ⟨y, hy, hyb⟩
    exact Set.disjoint_left.mp hd hza hzb
  · exact hc.subset_connectedComponentIn hx Set.subset_union_left

/-- Every point of a labelled circle has that whole circle as its component in
the frontier of the original open planar region. -/
theorem connectedComponentIn_frontier_pantsPlanarRegion (i : Fin 3) {x : ℂ}
    (hx : x ∈ pantsModelBoundaryCircle i) :
    connectedComponentIn (frontier pantsPlanarRegion) x = pantsModelBoundaryCircle i := by
  let B : Set ℂ := ⋃ j : {j : Fin 3 // j ≠ i}, pantsModelBoundaryCircle j.1
  have hB : IsClosed B := isClosed_iUnion_of_finite fun j =>
    (isCompact_pantsModelBoundaryCircle j.1).isClosed
  have hd : Disjoint (pantsModelBoundaryCircle i) B := by
    apply Set.disjoint_left.mpr
    intro z hzi hzB
    obtain ⟨j, hzj⟩ := mem_iUnion.mp hzB
    exact Set.disjoint_left.mp (pantsModelBoundaryCircle_pairwise_disjoint j.2.symm) hzi hzj
  have hF : frontier pantsPlanarRegion = pantsModelBoundaryCircle i ∪ B := by
    rw [frontier_pantsPlanarRegion]
    apply Subset.antisymm
    · intro z hz
      obtain ⟨j, hzj⟩ := mem_iUnion.mp hz
      by_cases hji : j = i
      · subst j
        exact Or.inl hzj
      · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hzj⟩)
    · rintro z (hz | hz)
      · exact mem_iUnion.mpr ⟨i, hz⟩
      · obtain ⟨j, hzj⟩ := mem_iUnion.mp hz
        exact mem_iUnion.mpr ⟨j.1, hzj⟩
  rw [hF]
  exact connectedComponentIn_union_eq_left
    (isCompact_pantsModelBoundaryCircle i).isClosed hB hd
    (isConnected_pantsModelBoundaryCircle i).isPreconnected hx

/-- The closed carrier has the same genuine boundary components. -/
theorem connectedComponentIn_frontier_pantsClosedPlanarRegion (i : Fin 3) {x : ℂ}
    (hx : x ∈ pantsModelBoundaryCircle i) :
    connectedComponentIn (frontier pantsClosedPlanarRegion) x = pantsModelBoundaryCircle i := by
  rw [frontier_pantsClosedPlanarRegion, ← frontier_pantsPlanarRegion]
  exact connectedComponentIn_frontier_pantsPlanarRegion i hx

/-- The three labels give three distinct boundary circles. -/
theorem pantsModelBoundaryCircle_injective : Function.Injective pantsModelBoundaryCircle := by
  intro i j hij
  by_contra hne
  obtain ⟨x, hx⟩ := pantsModelBoundaryCircle_nonempty i
  exact Set.disjoint_left.mp (pantsModelBoundaryCircle_pairwise_disjoint hne) hx (hij ▸ hx)

/-- The components at all frontier points are exactly the labelled circles. -/
theorem pantsPlanarRegion_boundaryComponents_eq_range :
    {C : Set ℂ | ∃ x ∈ frontier pantsPlanarRegion,
      connectedComponentIn (frontier pantsPlanarRegion) x = C} =
      range pantsModelBoundaryCircle := by
  ext C
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [frontier_pantsPlanarRegion] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨i, (connectedComponentIn_frontier_pantsPlanarRegion i hi).symm⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨x, hx⟩ := pantsModelBoundaryCircle_nonempty i
    refine ⟨x, ?_, connectedComponentIn_frontier_pantsPlanarRegion i hx⟩
    rw [frontier_pantsPlanarRegion]
    exact mem_iUnion.mpr ⟨i, hx⟩

/-- The original open region has exactly three ambient frontier components. -/
theorem pantsPlanarRegion_boundaryComponents_ncard :
    {C : Set ℂ | ∃ x ∈ frontier pantsPlanarRegion,
      connectedComponentIn (frontier pantsPlanarRegion) x = C}.ncard = 3 := by
  rw [pantsPlanarRegion_boundaryComponents_eq_range]
  simpa using Set.ncard_range_of_injective pantsModelBoundaryCircle_injective

/-- The closed carrier has exactly the same three labelled frontier components. -/
theorem pantsClosedPlanarRegion_boundaryComponents_eq_range :
    {C : Set ℂ | ∃ x ∈ frontier pantsClosedPlanarRegion,
      connectedComponentIn (frontier pantsClosedPlanarRegion) x = C} =
      range pantsModelBoundaryCircle := by
  simpa only [frontier_pantsClosedPlanarRegion, frontier_pantsPlanarRegion] using
    pantsPlanarRegion_boundaryComponents_eq_range

/-- The closed carrier also has exactly three ambient frontier components. -/
theorem pantsClosedPlanarRegion_boundaryComponents_ncard :
    {C : Set ℂ | ∃ x ∈ frontier pantsClosedPlanarRegion,
      connectedComponentIn (frontier pantsClosedPlanarRegion) x = C}.ncard = 3 := by
  rw [pantsClosedPlanarRegion_boundaryComponents_eq_range]
  simpa using Set.ncard_range_of_injective pantsModelBoundaryCircle_injective

end LowDimensionalTopology.Geometry.Surfaces
