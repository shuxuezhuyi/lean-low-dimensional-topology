/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonBoundaryConvexity
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace LowDimensionalTopology.Geometry.Polygon

set_option backward.isDefEq.respectTransparency false in
/-- A genuine locally linear two-sided Jordan boundary selects exactly one strict affine
half-plane as the local inside, with no global convexity premise. -/
theorem complex_jordan_linear_boundary_interior_germ {I O B : Set ℂ} {x : ℂ}
    (hI : IsOpen I) (hO : IsOpen O) (hd : Disjoint I O) (hu : I ∪ O = Bᶜ)
    (hxI : x ∈ frontier I) (hxO : x ∈ frontier O) (f : ℂ →ᵃ[ℝ] ℝ)
    (he : ∀ᶠ y in 𝓝 x, y ∈ B ↔ f y = 0) :
    (∀ᶠ y in 𝓝 x, y ∈ I ↔ 0 < f y) ∨ (∀ᶠ y in 𝓝 x, y ∈ I ↔ f y < 0) := by
  obtain ⟨r,hr,hre⟩ := Metric.mem_nhds_iff.mp he
  let A : Set ℂ := Metric.ball x r ∩ {y | 0 < f y}
  let C : Set ℂ := Metric.ball x r ∩ {y | f y < 0}
  have hAc : IsPreconnected A :=
    ((convex_ball x r).inter ((convex_Ioi (0 : ℝ)).affine_preimage f)).isPreconnected
  have hCc : IsPreconnected C :=
    ((convex_ball x r).inter ((convex_Iio (0 : ℝ)).affine_preimage f)).isPreconnected
  have hmem (y : ℂ) (hy : y ∈ Metric.ball x r) :
      (y ∈ I ∨ y ∈ O) ↔ f y ≠ 0 := by
    change y ∈ I ∪ O ↔ _
    have hh : y ∈ B ↔ f y = 0 := hre hy
    rw [hu,mem_compl_iff,hh]
  have hAsub : A ⊆ I ∪ O := by
    intro y hy
    exact (hmem y hy.1).mpr (ne_of_gt hy.2)
  have hCsub : C ⊆ I ∪ O := by
    intro y hy
    exact (hmem y hy.1).mpr (ne_of_lt hy.2)
  have hexI : ∃ y ∈ Metric.ball x r, y ∈ I := by
    exact mem_closure_iff.mp (frontier_subset_closure hxI) (Metric.ball x r)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hexO : ∃ y ∈ Metric.ball x r, y ∈ O := by
    exact mem_closure_iff.mp (frontier_subset_closure hxO) (Metric.ball x r)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hnotBothI : ¬ (A ⊆ I ∧ C ⊆ I) := by
    rintro ⟨ha,hc⟩
    obtain ⟨y,hy,hyo⟩ := hexO
    have hn := (hmem y hy).mp (Or.inr hyo)
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · exact Set.disjoint_left.mp hd (hc ⟨hy,hneg⟩) hyo
    · exact Set.disjoint_left.mp hd (ha ⟨hy,hpos⟩) hyo
  have hnotBothO : ¬ (A ⊆ O ∧ C ⊆ O) := by
    rintro ⟨ha,hc⟩
    obtain ⟨y,hy,hyi⟩ := hexI
    have hn := (hmem y hy).mp (Or.inl hyi)
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · exact Set.disjoint_left.mp hd hyi (hc ⟨hy,hneg⟩)
    · exact Set.disjoint_left.mp hd hyi (ha ⟨hy,hpos⟩)
  rcases hAc.subset_or_subset hI hO hd hAsub with ha | ha
  · have hc : C ⊆ O := (hCc.subset_or_subset hI hO hd hCsub).resolve_left
      (fun hi => hnotBothI ⟨ha,hi⟩)
    left
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    constructor
    · intro hi
      have hn := (hmem y hy).mp (Or.inl hi)
      rcases lt_or_gt_of_ne hn with hneg | hpos
      · exact (Set.disjoint_left.mp hd hi (hc ⟨hy,hneg⟩)).elim
      · exact hpos
    · intro hypos
      exact ha ⟨hy,hypos⟩
  · have hc : C ⊆ I := (hCc.subset_or_subset hI hO hd hCsub).resolve_right
      (fun ho => hnotBothO ⟨ha,ho⟩)
    right
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    constructor
    · intro hi
      have hn := (hmem y hy).mp (Or.inl hi)
      rcases lt_or_gt_of_ne hn with hneg | hpos
      · exact hneg
      · exact (Set.disjoint_left.mp hd hi (ha ⟨hy,hpos⟩)).elim
    · intro hyneg
      exact hc ⟨hy,hyneg⟩


end LowDimensionalTopology.Geometry.Polygon
