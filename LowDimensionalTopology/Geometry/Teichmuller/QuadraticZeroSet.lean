module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticNaturalCoordinate
public import Mathlib.Topology.DiscreteSubset

/-!
# The actual zero set of a nonzero quadratic differential

The existing isolated-zero charts give local isolation on the original surface.
The zero set is closed and discrete, hence finite by original compactness.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

variable {X : Type} [TopologicalSpace X]

/-- The actual zeros of the given differential, in the original preferred charts. -/
def quadraticZeroSet (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) : Set X :=
  letI := R.toRiemannAtlas.toChartedSpace
  {p | ¬ LiZhongQC.IsRegularPoint (q : X → ℂ → ℂ) p}

variable (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)

private theorem exists_open_quadraticZeroSet_subset_singleton (hq : q ≠ 0) (p : X) :
    ∃ U : Set X, IsOpen U ∧ p ∈ U ∧ U ∩ quadraticZeroSet R q ⊆ {p} := by
  let := R.toRiemannAtlas.toChartedSpace
  let D := chooseQuadraticNaturalCoordinateData R q hq p
  refine ⟨(chartAt ℂ p).source ∩ (chartAt ℂ p) ⁻¹' D.ordinaryChart.source,
    (chartAt ℂ p).isOpen_inter_preimage D.ordinaryChart.open_source,
    ⟨mem_chart_source ℂ p, D.normal.center⟩, ?_⟩
  rintro y ⟨hy, hyzero⟩
  change ¬ LiZhongQC.IsRegularPoint (q : X → ℂ → ℂ) y at hyzero
  have hcoord : chartAt ℂ p y = chartAt ℂ p p := by
    by_contra hne
    have hcoeff := D.normal.ne_zero (chartAt ℂ p y) hy.2 hne
    have hregular : LiZhongQC.IsRegularPoint (q : X → ℂ → ℂ) y := by
      simpa only [(chartAt ℂ p).left_inv hy.1] using
        (LiZhongQC.s26d_a_isRegularPoint_iff q.property p
          ((chartAt ℂ p).map_source hy.1)).mpr hcoeff
    exact hyzero hregular
  exact Set.mem_singleton_iff.mpr
    ((chartAt ℂ p).injOn hy.1 (mem_chart_source ℂ p) hcoord)

/-- The actual zero set is closed in the original surface. -/
theorem isClosed_quadraticZeroSet (hq : q ≠ 0) : IsClosed (quadraticZeroSet R q) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨U, hU, hpU, hsub⟩ := exists_open_quadraticZeroSet_subset_singleton R q hq p
  refine Filter.mem_of_superset (hU.mem_nhds hpU) ?_
  intro y hy hyzero
  have heq : y = p := Set.mem_singleton_iff.mp (hsub ⟨hy, hyzero⟩)
  exact hp (heq ▸ hyzero)

/-- Every actual zero is isolated in the original surface. -/
theorem isDiscrete_quadraticZeroSet (hq : q ≠ 0) : IsDiscrete (quadraticZeroSet R q) := by
  refine isDiscrete_iff_forall_mem_exists_isOpen.mpr ?_
  intro p hp
  obtain ⟨U, hU, hpU, hsub⟩ := exists_open_quadraticZeroSet_subset_singleton R q hq p
  refine ⟨U, hU, Set.Subset.antisymm hsub ?_⟩
  intro y hy
  rcases Set.mem_singleton_iff.mp hy with rfl
  exact ⟨hpU, hp⟩

/-- A nonzero native holomorphic quadratic differential has finitely many actual zeros. -/
theorem quadraticZeroSet_finite (hq : q ≠ 0) : (quadraticZeroSet R q).Finite := by
  let := R.compactSpace
  exact (isClosed_quadraticZeroSet R q hq).isCompact.finite
    (isDiscrete_quadraticZeroSet R q hq)

end LowDimensionalTopology.Geometry.Teichmuller
