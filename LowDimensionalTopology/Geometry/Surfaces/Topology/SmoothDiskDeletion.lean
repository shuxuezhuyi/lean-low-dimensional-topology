module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Disjoint

/-!
# Smooth disks and deletion with retained circles

A disk is specified by a real smooth coordinate neighborhood of its entire
closed unit disk. The finite deletion carrier removes disk interiors and
ordinary punctures. Its designated circle points remain in the same subtype.
No manifold-with-boundary structure or geometric decomposition is asserted.
-/

@[expose] public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Surfaces

universe u

variable {K : Type u} [TopologicalSpace K]

/-- A genuine smooth disk neighborhood in the original real smooth structure.
Neither direction is required to be complex analytic. -/
structure SmoothDiskNeighborhood (R : RiemannSurface K) where
  chart : OpenPartialHomeomorph ℂ K
  closedBall_subset_source : Metric.closedBall (0 : ℂ) 1 ⊆ chart.source
  contMDiffOn_forward :
    letI := R.toRiemannAtlas.toChartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ chart chart.source
  contMDiffOn_inverse :
    letI := R.toRiemannAtlas.toChartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ chart.symm chart.target

variable {R : RiemannSurface K}

/-- The open disk removed from the original carrier. -/
def SmoothDiskNeighborhood.openDisk (d : SmoothDiskNeighborhood R) : Set K :=
  d.chart '' Metric.ball (0 : ℂ) 1

/-- The closed disk used for disjointness and exclusion of ordinary punctures. -/
def SmoothDiskNeighborhood.closedDisk (d : SmoothDiskNeighborhood R) : Set K :=
  d.chart '' Metric.closedBall (0 : ℂ) 1

/-- The original subspace with finitely many points and open disk interiors
removed. Its topology is the subtype topology; no boundaryless atlas is supplied. -/
abbrev FiniteDiskDeletionCarrier (R : RiemannSurface K) (P : Finset K)
    {b : ℕ} (d : Fin b → SmoothDiskNeighborhood R) : Type u :=
  {x : K // x ∉ (P : Set K) ∧ ∀ i, x ∉ (d i).openDisk}

/-- Pairwise disjoint closed disks and punctures outside every closed disk
retain every actual unit-circle image as a point of the same deletion carrier. -/
theorem sphere_image_retained_in_finiteDiskDeletionCarrier
    (P : Finset K) {b : ℕ} (d : Fin b → SmoothDiskNeighborhood R)
    (hdisjoint : Pairwise fun i j => Disjoint (d i).closedDisk (d j).closedDisk)
    (hpunctures : ∀ i, Disjoint (P : Set K) (d i).closedDisk)
    (i : Fin b) {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) 1) :
    ∃ p : FiniteDiskDeletionCarrier R P d, (p : K) = (d i).chart z := by
  have hzClosed : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.sphere_subset_closedBall hz
  have hzSource : z ∈ (d i).chart.source := (d i).closedBall_subset_source hzClosed
  have hzImage : (d i).chart z ∈ (d i).closedDisk := ⟨z, hzClosed, rfl⟩
  have hzNotBall : z ∉ Metric.ball (0 : ℂ) 1 :=
    (Set.disjoint_left.mp Metric.sphere_disjoint_ball) hz
  refine ⟨⟨(d i).chart z, ?_⟩, rfl⟩
  refine ⟨(Set.disjoint_right.mp (hpunctures i)) hzImage, ?_⟩
  intro j hj
  rcases hj with ⟨w, hw, heq⟩
  by_cases hji : j = i
  · subst j
    have hwSource : w ∈ (d i).chart.source :=
      (d i).closedBall_subset_source (Metric.ball_subset_closedBall hw)
    have hwz : w = z := (d i).chart.injOn hwSource hzSource heq
    exact hzNotBall (hwz ▸ hw)
  · have hwImage : (d j).chart w ∈ (d j).closedDisk :=
      ⟨w, Metric.ball_subset_closedBall hw, rfl⟩
    have hxj : (d i).chart z ∈ (d j).closedDisk := heq ▸ hwImage
    have hClosedDisjoint : Disjoint (d i).closedDisk (d j).closedDisk :=
      hdisjoint (Ne.symm hji)
    exact (Set.disjoint_left.mp hClosedDisjoint) hzImage hxj

end LowDimensionalTopology.Geometry.Surfaces
