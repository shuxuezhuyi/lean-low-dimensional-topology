module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Closed
public import LowDimensionalTopology.Geometry.Surfaces.Topology.SmoothDiskDeletion
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Finite conformal deletion with retained boundary circles

The carrier removes finitely many points and actual open smooth disks from
a fixed closed Riemann surface. The open interior inherits the given complex
atlas. The same disk circles form the retained carrier outside this interior.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X]

/-- The image of the closed coordinate disk is the closure of the open image. -/
theorem SmoothDiskNeighborhood.closedDisk_eq_closure_openDisk
    (R : ClosedRiemannSurface X) (d : SmoothDiskNeighborhood R.toRiemannSurface) :
    d.closedDisk = closure d.openDisk := by
  let := R.t2Space
  have hclosure : closure (Metric.ball (0 : ℂ) 1) = Metric.closedBall (0 : ℂ) 1 :=
    closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0)
  have hcompact : IsCompact (closure (Metric.ball (0 : ℂ) 1)) := by
    rw [hclosure]
    exact isCompact_closedBall (0 : ℂ) 1
  have hcontinuous : ContinuousOn d.chart (closure (Metric.ball (0 : ℂ) 1)) := by
    rw [hclosure]
    exact d.chart.continuousOn.mono d.closedBall_subset_source
  change d.chart '' Metric.closedBall (0 : ℂ) 1 =
    closure (d.chart '' Metric.ball (0 : ℂ) 1)
  rw [← hclosure]
  exact image_closure_of_isCompact hcompact hcontinuous

/-- Finite punctures and smooth disks with disjoint closures in a fixed closed
surface. The closure conditions refer to the actual open disk images. -/
structure FiniteRetainedBoundaryData (R : ClosedRiemannSurface X) where
  punctures : Finset X
  circleCount : ℕ
  disks : Fin circleCount → SmoothDiskNeighborhood R.toRiemannSurface
  disjoint_closures : Pairwise fun i j =>
    Disjoint (closure (disks i).openDisk) (closure (disks j).openDisk)
  punctures_disjoint_closures : ∀ i,
    Disjoint (punctures : Set X) (closure (disks i).openDisk)

namespace FiniteRetainedBoundaryData

variable {R : ClosedRiemannSurface X}

/-- The literal deletion subtype, with its inherited subspace topology. -/
abbrev Carrier (D : FiniteRetainedBoundaryData R) : Type :=
  FiniteDiskDeletionCarrier R.toRiemannSurface D.punctures D.disks

/-- The complement of the punctures and all disk closures in the original surface. -/
def interiorOpen (D : FiniteRetainedBoundaryData R) : TopologicalSpace.Opens X := by
  let := R.t2Space
  exact ⟨((D.punctures : Set X) ∪ ⋃ i, closure (D.disks i).openDisk)ᶜ,
    (D.punctures.finite_toSet.isClosed.union
      (isClosed_iUnion_of_finite fun i => isClosed_closure)).isOpen_compl⟩

/-- The actual interior point, viewed in the same retained deletion carrier. -/
def interiorToCarrier (D : FiniteRetainedBoundaryData R)
    (x : D.interiorOpen) : D.Carrier := by
  have hx : (x : X) ∉
      ((D.punctures : Set X) ∪ ⋃ i, closure (D.disks i).openDisk) := x.property
  refine ⟨x.val, ?_, ?_⟩
  · intro hp
    exact hx (Or.inl hp)
  · intro i hi
    exact hx (Or.inr (mem_iUnion.mpr ⟨i, subset_closure hi⟩))

/-- The complex atlas is inherited from the original open submanifold. -/
def interiorAtlas (D : FiniteRetainedBoundaryData R) :
    RiemannAtlas D.interiorOpen := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  exact RiemannAtlas.ofManifold D.interiorOpen

/-- The original open-subtype inclusion is complex analytic in its inherited charts. -/
theorem interior_inclusion_contMDiff (D : FiniteRetainedBoundaryData R) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val : D.interiorOpen → X) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  exact contMDiff_subtype_val

/-- Every point of each actual coordinate circle remains in the deletion carrier. -/
theorem boundary_retention (D : FiniteRetainedBoundaryData R) (i : Fin D.circleCount)
    {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) 1) :
    ∃ p : D.Carrier, (p : X) = (D.disks i).chart z := by
  have hd : Pairwise fun i j => Disjoint (D.disks i).closedDisk (D.disks j).closedDisk := by
    intro i j hij
    simpa only [SmoothDiskNeighborhood.closedDisk_eq_closure_openDisk R] using
      D.disjoint_closures hij
  have hp : ∀ i, Disjoint (D.punctures : Set X) (D.disks i).closedDisk := by
    intro i
    rw [SmoothDiskNeighborhood.closedDisk_eq_closure_openDisk R]
    exact D.punctures_disjoint_closures i
  exact sphere_image_retained_in_finiteDiskDeletionCarrier
    D.punctures D.disks hd hp i hz

/-- The retained carrier outside the given open interior is exactly the same
finite collection of coordinate circle images. -/
theorem not_mem_interior_iff_boundary (D : FiniteRetainedBoundaryData R) (p : D.Carrier) :
    ((p : X) ∉ D.interiorOpen) ↔
      ∃ i : Fin D.circleCount, ∃ z ∈ Metric.sphere (0 : ℂ) 1,
        (D.disks i).chart z = (p : X) := by
  classical
  constructor
  · intro h
    have hmem : (p : X) ∈
        ((D.punctures : Set X) ∪ ⋃ i, closure (D.disks i).openDisk) := by
      by_contra hn
      exact h hn
    rcases hmem with hp | hd
    · exact False.elim (p.property.1 hp)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hd
      rw [← SmoothDiskNeighborhood.closedDisk_eq_closure_openDisk R] at hi
      obtain ⟨z, hz, heq⟩ := hi
      have hznot : z ∉ Metric.ball (0 : ℂ) 1 := by
        intro hb
        exact p.property.2 i ⟨z, hb, heq⟩
      have hle : dist z (0 : ℂ) ≤ 1 := Metric.mem_closedBall.mp hz
      have hnlt : ¬ dist z (0 : ℂ) < 1 := fun hlt => hznot (Metric.mem_ball.mpr hlt)
      have hsphere : z ∈ Metric.sphere (0 : ℂ) 1 :=
        Metric.mem_sphere.mpr (le_antisymm hle (not_lt.mp hnlt))
      exact ⟨i, z, hsphere, heq⟩
  · rintro ⟨i, z, hz, heq⟩ hinside
    have hi : (p : X) ∈ closure (D.disks i).openDisk := by
      rw [← SmoothDiskNeighborhood.closedDisk_eq_closure_openDisk R]
      exact ⟨z, Metric.sphere_subset_closedBall hz, heq⟩
    have hx : (p : X) ∉
        ((D.punctures : Set X) ∪ ⋃ i, closure (D.disks i).openDisk) := hinside
    exact hx (Or.inr (mem_iUnion.mpr ⟨i, hi⟩))

end FiniteRetainedBoundaryData
end LowDimensionalTopology.Geometry.Surfaces
