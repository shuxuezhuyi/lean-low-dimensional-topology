/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.SourceGenus
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGroupPresentationPositive
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LowDimensionalTopology.Geometry.Surfaces

universe u
variable {X : Type u} [TopologicalSpace X]

/-- The actual canonical handle presentation holds in every genus, including the sphere. -/
theorem canonicalHandleGroupPresentation (g : ℕ) :
    LowDimensionalTopology.Unproved.HandleGroupPresentation g := by
  cases g with
  | zero => exact handleGroupPresentation_zero
  | succ n => exact handleGroupPresentation_positive (n + 1) (Nat.succ_pos n)

/-- The actual based fundamental group of the canonical closed handle model. -/
def canonicalHandleFundamentalGroupMulEquiv (g : ℕ) :
    FundamentalGroup (CanonicalHandleSurface g) (canonicalHandleBasePoint g) ≃*
      LiZhongQC.surfaceGroup g :=
  Classical.choice (canonicalHandleGroupPresentation g)

/-- The native topological handle genus implies the original surface-group genus. -/
theorem sourceHasGenus_of_handleGenus [PathConnectedSpace X] {g : ℕ}
    (hg : HasTopologicalGenus X g) : LiZhongQC.HasGenus X g :=
  sourceHasGenus_of_topologicalGenus hg (canonicalHandleGroupPresentation g)

/-- The actual original Riemann surface has the standard surface group in its handle genus. -/
def ClosedRiemannSurface.surfaceGroupMulEquiv (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : R.HasGenus g) (x : X) :
    FundamentalGroup X x ≃* LiZhongQC.surfaceGroup g :=
  R.fundamentalGroupSurfaceGroupMulEquiv hg (canonicalHandleGroupPresentation g) x

/-- A closed Riemann surface's handle genus gives its actual fundamental-group presentation. -/
theorem ClosedRiemannSurface.hasSourceGenus (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : R.HasGenus g) : LiZhongQC.HasGenus X g :=
  R.sourceHasGenus hg (canonicalHandleGroupPresentation g)

/-- The comparison between analytic and handle genus now follows from the proved canonical
presentation and the existing real period-map theorem, with no unproved mathematical input. -/
theorem ClosedRiemannSurface.genusComparison (R : ClosedRiemannSurface X) (g : ℕ) :
    LowDimensionalTopology.Unproved.Surfaces.GenusComparison R g :=
  R.genusComparison_of_handleGroupPresentation (canonicalHandleGroupPresentation g)

/-- The dimension of holomorphic one-forms equals the handle genus, using exactly the complex
atlas of the given closed Riemann surface. -/
theorem ClosedRiemannSurface.analyticGenus_eq_handleGenus (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : R.HasGenus g) :
    let := R.t2Space
    let := R.compactSpace
    let := R.connectedSpace
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    _root_.genus X = g :=
  R.genusComparison g hg

end LowDimensionalTopology.Geometry.Surfaces
