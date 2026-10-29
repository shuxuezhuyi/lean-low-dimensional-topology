module

public import LowDimensionalTopology.Geometry.Surfaces.IntersectionSpectra

/-!
# The original projective intersection boundary

Take the closure of all actual simple-curve intersection profiles in the
projective nonnegative spectrum space, with its original quotient topology.
Every positive weighting of one curve supplies a point of this closure.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) {g : ℕ}
    (hg : 2 ≤ g) (hgenus : R.HasGenus g)
    (hGeom : Unproved.Surfaces.ClosedCurveIntersectionGeometry R hg hgenus)

/-- The closure of the original projective simple-curve intersection profiles. -/
def originalThurstonBoundary : Set (ProjectiveNonnegativeSpectrum X) :=
  closure (Set.range (projectiveIntersectionSpectrum R hg hgenus hGeom))

/-- Every positive weighted original curve profile lies in the same boundary set. -/
theorem projectivize_weightedIntersectionSpectrum_mem_originalThurstonBoundary
    (w : Set.Ioi (0 : ℝ)) (a : EssentialSimpleFreeClass X) :
    projectivizeNonnegativeSpectrum
      (weightedIntersectionSpectrum R hg hgenus hGeom (w, a)) ∈
        originalThurstonBoundary R hg hgenus hGeom := by
  rw [projectivize_weightedIntersectionSpectrum]
  exact subset_closure (Set.mem_range_self a)

end LowDimensionalTopology.Geometry.Surfaces
