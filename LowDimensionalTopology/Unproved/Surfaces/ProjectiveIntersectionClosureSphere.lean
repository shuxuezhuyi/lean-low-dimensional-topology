module

public import LowDimensionalTopology.Geometry.Surfaces.IntersectionSpectra
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Homeomorph.Defs

/-!
# The unproved sphere theorem for the original projective intersection closure

The exact projective intersection closure is asserted to be a sphere,
without a proof. The closure is taken in the existing projective
nonnegative spectrum space on the original essential simple free classes.
No measured-foliation space or replacement boundary is introduced.
-/

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Surfaces

open Geometry.Surfaces

/-- The closure of the actual original projective simple-curve intersection
spectra has the exact sphere model `S^(6g-7)` in real dimension `6g-6`.
This proposition is unproved. -/
def ProjectiveIntersectionClosureSphere
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) {g : ℕ}
    (hg : 2 ≤ g) (hgenus : R.HasGenus g)
    (hGeom : ClosedCurveIntersectionGeometry R hg hgenus) : Prop :=
  Nonempty
    (↥(closure (Set.range (projectiveIntersectionSpectrum R hg hgenus hGeom))) ≃ₜ
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1))

end LowDimensionalTopology.Unproved.Surfaces
