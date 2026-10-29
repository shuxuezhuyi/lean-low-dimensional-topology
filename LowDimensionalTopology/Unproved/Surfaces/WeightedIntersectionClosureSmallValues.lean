module

public import LowDimensionalTopology.Geometry.Surfaces.IntersectionSpectra

/-!
# Small coordinates in the nonzero weighted intersection closure

The closure is taken in the full nonnegative spectrum product on the original
essential simple free classes, and only the zero function is then removed.
The small-coordinate assertion is an explicit unproved geometric input.
No space of geometric measured foliations or identification with one is assumed
by the definition of this set.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

/-- The closure of all positively weighted original intersection spectra, in
the full nonnegative spectrum space, with the zero function removed. -/
def nonzeroWeightedIntersectionSpectrumClosure
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) {g : ℕ}
    (hg : 2 ≤ g) (hgenus : R.HasGenus g)
    (hGeom : Unproved.Surfaces.ClosedCurveIntersectionGeometry R hg hgenus) :
    Set (NonnegativeSpectrum X) :=
  closure (Set.range (fun p : Set.Ioi (0 : ℝ) × EssentialSimpleFreeClass X =>
    (weightedIntersectionSpectrum R hg hgenus hGeom p).val)) \ {0}

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Unproved.Surfaces

open Geometry.Surfaces

/-- Every nonzero spectrum in the weighted intersection closure has original
essential simple free-class coordinates arbitrarily close to zero.
This geometric small-coordinate assertion is unproved. -/
def WeightedIntersectionClosureSmallValues
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) {g : ℕ}
    (hg : 2 ≤ g) (hgenus : R.HasGenus g)
    (hGeom : ClosedCurveIntersectionGeometry R hg hgenus) : Prop :=
  ∀ (f : NonnegativeSpectrum X),
    f ∈ nonzeroWeightedIntersectionSpectrumClosure R hg hgenus hGeom →
      ∀ ε : ℝ, 0 < ε → ∃ a : EssentialSimpleFreeClass X, (f a : ℝ) < ε

end LowDimensionalTopology.Unproved.Surfaces
