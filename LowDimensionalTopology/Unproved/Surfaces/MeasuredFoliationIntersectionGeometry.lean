module

public import LowDimensionalTopology.Geometry.Surfaces.MeasuredFoliationIntersectionCosts
public import LowDimensionalTopology.Geometry.Surfaces.IntersectionSpectra

/-!
# Concrete geometric input for original measured-foliation intersection spectra

The six clauses concern the actual costs, actual elementary moves and independent
weighted curve spectra. This proposition supplies no proof of those clauses.
The independent hypothesis for geometric curve intersection counts stays explicit.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped ENNReal

namespace LowDimensionalTopology.Unproved.Surfaces

open Geometry.Surfaces

/-- Finite adapted representatives, endpoint regularization, geometric move
invariance, nonvanishing, separation and the independent weighted-curve closure
range for the same original surface and all its original curve classes. -/
def OriginalMeasuredFoliationIntersectionGeometry
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) {g : ℕ}
    (hg : 2 ≤ g) (hgenus : R.HasGenus g)
    (hCurve : ClosedCurveIntersectionGeometry R hg hgenus) : Prop :=
  (∀ F : nondegenerateMeasuredFoliation R, ∀ β : EssentialSimpleFreeClass X,
    ∃ L : EssentialSimpleCircle X, ∃ m : ℝ≥0∞,
      L.freeClass = β ∧ m ∈ measuredFoliationRegularCosts F L ∧ m < ∞) ∧
  (∀ F : nondegenerateMeasuredFoliation R, ∀ L : EssentialSimpleCircle X,
    ∀ m ∈ measuredFoliationGeneralCosts F L, ∀ ε : ℝ, 0 < ε →
      ∃ L' : EssentialSimpleCircle X, ∃ m' ∈ measuredFoliationRegularCosts F L',
        L'.freeClass = L.freeClass ∧ m' ≤ m + ENNReal.ofReal ε) ∧
  (∀ F G : nondegenerateMeasuredFoliation R,
    measuredFoliationElementaryStep F G → ∀ β : EssentialSimpleFreeClass X,
      measuredFoliationRegularIntersection F β = measuredFoliationRegularIntersection G β) ∧
  (∀ F : nondegenerateMeasuredFoliation R, ∃ β : EssentialSimpleFreeClass X,
    0 < measuredFoliationRegularIntersection F β) ∧
  (∀ F G : nondegenerateMeasuredFoliation R,
    (∀ β : EssentialSimpleFreeClass X,
      measuredFoliationRegularIntersection F β = measuredFoliationRegularIntersection G β) →
        Relation.EqvGen measuredFoliationElementaryStep F G) ∧
  (∀ f : NonnegativeSpectrum X,
    (f ≠ 0 ∧ f ∈ closure (Set.range (fun w : Set.Ioi (0 : ℝ) × EssentialSimpleFreeClass X =>
      (weightedIntersectionSpectrum R hg hgenus hCurve w).val))) ↔
        ∃ F : nondegenerateMeasuredFoliation R, ∀ β : EssentialSimpleFreeClass X,
          (f β : ℝ≥0∞) = measuredFoliationRegularIntersection F β)

end LowDimensionalTopology.Unproved.Surfaces
