module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedLengthSpectrumLowerBound
public import LowDimensionalTopology.Unproved.Surfaces.WeightedIntersectionClosureSmallValues

/-!
# Separation of marked lengths from the nonzero intersection closure

A fixed original marked length spectrum has one positive bound on all its
essential simple free-class coordinates. The explicit small-coordinate input
for the nonzero weighted intersection closure therefore separates the entire
marked length image from that closure. The same conclusion holds for its
literal native Fricke parametrization.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)

/-- The whole original marked length image is disjoint from the nonzero
weighted intersection closure under its explicit small-coordinate input. -/
theorem markedLengthSpectrum_disjoint_nonzeroWeightedIntersectionClosure
    (hGeom : Unproved.Surfaces.ClosedCurveIntersectionGeometry R hg hgenus)
    (hsmall : LowDimensionalTopology.Unproved.Surfaces.WeightedIntersectionClosureSmallValues
      R hg hgenus hGeom) :
    Disjoint
      (Set.range (fun t : TeichmullerSpace.{0, 0} R =>
        positiveSpectrumToNonnegative (markedLengthSpectrum R hg hgenus t)))
      (nonzeroWeightedIntersectionSpectrumClosure R hg hgenus hGeom) := by
  refine Set.disjoint_left.mpr ?_
  rintro f ⟨t, rfl⟩ hf
  obtain ⟨ε, hε, hlower⟩ := markedLengthSpectrum_uniformly_pos R hg hgenus t
  obtain ⟨a, ha⟩ := hsmall _ hf ε hε
  have ha' : (markedLengthSpectrum R hg hgenus t a : ℝ) < ε := ha
  exact (not_lt_of_ge (hlower a)) ha'

/-- The same complete marked spectra on the entire literal native Fricke
image are disjoint from the same nonzero weighted intersection closure.
The original model and separation inputs are retained. -/
theorem frickeMarkedLengthSpectrum_disjoint_nonzeroWeightedIntersectionClosure
    {e : X ≃ₜ PolygonQuotient g}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R
      (Nat.lt_of_succ_le hg) e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (hGeom : Unproved.Surfaces.ClosedCurveIntersectionGeometry R hg hgenus)
    (hsmall : LowDimensionalTopology.Unproved.Surfaces.WeightedIntersectionClosureSmallValues
      R hg hgenus hGeom) :
    Disjoint
      (Set.range (fun t : nativeFrickeImage hA =>
        positiveSpectrumToNonnegative
          (frickeMarkedLengthSpectrum R hg hgenus hA hAlt t)))
      (nonzeroWeightedIntersectionSpectrumClosure R hg hgenus hGeom) := by
  refine Set.disjoint_left.mpr ?_
  rintro f ⟨t, rfl⟩ hf
  let := nativeFrickeTopology hA
  apply Set.disjoint_left.mp
    (markedLengthSpectrum_disjoint_nonzeroWeightedIntersectionClosure
      R hg hgenus hGeom hsmall) ?_ hf
  exact ⟨(nativeFrickeHomeomorph hA hAlt).symm t, rfl⟩

end LowDimensionalTopology.Geometry.Teichmuller
