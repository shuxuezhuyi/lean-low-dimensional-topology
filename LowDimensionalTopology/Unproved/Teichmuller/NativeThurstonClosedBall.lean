module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeFrickeMarkedSpectrumClosureAction
public import LowDimensionalTopology.Geometry.Surfaces.IntersectionSpectra
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Homeomorph.Defs

/-!
# The unproved closed-ball realization of the original spectrum closure

This module states the closed-ball conclusion without proving it. The
domain is the same full native Fricke marked-spectrum closure already used
by the original homeomorphism action. The interior is the image of the
same literal native Fricke space. The boundary is the exact projective
intersection closure, denoted `PMF`. No measured-foliation model or theorem
about such a model is introduced here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller Geometry.Surfaces.HandlePresentation

/-- The entire actual projective marked-length closure is the compact closed
`(6g-6)`-ball. Its exact original native Fricke image is the open-ball interior,
and its exact original projective intersection closure is the unit sphere.
The interior homeomorphism commutes pointwise with the original spectrum map;
no arbitrary replacement parametrization of the source is permitted.
This proposition is unproved and contains no assumed compactification result. -/
def NativeThurstonClosedBall
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) {g : ℕ}
    (hg : 2 ≤ g) (hgenus : R.HasGenus g) {e : X ≃ₜ PolygonQuotient g}
    (hA : CanonicalNormalizedModelsAvailable R (Nat.lt_of_succ_le hg) e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (hGeom : Unproved.Surfaces.ClosedCurveIntersectionGeometry R hg hgenus)
    (a₀ : EssentialSimpleFreeClass X) : Prop :=
  let f := frickeProjectiveMarkedLengthSpectrum R hg hgenus hA hAlt a₀
  let C := frickeMarkedLengthSpectrumProjectiveClosure R hg hgenus hA hAlt a₀
  let I := Set.range f
  let B := closure (Set.range (projectiveIntersectionSpectrum R hg hgenus hGeom))
  let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1
  let U := Metric.ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1
  let j : nativeFrickeImage hA → C := fun t => ⟨f t, by
    change f t ∈ closure (Set.range f)
    exact subset_closure (Set.mem_range_self t)⟩
  C = I ∪ B ∧ Disjoint I B ∧ IsCompact C ∧
    ∃ (H : C ≃ₜ D) (HInterior : nativeFrickeImage hA ≃ₜ U),
      (∀ t : nativeFrickeImage hA,
        (H (j t) : EuclideanSpace ℝ (Fin (6 * g - 6))) =
          (HInterior t : EuclideanSpace ℝ (Fin (6 * g - 6)))) ∧
      (∀ p : C, (H p : EuclideanSpace ℝ (Fin (6 * g - 6))) ∈ U ↔ p.val ∈ I) ∧
      (∀ p : C, (H p : EuclideanSpace ℝ (Fin (6 * g - 6))) ∈ S ↔ p.val ∈ B)

end LowDimensionalTopology.Unproved.Teichmuller
