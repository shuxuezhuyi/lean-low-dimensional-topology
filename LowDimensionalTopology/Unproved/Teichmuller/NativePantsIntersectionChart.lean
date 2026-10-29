module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.GeodesicDecomposingSystem
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed
public import LowDimensionalTopology.Geometry.Teichmuller.MarkedLengthSpectrum
public import LowDimensionalTopology.Unproved.Surfaces.WeightedIntersectionClosureSmallValues
public import Mathlib.Topology.Homeomorph.Defs

/-!
# An unproved pants intersection-spectrum chart

The given original circle images form a distinct indexed maximal family of
disjoint simple closed geodesics. The proposed chart has the whole original
marked length image as its domain and the positive-pants-coordinate part of
the nonzero weighted intersection closure as its codomain, both with their
inherited spectrum topologies.

One homeomorphism must simultaneously preserve every pants coordinate and
satisfy the uniform additive inequalities on every thick part for every
original essential simple free class. The same homeomorphism is fixed before
the thickness, free-class and error-constant quantifiers. This construction
is unproved.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller Geometry.Surfaces.HandlePresentation

/-- The prescribed original pants system admits one intersection-spectrum
homeomorphism preserving all pants lengths and satisfying the uniform
additive estimate for every original curve class on each positive thick part.
The homeomorphism and its simultaneous two properties are unproved. -/
def NativePantsIntersectionChart
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) {g : ℕ}
    (hg : 2 ≤ g) (hgenus : R.HasGenus g) {e : X ≃ₜ PolygonQuotient g}
    (hA : CanonicalNormalizedModelsAvailable R (Nat.lt_of_succ_le hg) e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (hGeom : LowDimensionalTopology.Unproved.Surfaces.ClosedCurveIntersectionGeometry
      R hg hgenus) : Prop :=
  ∀ L : Fin (3 * g - 3) → EssentialSimpleCircle X,
    Function.Injective (fun j => Set.range (L j).val) →
    IsGeodesicDecomposingSystem (R := R) (R.hyperbolicOfGenusGeTwo hg hgenus).model
      (Set.range (fun j => Set.range (L j).val)) →
    let D : Set (NonnegativeSpectrum X) :=
      Set.range (fun t : nativeFrickeImage hA =>
        positiveSpectrumToNonnegative
          (frickeMarkedLengthSpectrum R hg hgenus hA hAlt t))
    let U : Set (NonnegativeSpectrum X) :=
      {f | f ∈ nonzeroWeightedIntersectionSpectrumClosure R hg hgenus hGeom ∧
        ∀ j : Fin (3 * g - 3), 0 < (f (L j).freeClass : ℝ)}
    ∃ q : ↥D ≃ₜ ↥U,
      (∀ (x : ↥D) (j : Fin (3 * g - 3)),
        ((q x).val (L j).freeClass : ℝ) = (x.val (L j).freeClass : ℝ)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ α : EssentialSimpleFreeClass X,
        ∃ c : ℝ, ∀ x : ↥D,
          (∀ j : Fin (3 * g - 3), ε < (x.val (L j).freeClass : ℝ)) →
          ((q x).val α : ℝ) ≤ (x.val α : ℝ) ∧
            (x.val α : ℝ) ≤ ((q x).val α : ℝ) + c

end LowDimensionalTopology.Unproved.Teichmuller
