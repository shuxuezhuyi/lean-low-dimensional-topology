module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedLengthSpectrum
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# A finite family of actual native spectrum evaluations

This independent geometric obligation supplies a finite proper embedding by
the original marked lengths. Importing the proposition supplies no proof.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller Geometry.Surfaces.HandlePresentation

/-- Some original finite family of essential simple free classes gives a proper
embedding by evaluation of the actual positive marked spectrum on the entire
literal native Fricke image. -/
def NativeFiniteLengthEmbedding
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) {g : ℕ}
    (hg : 2 ≤ g) (hgenus : R.HasGenus g) {e : X ≃ₜ PolygonQuotient g}
    (hA : CanonicalNormalizedModelsAvailable R (Nat.lt_of_succ_le hg) e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m)) : Prop :=
  ∃ classes : Fin (9 * g - 9) → EssentialSimpleFreeClass X,
    let f : nativeFrickeImage hA → (Fin (9 * g - 9) → Set.Ioi (0 : ℝ)) :=
      fun t i => frickeMarkedLengthSpectrum R hg hgenus hA hAlt t (classes i)
    Topology.IsEmbedding f ∧ IsProperMap f

end LowDimensionalTopology.Unproved.Teichmuller
