module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedLengthSpectrum
public import LowDimensionalTopology.Geometry.Surfaces.ProjectiveSpectra

/-!
# The unproved projective marked-length embedding theorem

This module names the exact projective embedding conclusion on the existing
original classes and literal native Fricke image. It supplies no proof of
the proposition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller Geometry.Surfaces.HandlePresentation

/-- The unchanged full positive marked spectrum remains an embedding after
quotienting by one common positive scale. This proposition is unproved;
no finite collection of lengths replaces its target. -/
def NativeProjectiveMarkedLengthEmbedding
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) {g : ℕ}
    (hg : 2 ≤ g) (hgenus : R.HasGenus g) {e : X ≃ₜ PolygonQuotient g}
    (hA : CanonicalNormalizedModelsAvailable R (Nat.lt_of_succ_le hg) e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m)) : Prop :=
  Topology.IsEmbedding
    (fun t : nativeFrickeImage hA =>
      projectivizePositiveSpectrum (frickeMarkedLengthSpectrum R hg hgenus hA hAlt t))

end LowDimensionalTopology.Unproved.Teichmuller
