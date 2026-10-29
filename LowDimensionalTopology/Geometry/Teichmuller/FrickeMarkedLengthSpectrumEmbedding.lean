module

public import LowDimensionalTopology.Geometry.Teichmuller.FrickeMarkedLengthSpectrumContinuity
public import LowDimensionalTopology.Unproved.Teichmuller.NativeFiniteLengthEmbedding

/-! Properness and embedding of the complete positive marked length spectrum
from finitely many of its actual source-class evaluations. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R
  (Nat.lt_of_succ_le hg) e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))

/-- The unchanged full positive marked spectrum is a proper embedding,
conditional on the earlier finite actual-length embedding input. -/
theorem frickeMarkedLengthSpectrum_properEmbedding_of_nativeFiniteLengthEmbedding
    (hFinite : Unproved.Teichmuller.NativeFiniteLengthEmbedding R hg hgenus hA hAlt) :
    Topology.IsEmbedding (frickeMarkedLengthSpectrum R hg hgenus hA hAlt) ∧
      IsProperMap (frickeMarkedLengthSpectrum R hg hgenus hA hAlt) := by
  obtain ⟨C, hEmbedding, hProper⟩ := hFinite
  exact frickeMarkedLengthSpectrum_properEmbedding_of_finiteEvaluation
    R (Nat.lt_of_succ_le hg) hgenus hA hAlt C hEmbedding hProper

end LowDimensionalTopology.Geometry.Teichmuller
