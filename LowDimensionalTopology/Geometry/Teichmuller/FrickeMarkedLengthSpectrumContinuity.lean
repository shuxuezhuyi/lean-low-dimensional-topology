module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedLengthSpectrum
public import LowDimensionalTopology.Geometry.Teichmuller.FrickeGeodesicLengthAnalytic
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Continuity and finite-coordinate transfer for the full actual spectrum

Ambient analytic germs imply continuity on the literal Fricke subspace without
assuming it is open. A proper embedding given by finitely many coordinates of
the same spectrum then makes the whole spectrum a proper embedding.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Filter Set Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))

/-- Each essential original length is continuous in the actual Fricke subspace topology. -/
theorem frickeGeodesicLength_continuous
    (α : LiZhongQC.Loop X) (hα : ¬ IsNullHomotopicLoop α) :
    Continuous (frickeGeodesicLength R hg hgenus hA hAlt α) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  obtain ⟨F, hF, W, hW, hEq⟩ :=
    frickeGeodesicLength_exists_analytic_germ R hg hgenus hA hAlt α hα v
  have hF' : ContinuousAt (fun t : nativeFrickeImage hA => F t) v :=
    hF.continuousAt.comp continuousAt_subtype_val
  apply hF'.congr
  have hW' : ∀ᶠ t : nativeFrickeImage hA in 𝓝 v,
      (t : Fin (6 * g - 6) → ℝ) ∈ W :=
    continuousAt_subtype_val.preimage_mem_nhds hW
  filter_upwards [hW'] with t ht
  exact hEq t ht

/-- A source class representative gives exactly the same real length as the accepted germ. -/
theorem frickeMarkedLengthSpectrum_apply
    (c : EssentialSimpleCircle X) (v : nativeFrickeImage hA) :
    (frickeMarkedLengthSpectrum R (Nat.succ_le_of_lt hg) hgenus hA hAlt v c.freeClass : ℝ) =
      frickeGeodesicLength R hg hgenus hA hAlt (circleRepresentativeLoop c.1) v := rfl

/-- The whole positive spectrum is continuous for its literal product topology. -/
theorem frickeMarkedLengthSpectrum_continuous :
    Continuous (frickeMarkedLengthSpectrum R (Nat.succ_le_of_lt hg) hgenus hA hAlt) := by
  apply continuous_pi
  intro a
  induction a using Quotient.inductionOn with
  | h c =>
      apply continuous_induced_rng.mpr
      change Continuous
        (frickeGeodesicLength R hg hgenus hA hAlt (circleRepresentativeLoop c.1))
      exact frickeGeodesicLength_continuous R hg hgenus hA hAlt
        (circleRepresentativeLoop c.1) (essentialSimpleCircle_loop_not_null c)

/-- A proper embedding given by actual finite source-class evaluations implies
the same property for the unchanged full positive spectrum. -/
theorem frickeMarkedLengthSpectrum_properEmbedding_of_finiteEvaluation
    (C : Fin (9 * g - 9) → EssentialSimpleFreeClass X)
    (hEmbedding : IsEmbedding
      (fun t : nativeFrickeImage hA => fun i =>
        frickeMarkedLengthSpectrum R (Nat.succ_le_of_lt hg) hgenus hA hAlt t (C i)))
    (hProper : IsProperMap
      (fun t : nativeFrickeImage hA => fun i =>
        frickeMarkedLengthSpectrum R (Nat.succ_le_of_lt hg) hgenus hA hAlt t (C i))) :
    IsEmbedding (frickeMarkedLengthSpectrum R (Nat.succ_le_of_lt hg) hgenus hA hAlt) ∧
      IsProperMap (frickeMarkedLengthSpectrum R (Nat.succ_le_of_lt hg) hgenus hA hAlt) := by
  let p : PositiveSpectrum X → (Fin (9 * g - 9) → Set.Ioi (0 : ℝ)) :=
    fun s i => s (C i)
  have hp : Continuous p :=
    continuous_pi (fun i => continuous_apply (C i))
  have hL := frickeMarkedLengthSpectrum_continuous R hg hgenus hA hAlt
  exact ⟨IsEmbedding.of_comp hL hp hEmbedding,
    isProperMap_of_comp_of_t2 hL hp hProper⟩

end LowDimensionalTopology.Geometry.Teichmuller
