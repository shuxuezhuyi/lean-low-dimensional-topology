module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeFrickeOpenEmbedding
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! The actual finite Fricke image is a simply connected Euclidean domain. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}

include hgenus

/-- The actual Fricke image is an open connected, simply connected subset of
the literal finite coordinate space and is homeomorphic to that whole space. -/
theorem nativeFrickeImage_domain
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m)) :
    IsOpen (nativeFrickeImage hA) ∧ IsConnected (nativeFrickeImage hA) ∧
      IsSimplyConnected (nativeFrickeImage hA) ∧
      Nonempty (nativeFrickeImage hA ≃ₜ (Fin (6 * g - 6) → ℝ)) := by
  classical
  let mT : MetricSpace (TeichmullerSpace.{0, 0} R) :=
    TeichmullerSpace.qcMetricSpace R hg hgenus
  let : TopologicalSpace (TeichmullerSpace.{0, 0} R) :=
    mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hf := finiteFrickeCoordinates_qc_isOpenEmbedding R hg hgenus hA hAlt
  obtain ⟨E⟩ := (TeichmullerSpace.l1ParameterMap_homeomorphism R hg hgenus).2
  let H : nativeFrickeImage hA ≃ₜ (Fin (6 * g - 6) → ℝ) :=
    hf.isEmbedding.toHomeomorph.symm.trans
      (E.trans (EuclideanSpace.equiv (Fin (6 * g - 6)) ℝ).toHomeomorph)
  let : ContractibleSpace (nativeFrickeImage hA) := H.contractibleSpace
  have hs : SimplyConnectedSpace (nativeFrickeImage hA) := inferInstance
  exact ⟨hf.isOpen_range, isConnected_iff_connectedSpace.mpr inferInstance, hs, ⟨H⟩⟩

end LowDimensionalTopology.Geometry.Teichmuller
