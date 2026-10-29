module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeFrickeParameterMap
public import LowDimensionalTopology.Geometry.Teichmuller.NativeFrickeCoordinateContinuityProof

/-! Continuity of the original L1 quadratic parameter map in its actual
finite Fricke coordinates and their Euclidean image topology. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Topology Surfaces Surfaces.HandlePresentation
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}

/-- The same entire original L1 parameter map is continuous into the actual
native Fricke image and into its ambient finite Euclidean coordinates. -/
theorem nativeFrickeParameterMap_continuous
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e) :
    let mQ : MetricSpace ↥(QuadraticL1.openUnitBall R) := QuadraticL1.unitBallMetricSpace R
    let : TopologicalSpace ↥(QuadraticL1.openUnitBall R) :=
      mQ.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Continuous (nativeFrickeParameterMap R hg hgenus hA) ∧
      Continuous (fun φ : ↥(QuadraticL1.openUnitBall R) =>
        (nativeFrickeParameterMap R hg hgenus hA φ : Fin (6 * g - 6) → ℝ)) := by
  let mQ : MetricSpace ↥(QuadraticL1.openUnitBall R) := QuadraticL1.unitBallMetricSpace R
  let : TopologicalSpace ↥(QuadraticL1.openUnitBall R) :=
    mQ.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let mT : MetricSpace (TeichmullerSpace.{0, 0} R) :=
    TeichmullerSpace.qcMetricSpace R hg hgenus
  let : TopologicalSpace (TeichmullerSpace.{0, 0} R) :=
    mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hc : Continuous (finiteFrickeCoordinates hA) :=
    nativeFrickeCoordinateContinuity R hg hgenus e hA
  have hp : Continuous (TeichmullerSpace.l1ParameterMap R hg hgenus) :=
    (TeichmullerSpace.l1ParameterMap_topology R hg hgenus).1.continuous
  have hf : Continuous (fun φ : ↥(QuadraticL1.openUnitBall R) =>
      (nativeFrickeParameterMap R hg hgenus hA φ : Fin (6 * g - 6) → ℝ)) := by
    change Continuous (finiteFrickeCoordinates hA ∘
      TeichmullerSpace.l1ParameterMap R hg hgenus)
    exact hc.comp hp
  exact ⟨IsEmbedding.subtypeVal.continuous_iff.mpr hf, hf⟩

end LowDimensionalTopology.Geometry.Teichmuller
