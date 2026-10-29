module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersProjectionTopology
public import LowDimensionalTopology.Geometry.Teichmuller.NativeFrickeImageTopology
public import LowDimensionalTopology.Geometry.Teichmuller.NativeFrickeCoordinateContinuityProof
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Paths in the original Teichmuller space and the actual Fricke image

The entire measurable coefficient ball is convex. Its actual continuous
surjection supplies paths for the full native marked quotient with the QC
metric. The proved Fricke continuity then supplies paths in the
literal Euclidean image, without identifying independently defined topologies.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)

namespace TeichmullerSpace

/-- The entire original QC-metric marked quotient is path connected. -/
theorem qcMetric_pathConnected {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) :
    let mT : MetricSpace (TeichmullerSpace.{0, 0} R) := qcMetricSpace R hg hgenus
    let : TopologicalSpace (TeichmullerSpace.{0, 0} R) :=
      mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    PathConnectedSpace (TeichmullerSpace.{0, 0} R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let mT : MetricSpace (TeichmullerSpace.{0, 0} R) := qcMetricSpace R hg hgenus
  let : TopologicalSpace (TeichmullerSpace.{0, 0} R) :=
    mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  obtain ⟨Γ, p, hΓ, hfree, hp⟩ :=
    LiZhongQC.s22hg_exists_fuchsian_uniformization hg (R.hasSourceGenus hgenus)
  let : NormedSpace ℝ (GammaMeasurableBeltrami.Space Γ) :=
    NormedSpace.restrictScalars ℝ ℂ (GammaMeasurableBeltrami.Space Γ)
  have hball : IsPathConnected
      (Metric.ball (0 : GammaMeasurableBeltrami.Space Γ) 1) :=
    (convex_ball _ _).isPathConnected ⟨0, by simp⟩
  let : PathConnectedSpace (GammaMeasurableBeltrami.Ball Γ) :=
    isPathConnected_iff_pathConnectedSpace.mp hball
  exact (coefficientProjectionBall_surjective R hg hgenus hΓ hfree hp).pathConnectedSpace
    (continuous_coefficientProjectionBall_fromQC R hg hgenus hΓ hfree hp)

end TeichmullerSpace

/-- Both original spaces are path connected, using actual model availability
and the actual Euclidean image topology. -/
theorem teichmuller_and_nativeFricke_pathConnected {g : ℕ}
    (hg : 1 < g) (hgenus : R.HasGenus g)
    {e : X ≃ₜ Surfaces.HandlePresentation.PolygonQuotient g}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e) :
    let mT : MetricSpace (TeichmullerSpace.{0, 0} R) :=
      TeichmullerSpace.qcMetricSpace R hg hgenus
    let : TopologicalSpace (TeichmullerSpace.{0, 0} R) :=
      mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    PathConnectedSpace (TeichmullerSpace.{0, 0} R) ∧
      PathConnectedSpace (nativeFrickeImage hA) := by
  let mT : MetricSpace (TeichmullerSpace.{0, 0} R) :=
    TeichmullerSpace.qcMetricSpace R hg hgenus
  let : TopologicalSpace (TeichmullerSpace.{0, 0} R) :=
    mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : PathConnectedSpace (TeichmullerSpace.{0, 0} R) :=
    TeichmullerSpace.qcMetric_pathConnected R hg hgenus
  have hc : Continuous (finiteFrickeCoordinates hA) :=
    nativeFrickeCoordinateContinuity R hg hgenus e hA
  exact ⟨inferInstance,
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_range hc)⟩

end LowDimensionalTopology.Geometry.Teichmuller
