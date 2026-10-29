module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeFrickeParameterMap
public import LowDimensionalTopology.Geometry.Teichmuller.NativeFrickeCoordinateContinuityProof
public import LowDimensionalTopology.External.LiZhongQC.LiZhongExternal.Topology.InvarianceOfDomain
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Openness of the original quadratic-to-Fricke parameter map

The L1 topology of the original differential ball and the full-log QC topology
of the native marked quotient are fixed independently of their coordinates.
The existing finite-dimensional invariance-of-domain theorem then supplies
openness from the proved coordinate continuity and explicit separation input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Set Topology Surfaces Surfaces.HandlePresentation
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}

/-- The actual finite coordinates are an open embedding for the original QC
metric, under the original model availability and geometric separation inputs. -/
theorem finiteFrickeCoordinates_qc_isOpenEmbedding
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m)) :
    let mT : MetricSpace (TeichmullerSpace.{0, 0} R) :=
      TeichmullerSpace.qcMetricSpace R hg hgenus
    let : TopologicalSpace (TeichmullerSpace.{0, 0} R) :=
      mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    IsOpenEmbedding (finiteFrickeCoordinates hA) := by
  classical
  let mT : MetricSpace (TeichmullerSpace.{0, 0} R) :=
    TeichmullerSpace.qcMetricSpace R hg hgenus
  let : TopologicalSpace (TeichmullerSpace.{0, 0} R) :=
    mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  obtain ⟨H⟩ := (TeichmullerSpace.l1ParameterMap_homeomorphism R hg hgenus).2
  let J : TeichmullerSpace.{0, 0} R ≃ₜ (Fin (6 * g - 6) → ℝ) :=
    H.trans (EuclideanSpace.equiv (Fin (6 * g - 6)) ℝ).toHomeomorph
  let F : (Fin (6 * g - 6) → ℝ) → (Fin (6 * g - 6) → ℝ) :=
    finiteFrickeCoordinates hA ∘ J.symm
  have hc : Continuous (finiteFrickeCoordinates hA) :=
    nativeFrickeCoordinateContinuity R hg hgenus e hA
  have hFc : Continuous F := hc.comp J.symm.continuous
  have hFi : Function.Injective F :=
    (finiteFrickeCoordinates_injective hA hAlt).comp J.symm.injective
  have hFo : IsOpenMap F := by
    intro U hU
    exact LiZhongExternal.Topology.invariance_of_domain_finiteDimensional
      F U hU hFc.continuousOn (fun _ _ _ _ hxy => hFi hxy)
  have hFe : IsOpenEmbedding F :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap hFc hFi hFo
  simpa [F, Function.comp_def] using hFe.comp J.isOpenEmbedding

/-- The entire original L1 parameter ball has open Euclidean Fricke image,
and the same map is a homeomorphism onto the actual full native Fricke image. -/
theorem nativeFrickeParameterMap_open_embedding
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m)) :
    let mQ : MetricSpace ↥(QuadraticL1.openUnitBall R) := QuadraticL1.unitBallMetricSpace R
    let : TopologicalSpace ↥(QuadraticL1.openUnitBall R) :=
      mQ.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    IsOpen (range (fun φ : ↥(QuadraticL1.openUnitBall R) =>
      (nativeFrickeParameterMap R hg hgenus hA φ : Fin (6 * g - 6) → ℝ))) ∧
      IsOpenEmbedding (fun φ : ↥(QuadraticL1.openUnitBall R) =>
        (nativeFrickeParameterMap R hg hgenus hA φ : Fin (6 * g - 6) → ℝ)) ∧
      IsHomeomorph (nativeFrickeParameterMap R hg hgenus hA) := by
  let mQ : MetricSpace ↥(QuadraticL1.openUnitBall R) := QuadraticL1.unitBallMetricSpace R
  let : TopologicalSpace ↥(QuadraticL1.openUnitBall R) :=
    mQ.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let mT : MetricSpace (TeichmullerSpace.{0, 0} R) :=
    TeichmullerSpace.qcMetricSpace R hg hgenus
  let : TopologicalSpace (TeichmullerSpace.{0, 0} R) :=
    mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let F := fun φ : ↥(QuadraticL1.openUnitBall R) =>
    (nativeFrickeParameterMap R hg hgenus hA φ : Fin (6 * g - 6) → ℝ)
  have hF : IsOpenEmbedding F := by
    change IsOpenEmbedding (finiteFrickeCoordinates hA ∘
      TeichmullerSpace.l1ParameterMap R hg hgenus)
    exact (finiteFrickeCoordinates_qc_isOpenEmbedding R hg hgenus hA hAlt).comp
      (TeichmullerSpace.l1ParameterMap_topology R hg hgenus).1
  refine ⟨hF.isOpen_range, hF, ?_⟩
  apply isHomeomorph_iff_isEmbedding_surjective.mpr
  refine ⟨?_, (quadraticParameterMaps_surjective R hg hgenus hA).2⟩
  exact (IsEmbedding.subtypeVal.of_comp_iff).mp hF.isEmbedding

end LowDimensionalTopology.Geometry.Teichmuller
