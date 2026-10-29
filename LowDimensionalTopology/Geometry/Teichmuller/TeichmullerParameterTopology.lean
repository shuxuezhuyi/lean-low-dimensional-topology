module

public import LowDimensionalTopology.Geometry.Teichmuller.TeichmullerL1Parameters
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Topological properties of the literal quadratic parameter map

The original-atlas differential and its integral norm remain the parameter.
The domain uses its L1 norm topology and the native marked quotient uses the
full-log quasiconformal metric. The same actual map is open, embedded and
bijective; these statements do not change the topology of another model.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces
universe u

/-- The specific quadratic parameter map is an open embedding and bijection,
for its actual integral-norm and quasiconformal metric topologies. -/
theorem l1ParameterMap_topology
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) :
    let mQ : MetricSpace ↥(QuadraticL1.openUnitBall R) := QuadraticL1.unitBallMetricSpace R
    let : TopologicalSpace ↥(QuadraticL1.openUnitBall R) :=
      mQ.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    let mT : MetricSpace (TeichmullerSpace.{u, u} R) := qcMetricSpace R hg hgenus
    let : TopologicalSpace (TeichmullerSpace.{u, u} R) :=
      mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Topology.IsOpenEmbedding (l1ParameterMap R hg hgenus) ∧
      Function.Bijective (l1ParameterMap R hg hgenus) := by
  let mQ : MetricSpace ↥(QuadraticL1.openUnitBall R) := QuadraticL1.unitBallMetricSpace R
  let : TopologicalSpace ↥(QuadraticL1.openUnitBall R) :=
    mQ.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let mT : MetricSpace (TeichmullerSpace.{u, u} R) := qcMetricSpace R hg hgenus
  let : TopologicalSpace (TeichmullerSpace.{u, u} R) :=
    mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have h := (l1ParameterMap_homeomorphism R hg hgenus).1
  exact ⟨h.isOpenEmbedding, h.bijective⟩

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
