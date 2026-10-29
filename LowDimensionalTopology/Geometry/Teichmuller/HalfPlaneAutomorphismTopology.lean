/- Released under Apache 2.0 license as described in the file LICENSE. -/
module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.AnalyticAutomorphismGroup
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannManifold
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Compact-open topology and Fuchsian subgroups of the actual half-plane

Use the original upper half-plane and its analytic atlas. The compact-open
topology is pulled back from actual continuous self-maps. A Fuchsian subgroup
is discrete in precisely this topology, with elliptic elements permitted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Filter Set Topology
namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

/-- The full analytic automorphism group of the original upper half-plane. -/
abbrev HalfPlaneAnalyticAut :=
  (RiemannAtlas.ofManifold UpperHalfPlane).analyticAutomorphismSubgroup

/-- Forget only the analyticity and inverse data, retaining the actual map. -/
def HalfPlaneAnalyticAut.toContinuousMap (f : HalfPlaneAnalyticAut) :
    C(UpperHalfPlane, UpperHalfPlane) := _root_.toContinuousMap f.val

/-- The source compact-open topology on the actual analytic automorphism group. -/
instance halfPlaneAnalyticAutTopology : TopologicalSpace HalfPlaneAnalyticAut :=
  TopologicalSpace.induced HalfPlaneAnalyticAut.toContinuousMap inferInstance

/-- Convergence is exactly uniform convergence on every compact subset of H. -/
theorem halfPlaneAnalyticAut_tendsto_iff {ι : Type*} {p : Filter ι}
    {F : ι → HalfPlaneAnalyticAut} {f : HalfPlaneAnalyticAut} :
    Tendsto F p (𝓝 f) ↔ ∀ K : Set UpperHalfPlane, IsCompact K →
      TendstoUniformlyOn (fun i z => (F i).val z) (fun z => f.val z) p K := by
  rw [(Topology.IsInducing.induced HalfPlaneAnalyticAut.toContinuousMap).tendsto_nhds_iff]
  exact ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn

/-- A Fuchsian group is a discrete subgroup of the actual analytic Aut(H). -/
def IsHalfPlaneFuchsian (Γ : Subgroup HalfPlaneAnalyticAut) : Prop :=
  DiscreteTopology Γ

end LowDimensionalTopology.Geometry.Teichmuller
