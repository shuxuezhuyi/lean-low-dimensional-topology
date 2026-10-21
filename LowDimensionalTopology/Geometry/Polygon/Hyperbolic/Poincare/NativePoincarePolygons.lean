/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareFundamentalPolygons
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.FullHalfPlaneIsometries
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.CompactOpen
@[expose] public section
noncomputable section
open Set Topology MeasureTheory
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
local instance nativePoincareChordalMetric : MetricSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := _root_.LowDimensionalTopology.Geometry.Mobius.complexChordalMetricSpace

/-- The actual all-isometry boundary-uniform topology acts jointly continuously on the native plane. -/
theorem native_poincare_continuous_evaluation :
    Continuous (fun p : (ℍ ≃ᵢ ℍ) × ℍ => p.1 p.2) := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_isOpenEmbedding.isEmbedding.isInducing.continuous_iff.mpr
  have hc : Continuous (fun p : (ℍ ≃ᵢ ℍ) × ℍ =>
      _root_.LowDimensionalTopology.Geometry.Mobius.fullMobiusContinuousMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension p.1) (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint p.2)) :=
    continuous_eval.comp
      (((_root_.LowDimensionalTopology.Geometry.Mobius.fullMobiusContinuousMap_isometry.continuous.comp
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension_isometry.continuous).comp
        continuous_fst).prodMk (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_isOpenEmbedding.continuous.comp continuous_snd))
  convert hc using 1
  funext p
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension_action p.1 p.2).symm

/-- No artificial discrete topology is imposed: this is joint continuity in the existing sphere-boundary uniform metric. -/
instance nativePoincareContinuousSMul : ContinuousSMul (ℍ ≃ᵢ ℍ) ℍ :=
  ⟨native_poincare_continuous_evaluation⟩

namespace PoincareSidePairing
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ ≃ᵢ ℍ) P)

/-- For genuine native side isometries, the generator-isometry hypothesis is automatic; openness and connectedness remain explicit geometric assumptions. -/
theorem native_metric_assumptions (ho : IsOpen P.interior) (hc : IsConnected P.interior) :
    S.MetricPolygonAssumptions := ⟨fun s => (S.element s).isometry,ho,hc⟩

/-- The actual generated native isometry group is discrete in its original boundary-uniform topology. -/
theorem native_discrete_of_uniform_cover
    (h : S.FiniteFiberLocalTessellationCondition) {ε : ℝ} (hu : S.UniformLocalTessellationCover ε)
    (ho : IsOpen P.interior) (hc : IsConnected P.interior)
    (hcl : P.carrier ⊆ closure P.interior) :
    DiscreteTopology (↥(Subgroup.closure (range S.element))) := by
  let : TopologicalSpace S.Generated :=
    inferInstanceAs (TopologicalSpace (↥(Subgroup.closure (range S.element))))
  let : IsTopologicalGroup S.Generated :=
    inferInstanceAs (IsTopologicalGroup (↥(Subgroup.closure (range S.element))))
  let : ContinuousSMul S.Generated ℍ :=
    inferInstanceAs (ContinuousSMul (↥(Subgroup.closure (range S.element))) ℍ)
  exact h.discrete_of_uniform_cover S hu (S.native_metric_assumptions ho hc) hcl

/-- local tessellation and the geometric uniform cover give both original conclusions for a genuine native geodesic polygon. -/
theorem native_poincare_of_uniform_cover
    (h : S.FiniteFiberLocalTessellationCondition) {ε : ℝ} (hu : S.UniformLocalTessellationCover ε)
    (ho : IsOpen P.interior) (hc : IsConnected P.interior)
    (hcl : P.carrier = closure P.interior) (hcount : P.sides.Countable)
    (hside : ∀ s ∈ P.sides,∃ L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,s ⊆ L.carrier) :
    DiscreteTopology (↥(Subgroup.closure (range S.element))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ volume P.interior :=
  ⟨S.native_discrete_of_uniform_cover h hu ho hc hcl.le,
    h.fundamentalDomain_of_geodesic_sides S hu (S.native_metric_assumptions ho hc) hcl hcount hside⟩

/-- Compact genuine polygons need no additional uniform radius hypothesis. -/
theorem native_poincare_of_compact
    (h : S.FiniteFiberLocalTessellationCondition) (ho : IsOpen P.interior) (hc : IsConnected P.interior)
    (hcl : P.carrier = closure P.interior) (hcompact : IsCompact P.carrier)
    (hcount : P.sides.Countable) (hside : ∀ s ∈ P.sides,∃ L :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,s ⊆ L.carrier) :
    DiscreteTopology (↥(Subgroup.closure (range S.element))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ volume P.interior := by
  obtain ⟨ε,hu⟩ := h.uniform_cover_of_compact S hcompact
  exact S.native_poincare_of_uniform_cover h hu ho hc hcl hcount hside

end PoincareSidePairing
end LowDimensionalTopology.Geometry.Polygon
