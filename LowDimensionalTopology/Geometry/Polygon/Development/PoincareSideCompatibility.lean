module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincarePairedSideStars
public import Mathlib.Topology.Neighborhoods
@[expose] public section
noncomputable section
open Set Filter Topology
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
universe u v
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X] [MetricSpace X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)

/-- Any two relative polygon neighborhoods across a paired side cover an ambient neighborhood. -/
def OppositeSideNeighborhoods (s : P.Side) (x : X) : Prop :=
  ∀ U : Set X,U ∈ 𝓝[P.carrier] x → ∀ V : Set X,V ∈ 𝓝[P.carrier] (S.generator s • x) →
    U ∪ (fun z : X => S.generator s • z) ⁻¹' V ∈ 𝓝 x

/-- Relative-neighborhood compatibility is equivalent to the two polygon copies covering a neighborhood. -/
theorem oppositeSideNeighborhoods_iff [IsIsometricSMul S.Generated X]
    (s : P.Side) (x : X) :
    S.OppositeSideNeighborhoods s x ↔
      P.carrier ∪ (fun z : X => S.generator s • z) ⁻¹' P.carrier ∈ 𝓝 x := by
  constructor
  · intro h
    exact h P.carrier self_mem_nhdsWithin P.carrier self_mem_nhdsWithin
  · intro hn U hU V hV
    have hu : ∀ᶠ z in 𝓝 x,z ∈ P.carrier → z ∈ U :=
      Filter.mem_inf_principal.mp hU
    have hv : ∀ᶠ z in 𝓝 (S.generator s • x),z ∈ P.carrier → z ∈ V :=
      Filter.mem_inf_principal.mp hV
    have hv' : ∀ᶠ z in 𝓝 x,S.generator s • z ∈ P.carrier → S.generator s • z ∈ V :=
      ((isometry_smul X (S.generator s)).continuous.tendsto x).eventually hv
    filter_upwards [hn,hu,hv'] with z hz hzu hzv
    rcases hz with hz | hz
    · exact Or.inl (hzu hz)
    · exact Or.inr (hzv hz)

/-- Compatibility means that the point lies in the interior of the two-copy union. -/
theorem oppositeSideNeighborhoods_iff_interior [IsIsometricSMul S.Generated X]
    (s : P.Side) (x : X) :
    S.OppositeSideNeighborhoods s x ↔
      x ∈ interior (P.carrier ∪ (fun z : X => S.generator s • z) ⁻¹' P.carrier) := by
  rw [S.oppositeSideNeighborhoods_iff,mem_interior_iff_mem_nhds]

/-- A paired-side neighborhood satisfies relative-neighborhood compatibility. -/
theorem PairedSideNeighborhood.oppositeSideNeighborhoods [IsIsometricSMul S.Generated X]
    {x : P.Point} {s : P.Side} {r : ℝ} (h : S.PairedSideNeighborhood x s r) :
    S.OppositeSideNeighborhoods s x.val := by
  apply (S.oppositeSideNeighborhoods_iff s x.val).mpr
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x.val h.positive)
  intro z hz
  exact h.cover z hz

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
