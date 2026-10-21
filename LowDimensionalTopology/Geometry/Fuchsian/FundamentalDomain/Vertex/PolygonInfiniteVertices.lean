module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonIdealBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSides
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.AngularMeasure
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Tactic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology MeasureTheory Function
open scoped Complex.UnitDisc Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon

/-- The actual Euclidean ideal boundary in its literal unit-circle carrier. -/
def fuchsianPolygonIdealCircle {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) : Set Circle :=
  (fun u : Circle => (u : ℂ)) ⁻¹' fuchsianPolygonIdealBoundary P D

theorem fuchsianPolygonIdealCircle_isClosed
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) :
    IsClosed (fuchsianPolygonIdealCircle P D) :=
  (fuchsianPolygonIdealBoundary_isCompact P D).isClosed.preimage continuous_subtype_val

/-- A true free side is an actual ideal-boundary connected component of positive arc length. -/
def IsFuchsianFreeSide {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (S : Set Circle) : Prop :=
  (∃ u ∈ fuchsianPolygonIdealCircle P D,
    S = connectedComponentIn (fuchsianPolygonIdealCircle P D) u) ∧
    0 < _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure S

theorem isClosed_connectedComponentIn_of_isClosed {α : Type*} [TopologicalSpace α]
    {E : Set α} (hE : IsClosed E) {u : α} (hu : u ∈ E) :
    IsClosed (connectedComponentIn E u) := by
  apply isClosed_of_closure_subset
  have hsub : closure (connectedComponentIn E u) ⊆ E :=
    closure_minimal (connectedComponentIn_subset E u) hE
  exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
    (subset_closure (mem_connectedComponentIn hu)) hsub

theorem IsFuchsianFreeSide.isClosed {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} {S : Set Circle}
    (hS : IsFuchsianFreeSide P D S) : IsClosed S := by
  obtain ⟨⟨u,hu,rfl⟩,_⟩ := hS
  exact isClosed_connectedComponentIn_of_isClosed (fuchsianPolygonIdealCircle_isClosed P D) hu

theorem IsFuchsianFreeSide.isConnected {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} {S : Set Circle}
    (hS : IsFuchsianFreeSide P D S) : IsConnected S := by
  obtain ⟨⟨u,hu,rfl⟩,_⟩ := hS
  exact isConnected_connectedComponentIn_iff.mpr hu

theorem IsFuchsianFreeSide.nontrivial {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} {S : Set Circle}
    (hS : IsFuchsianFreeSide P D S) : S.Nontrivial := by
  by_contra hn
  have hs : S.Subsingleton := Set.not_nontrivial_iff.mp hn
  exact hS.2.ne' (hs.countable.measure_zero _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure)

/-- Distinct genuine ideal-boundary components are literally disjoint. -/
theorem fuchsianIdealComponents_disjoint {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} {S T : Set Circle}
    (hS : ∃ u ∈ fuchsianPolygonIdealCircle P D,
      S = connectedComponentIn (fuchsianPolygonIdealCircle P D) u)
    (hT : ∃ u ∈ fuchsianPolygonIdealCircle P D,
      T = connectedComponentIn (fuchsianPolygonIdealCircle P D) u) (hne : S ≠ T) :
    Disjoint S T := by
  obtain ⟨u,_hu,rfl⟩ := hS
  obtain ⟨v,_hv,rfl⟩ := hT
  apply Set.disjoint_left.mpr
  intro z hzS hzT
  exact hne ((connectedComponentIn_eq hzS).trans (connectedComponentIn_eq hzT).symm)

/-- Only countably many literal ideal-boundary components have positive Euclidean arc length. -/
theorem fuchsianFreeSides_countable {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) :
    {S | IsFuchsianFreeSide P D S}.Countable := by
  let I := {S : Set Circle // ∃ u ∈ fuchsianPolygonIdealCircle P D,
    S = connectedComponentIn (fuchsianPolygonIdealCircle P D) u}
  have hm (i : I) : MeasurableSet i.val := by
    obtain ⟨u,hu,he⟩ := i.property
    rw [he]
    exact (isClosed_connectedComponentIn_of_isClosed
      (fuchsianPolygonIdealCircle_isClosed P D) hu).measurableSet
  have hd : Pairwise (Disjoint on (fun i : I => i.val)) := by
    intro i j hij
    exact fuchsianIdealComponents_disjoint i.property j.property (fun he => hij (Subtype.ext he))
  have hc := Measure.countable_meas_pos_of_disjoint_iUnion
    (μ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure) hm hd
  apply (hc.image (fun i : I => i.val)).mono
  intro S hS
  exact ⟨⟨S,hS.1⟩,hS.2,rfl⟩

/-- An actual side endpoint at infinity is a genuine unit-circle point of its Euclidean closure. -/
def IsFuchsianSideIdealEndpoint {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (S : Set P.domain.carrier) (u : Circle) : Prop :=
  (u : ℂ) ∈ closure ((fun x => (P.finiteCoordinate x : ℂ)) '' S)

/-- A proper infinite vertex is the shared actual ideal endpoint of two distinct sides. -/
def IsProperFuchsianInfiniteVertex {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (u : Circle) : Prop :=
  u ∈ fuchsianPolygonIdealCircle P D ∧ ∃ S T : Set P.domain.carrier,
    IsFuchsianPolygonSide P D S ∧ IsFuchsianPolygonSide P D T ∧ S ≠ T ∧
    IsFuchsianSideIdealEndpoint P S u ∧ IsFuchsianSideIdealEndpoint P T u

/-- The endpoint of a true side and a true free side, using the circle frontier. -/
def IsImproperFuchsianInfiniteVertex {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (u : Circle) : Prop :=
  u ∈ fuchsianPolygonIdealCircle P D ∧ ∃ (S : Set P.domain.carrier) (F : Set Circle),
    IsFuchsianPolygonSide P D S ∧ IsFuchsianSideIdealEndpoint P S u ∧
    IsFuchsianFreeSide P D F ∧ u ∈ frontier F

/-- either of the two genuine kinds of infinite vertex. -/
def IsFuchsianInfiniteVertex {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (u : Circle) : Prop :=
  IsProperFuchsianInfiniteVertex P D u ∨ IsImproperFuchsianInfiniteVertex P D u

end LowDimensionalTopology.Geometry.Fuchsian
