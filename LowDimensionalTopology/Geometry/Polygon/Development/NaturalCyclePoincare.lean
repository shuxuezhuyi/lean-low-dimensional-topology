module
public import LowDimensionalTopology.Geometry.Polygon.Development.LabeledNaturalVertexCycles
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeSideEndpointTransport
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.OriginalJordanPolygonPoincare
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
open scoped UpperHalfPlane Complex.UnitDisc

/-- At a Jordan polygon vertex, two distinct side labels exhaust all incident sides. -/
theorem NativeGeodesicSideIntervals.vertex_two_sides_exhaustion
    {P : PoincarePolygon ℍ} (D : NativeGeodesicSideIntervals P)
    (C : Set ℂ) (hC : IsComplexJordanCurve C)
    (hBoundary : P.boundary=(fun z : ℍ => (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (x : ℍ) (hx : x∈D.vertices) (s t : P.Side) (hst : s≠t)
    (hxs : x∈s.val) (hxt : x∈t.val) (v : P.Side) (hxv : x∈v.val) : v=s ∨v=t := by
  obtain ⟨a,b,hab,hxa,hxb,hex⟩ := D.vertex_exactly_two_incident_sides C hC hBoundary x hx
  rcases hex s hxs with hs | hs <;>
    rcases hex t hxt with ht | ht <;>
    rcases hex v hxv with hv | hv <;>simp_all

/--
Labeled nonbacktracking vertex cycles and opposite-side neighborhoods give a local tessellation
for a Jordan polygon. The proof supplies finite fibers and compatible local charts.
-/
theorem nativeJordan_natural_cycles_local_tessellation {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ => (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hNatural : S.NaturalVertexCycleCondition D.vertices)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉D.vertices → S.OppositeSideNeighborhoods s x) :
    S.FiniteFiberLocalTessellationCondition := by
  let G:=nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D
  let : IsIsometricSMul S.Generated ℍ:=⟨fun g => g.val.isometry⟩
  apply hNatural.finiteFiberLocalTessellationCondition S D.vertices D.vertices_discrete D.locallyFinite
    D.side_geometry.side_closed G.interior_open G.carrier_closure.le
    (D.vertex_two_sides_exhaustion C hC hBoundary)
  exact G.regularity_of_vertex_preservation S (D.pairing_preserves_vertices S) hOpp

/-- Uniform developing-ball charts for the tessellation associated with labeled vertex cycles
imply discreteness of the generated group and that the polygon interior is a fundamental domain. -/
theorem nativeJordan_natural_cycles_poincare {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ => (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hNatural : S.NaturalVertexCycleCondition D.vertices)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉D.vertices → S.OppositeSideNeighborhoods s x)
    {ε : ℝ} (hε : 0<ε) (hCharts : _root_.LowDimensionalTopology.Geometry.Hyperbolic.UniformHyperbolicBallCharts
      S.evaluation ε) :
    DiscreteTopology (↥(Subgroup.closure (range S.element))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume P.interior := by
  let G:=nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D
  exact S.native_poincare_of_uniform_developing_charts
    (nativeJordan_natural_cycles_local_tessellation C hC hbound hInside hBoundary D S hNatural hOpp)
    G.interior_open G.interior_connected G.carrier_closure G.countable_sides
    (fun s hs => ⟨G.line ⟨s,hs⟩,G.side_subset_line ⟨s,hs⟩⟩) hε hCharts

/--
A uniform local tessellation radius yields the same discreteness and fundamental-domain
conclusions through the recentered developing-chart construction.
-/
theorem nativeJordan_natural_cycles_poincare_of_uniform_local_tessellation_radius {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ => (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hNatural : S.NaturalVertexCycleCondition D.vertices)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉D.vertices → S.OppositeSideNeighborhoods s x)
    {ε : ℝ} (hUniform : S.UniformLocalTessellationRadius ε) :
    DiscreteTopology (↥(Subgroup.closure (range S.element))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume P.interior := by
  let G:=nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D
  exact S.native_poincare_of_uniform_cover
    (nativeJordan_natural_cycles_local_tessellation C hC hbound hInside hBoundary D S hNatural hOpp)
    (hUniform.to_uniform_cover S) G.interior_open G.interior_connected G.carrier_closure G.countable_sides
    (fun s hs => ⟨G.line ⟨s,hs⟩,G.side_subset_line ⟨s,hs⟩⟩)

end LowDimensionalTopology.Geometry.Polygon
