module
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeCompactifiedSideGeometry
public import LowDimensionalTopology.Geometry.Polygon.Development.NativeDevelopingPoincare
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.JordanRegionBounds
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
/-- The bounded Jordan side is strictly inside any positive closed ball containing its
original boundary, even when that boundary meets the ball's sphere. -/
theorem complexJordanInside_subset_ball
    {C : Set ℂ} {r : ℝ} (hr : 0<r) (hC : C⊆Metric.closedBall (0 : ℂ) r) :
    complexJordanInside C⊆Metric.ball (0 : ℂ) r := by
  let e := complexJordanPlaneHomeomorph
  have heNorm (z : ℂ) : ‖e z‖=‖z‖ := Complex.orthonormalBasisOneI.repr.norm_map z
  have hCplane : e '' C⊆Metric.closedBall (0 : Schoenflies.Plane) r := by
    rintro z ⟨x,hx,rfl⟩
    have hn : ‖x‖≤r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hC hx
    change dist (e x) 0≤r
    rwa [dist_zero_right,heNorm]
  intro z hz
  change e z∉e '' C ∧ Bornology.IsBounded (connectedComponentIn (e '' C)ᶜ (e z)) at hz
  have hn := _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.norm_lt_of_bounded_complement_component hr hCplane hz.1 hz.2
  change dist z 0<r
  rwa [dist_zero_right,←heNorm]

/-- A genuine original Jordan polygon contained in the closed disc has a connected
native inside; ideal endpoints or free boundary arcs add no connectedness assumption. -/
theorem nativeJordan_inside_connected {C : Set ℂ} (hC : IsComplexJordanCurve C)
    (hbound : C⊆Metric.closedBall (0 : ℂ) 1) : IsConnected (nativeJordanInside C) := by
  let f : ℍ→ℂ := fun z=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)
  have hI : IsConnected (complexJordanInside C) := (complexJordan_regions hC).2.2.2.2.1
  have hsubset : complexJordanInside C⊆range f := by
    intro z hz
    have hn : ‖z‖<1 := by
      simpa only [Metric.mem_ball,dist_zero_right] using complexJordanInside_subset_ball (by norm_num) hbound hz
    let w : 𝔻 := Complex.UnitDisc.mk z hn
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w,?_⟩
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) : ℂ)=z
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
    rfl
  have hImage : f '' nativeJordanInside C=complexJordanInside C :=
    image_preimage_eq_of_subset hsubset
  have hf : Topology.IsEmbedding f := Complex.UnitDisc.isEmbedding_coe.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isEmbedding
  constructor
  · obtain ⟨z,hz⟩:=hI.nonempty
    obtain ⟨w,hw⟩:=hsubset hz
    refine ⟨w,?_⟩
    change f w∈complexJordanInside C
    rwa [hw]
  · apply hf.isInducing.isPreconnected_image.mp
    rw [hImage]
    exact hI.isPreconnected

/-- All original native polygon geometry is derived from its genuine Jordan boundary
and literal locally finite geodesic side intervals, with free ideal sides allowed. -/
def nativeJordan_sideIntervals_geometry {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) : NativeGeodesicPolygonGeometry P D.vertices := by
  apply nativeJordan_geodesic_geometry C hC hInside hBoundary ?_ D.side_geometry
  rw [hInside]
  exact nativeJordan_inside_connected hC hbound

/-- Geodesic side intervals, complete vertex cycles, opposite-side compatibility and
uniform developing-ball charts imply discreteness and a fundamental domain. -/
theorem nativeJordan_sideIntervals_poincare {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hCycles : S.CompleteVertexCycleCondition D.vertices)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉D.vertices →S.OppositeSideNeighborhoods s x)
    {ε : ℝ} (hε : 0<ε) (hCharts : _root_.LowDimensionalTopology.Geometry.Hyperbolic.UniformHyperbolicBallCharts
      S.evaluation ε) :
    DiscreteTopology (↥(Subgroup.closure (range S.element))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume P.interior :=
  (nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D).poincare_of_uniform_developing_charts
    S hCycles hOpp hε hCharts



/--
A uniform positive local tessellation radius, complete vertex cycles and
opposite-side compatibility give discreteness of the generated isometry group
and a fundamental domain equal to the polygon interior.
-/
theorem nativeJordan_sideIntervals_poincare_of_uniform_local_tessellation_radius {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hCycles : S.CompleteVertexCycleCondition D.vertices)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉D.vertices →S.OppositeSideNeighborhoods s x)
    {ε : ℝ} (hUniform : S.UniformLocalTessellationRadius ε) :
    DiscreteTopology (↥(Subgroup.closure (range S.element))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume P.interior :=
  (nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D).poincare
    S hCycles hOpp (hUniform.to_uniform_cover S)

end LowDimensionalTopology.Geometry.Polygon
