module
public import LowDimensionalTopology.Geometry.Polygon.Topology.Jordan.JordanPolygonRegions
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeGeodesicPolygonGeometry
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
/-- The half-plane region obtained by pulling back the inside of a complex Jordan curve. -/
def nativeJordanInside (C : Set ℂ) : Set ℍ :=
  (fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹' complexJordanInside C

/-- Pullback along the Cayley map preserves regular-open interior, frontier and closure identities. -/
theorem nativeJordan_regions {C : Set ℂ} (hC : IsComplexJordanCurve C) :
    IsOpen (nativeJordanInside C) ∧
    interior (closure (nativeJordanInside C))=nativeJordanInside C ∧
    frontier (nativeJordanInside C)=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z :
      ℂ)) ⁻¹' C ∧
    closure (nativeJordanInside C)=nativeJordanInside C∪(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹' C := by
  let f : ℍ→ℂ:=fun z=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)
  have hfc : Continuous f:=Complex.UnitDisc.continuous_coe.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.continuous
  have hCo : IsOpenMap ((↑) : 𝔻→ℂ) := by
    change IsOpenMap (Subtype.val : Metric.ball (0 : ℂ) 1→ℂ)
    exact Metric.isOpen_ball.isOpenMap_subtype_val
  have hfo : IsOpenMap f:=hCo.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isOpenMap
  obtain ⟨hI,_,_,_,_,_,hFI,_⟩:=complexJordan_regions hC
  have hreg:=(complexJordan_regular_open hC).1
  have hNativeF : frontier (nativeJordanInside C)=f ⁻¹' C := by
    change frontier (f ⁻¹' complexJordanInside C)=f ⁻¹' C
    rw [←hfo.preimage_frontier_eq_frontier_preimage hfc,hFI]
  refine ⟨hI.preimage hfc,?_,hNativeF,?_⟩
  · change interior (closure (f ⁻¹' complexJordanInside C))=f ⁻¹' complexJordanInside C
    rw [←hfo.preimage_closure_eq_closure_preimage hfc,
      ←hfo.preimage_interior_eq_interior_preimage hfc,hreg]
  · rw [closure_eq_self_union_frontier,hNativeF]

/-- Locally finite closed geodesic sides, discrete vertices and a line-interval germ off the vertices. -/
structure NativeGeodesicSideData (P : PoincarePolygon ℍ) (V : Set ℍ) where
  locallyFinite : LocallyFinite (fun s : P.Side=>s.val)
  side_closed : ∀s : P.Side,IsClosed s.val
  vertex_discrete : IsDiscrete V
  line : P.Side→_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine
  side_subset_line : ∀s : P.Side,s.val⊆(line s).carrier
  side_two_points : ∀s : P.Side,∃a∈s.val,∃b∈s.val,a≠b
  side_meet_vertex : ∀s t : P.Side,s≠t →∀x∈s.val,x∈t.val →x∈V
  side_interval : ∀s : P.Side,∀x∈s.val,x∉V →∀ᶠy in 𝓝 x,y∈s.val ↔y∈(line s).carrier

/-- Jordan separation and the boundary identification supply regularity, frontier and
closure properties; the side data supply the remaining geodesic geometry. -/
def nativeJordan_geodesic_geometry {P : PoincarePolygon ℍ} {V : Set ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (hConnected : IsConnected P.interior) (D : NativeGeodesicSideData P V) :
    NativeGeodesicPolygonGeometry P V := by
  obtain ⟨ho,hr,hf,hcl⟩:=nativeJordan_regions hC
  refine ⟨?_,hConnected,?_,?_,?_,D.locallyFinite,D.side_closed,D.vertex_discrete,D.line,
    D.side_subset_line,D.side_two_points,D.side_meet_vertex,D.side_interval⟩
  · rwa [←hInside] at ho
  · rw [PoincarePolygon.carrier,hInside,hBoundary,hcl]
  · rwa [←hInside] at hr
  · rwa [←hInside,←hBoundary] at hf

/-- Complete vertex cycles, opposite-side compatibility and uniform local tessellation
imply discreteness and a fundamental domain for the Jordan polygon. -/
theorem nativeJordan_poincare {P : PoincarePolygon ℍ} {V : Set ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (hConnected : IsConnected P.interior) (D : NativeGeodesicSideData P V)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) P) (hCycles : S.CompleteVertexCycleCondition V)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉V →S.OppositeSideNeighborhoods s x)
    {ε : ℝ} (hUniform : S.UniformLocalTessellationCover ε) :
    DiscreteTopology (↥(Subgroup.closure (range S.element))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume P.interior :=
  (nativeJordan_geodesic_geometry C hC hInside hBoundary hConnected D).poincare S hCycles hOpp hUniform

end LowDimensionalTopology.Geometry.Polygon
