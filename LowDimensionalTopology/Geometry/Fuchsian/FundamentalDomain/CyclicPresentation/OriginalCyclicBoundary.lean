/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Topology.PolygonalVertexRefinement
public import LowDimensionalTopology.Geometry.Polygon.Support.CyclicSupportExtremeVertices
public import LowDimensionalTopology.Geometry.Polygon.DiscPolygonJordan
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Refinement.OriginalCompactSideBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Refinement.OriginalRefinedSideIncidence
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteConvexBoundary
/-!
# Exact marked vertices on the cyclic boundary

The refined boundary maps to the compact Klein frontier. Refining its
polygonal-circle traversal retains exactly the refined side endpoints,
including straight vertices and self-pairing centers.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Topology
open scoped Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- The entire literal refined original boundary has exactly the actual compact Klein frontier as its image. -/
theorem finite_area_refined_boundary_klein {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ha:P.area D≠⊤) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' (⋃v:OriginalRefinedSide hD,v.carrier)=frontier (fuchsianPolygonCompactKlein P D) := by
  rw [originalRefinedSide_iUnion_carrier,image_iUnion,finite_area_original_compact_boundary hD ha]
  congr 1
  funext s
  exact fuchsianSideClosedModel_klein_image s

/-- A true extreme point lying on an original refined piece is one of the actual selected endpoints. -/
theorem OriginalRefinedSide.extreme_mem_endpointSet {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) (x:𝕔𝔻) (hx:x∈v.carrier)
    (he:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate x∈(fuchsianPolygonCompactKlein P
      D).extremePoints ℝ) :
    x∈originalRefinedEndpointSet hD := by
  by_contra hn
  have hleft:x≠v.leftEndpoint:=fun h=>hn (h.symm ▸ Or.inl (mem_range_self v))
  have hright:x≠v.rightEndpoint:=fun h=>hn (h.symm ▸ Or.inr (mem_range_self v))
  have hxseg:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate x∈segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate v.leftEndpoint)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate v.rightEndpoint):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment,←v.carrier_eq_endpoints]
    exact mem_image_of_mem _ hx
  have hopen:=mem_openSegment_of_ne_left_right (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hleft.symm)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hright.symm) hxseg
  have hl:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate v.leftEndpoint∈fuchsianPolygonCompactKlein P D:=
    fuchsianSideClosedModel_klein_subset_polygon v.val.1
      ⟨v.leftEndpoint,v.carrier_subset_original v.endpoints_mem_carrier.1,rfl⟩
  have hr:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate v.rightEndpoint∈fuchsianPolygonCompactKlein P D:=
    fuchsianSideClosedModel_klein_subset_polygon v.val.1
      ⟨v.rightEndpoint,v.carrier_subset_original v.endpoints_mem_carrier.2,rfl⟩
  exact hleft (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective (he.2 hl hr
    hopen).symm)

/-- An actual cyclic straight-edged traversal of the unchanged original compact boundary, with vertex set exactly all the actual refined original endpoints. Original straight vertices and true self-pairing centers are retained. No side pairing or genus is stipulated as data. -/
theorem finite_area_original_exact_vertex_cyclic_model {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ha:P.area D≠⊤) :
    ∃J:PolygonalCircle,J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide hD,v.carrier) ∧
      ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hD := by
  classical
  obtain ⟨n,S,hregion,_hint⟩:=finite_area_polygon_actual_cyclic_model hD ha
  let Q:=S.toDiscPolygon
  have hb:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' Q.boundary=frontier (fuchsianPolygonCompactKlein P D):=by
    have he:=S.toCenteredData.boundary_image_eq_frontier
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' Q.boundary=frontier S.toCenteredData.kleinRegion at he
    rwa [hregion] at he
  have hboundary:Q.boundary=⋃v:OriginalRefinedSide hD,v.carrier:=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.image_injective
    rw [hb,finite_area_refined_boundary_klein hD ha]
  let J:=Q.toPolygonalCircle
  let hfinite: (_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet
    hD).Finite:=
    (originalRefinedEndpointSet_finite hD ha).image _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane
  let F:=hfinite.toFinset
  have hF:∀p∈F,p∈J.carrier:=by
    intro p hp
    obtain ⟨x,hx,rfl⟩:=hfinite.mem_toFinset.mp hp
    rw [Q.toPolygonalCircle_carrier,hboundary]
    refine ⟨x,?_,rfl⟩
    rcases hx with ⟨v,rfl⟩|⟨v,rfl⟩
    · exact mem_iUnion.mpr ⟨v,v.endpoints_mem_carrier.1⟩
    · exact mem_iUnion.mpr ⟨v,v.endpoints_mem_carrier.2⟩
  have hkeep:∀p,J.IsVertexPoint p→p∈F:=by
    rintro p ⟨j,hj⟩
    let i:=Q.jordanIndexEquiv.symm j
    have hp:_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane (S.vertices i)=p:=hj
    apply hfinite.mem_toFinset.mpr
    refine ⟨S.vertices i,?_,hp⟩
    have hpoint:S.vertices i∈⋃v:OriginalRefinedSide hD,v.carrier:=by
      rw [←hboundary]
      exact mem_iUnion.mpr ⟨i,_root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_left_mem _ _⟩
    obtain ⟨v,hv⟩:=mem_iUnion.mp hpoint
    have hext:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)∈(fuchsianPolygonCompactKlein P D).extremePoints ℝ:=by
      rw [←hregion]
      exact S.vertex_mem_extreme i
    exact v.extreme_mem_endpointSet _ hv hext
  obtain ⟨L,hL,hvertices⟩:=_root_.LowDimensionalTopology.Geometry.Surfaces.polygonalCircle_exists_refinement_exact_of_vertex_cover J F hF hkeep
  refine ⟨L,?_,fun p=>?_⟩
  · rw [hL,Q.toPolygonalCircle_carrier,hboundary]
  · rw [hvertices,hfinite.mem_toFinset]
end LowDimensionalTopology.Geometry.Fuchsian
