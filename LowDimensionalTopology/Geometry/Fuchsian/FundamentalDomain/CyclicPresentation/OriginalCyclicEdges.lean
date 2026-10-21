/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.FiniteClosedCoverConnected
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicBoundary
/-!
# Cyclic edges and refined sides

Each cyclic edge is exactly one refined side, and every refined side occurs.
This derived bijection preserves the entire geometric carrier and supplies
the side model in cyclic order.
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

/-- The literal true Euclidean Klein-plane trace of a refined original side. -/
def OriginalRefinedSide.planeCarrier {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide
      hD) : Set Plane:=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' v.carrier

/-- The true planar carrier is exactly the segment joining the genuine selected endpoints. -/
theorem OriginalRefinedSide.planeCarrier_eq_segment {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) : v.planeCarrier=
      segment ℝ (_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane v.leftEndpoint) (_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane v.rightEndpoint) := by
  let e:=PolygonalCircle.planeComplexEquiv.symm
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.planeCarrier,v.carrier_eq_endpoints]
  calc
    _=e '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment v.leftEndpoint v.rightEndpoint):=by
      rw [image_image]
      rfl
    _=e '' segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate v.leftEndpoint) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate v.rightEndpoint):=by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    _=_:=image_segment ℝ e.toLinearEquiv.toAffineEquiv.toAffineMap _ _

theorem OriginalRefinedSide.planeCarrier_isClosed {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) : IsClosed v.planeCarrier := by
  rw [v.planeCarrier_eq_segment]
  rw [segment_eq_image_lineMap]
  exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed

/-- No other actual marked endpoint lies inside a genuine refined piece in planar coordinates. -/
theorem OriginalRefinedSide.planeEndpointSet_inter_carrier {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) :
    (_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet
      hD)∩v.planeCarrier⊆
      {_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane v.leftEndpoint,_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane v.rightEndpoint} := by
  rintro x ⟨⟨a,ha,hax⟩,⟨b,hb,hbx⟩⟩
  have hab:a=b:=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane_injective (hax.trans hbx.symm)
  subst b
  have he:a=v.leftEndpoint∨a=v.rightEndpoint:=by
    simpa only [mem_insert_iff,mem_singleton_iff] using v.endpointSet_inter_carrier ⟨ha,hb⟩
  rcases he with he|he
  · exact Or.inl (hax.symm.trans (congrArg _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane he))
  · exact Or.inr (hax.symm.trans (congrArg _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane he))

/-- A genuine relative-interior point of a cyclic edge is not one of the exact marked endpoints. -/
theorem original_cyclic_openEdge_not_endpoint {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (J:PolygonalCircle)
    (hvertices:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (i:ZMod J.n) (x:Plane) (hx:x∈openSegment ℝ (J.vertex i) (J.vertex (i+1))) :
    x∉_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hD := by
  intro he
  have hv:=(hvertices x).mpr he
  rcases hv.mem_edgeSegment_iff i |>.mp (openSegment_subset_segment ℝ _ _ hx) with hi|hi
  · rw [hi] at hx
    exact J.adjacent_ne i (left_mem_openSegment_iff.mp hx)
  · rw [hi] at hx
    exact J.adjacent_ne i (right_mem_openSegment_iff.mp hx)

/-- Each real cyclic edge lies in one actual refined original side; connectedness and the exact endpoint set prove this without supplying a side-to-edge matching. -/
theorem original_cyclic_edge_subset_refined_side {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ha:P.area D≠⊤) (J:PolygonalCircle)
    (hcarrier:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hvertices:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (i:ZMod J.n) : ∃v:OriginalRefinedSide hD,J.edgeSegment i⊆v.planeCarrier := by
  let :Finite (OriginalRefinedSide hD):=originalRefinedSide_finite hD ha
  let U:=openSegment ℝ (J.vertex i) (J.vertex (i+1))
  have hcover:U⊆⋃v:OriginalRefinedSide hD,v.planeCarrier:=by
    intro x hx
    change x∈⋃v:OriginalRefinedSide hD,_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' v.carrier
    rw [←image_iUnion,←hcarrier]
    exact J.edgeSegment_subset_carrier i (openSegment_subset_segment ℝ _ _ hx)
  have hsep:∀v w:OriginalRefinedSide hD,v≠w→∀x∈U,x∈v.planeCarrier→x∉w.planeCarrier:=by
    rintro v w hvw x hx ⟨a,hav,ha⟩ ⟨b,hbw,hb⟩
    have hab:a=b:=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane_injective (ha.trans hb.symm)
    subst b
    have he:=v.inter_subset_endpointSet w hvw ⟨hav,hbw⟩
    exact original_cyclic_openEdge_not_endpoint hD J hvertices i x hx ⟨a,he,ha⟩
  obtain ⟨v,hv⟩:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.isPreconnected_subset_one_finite_closed_cover U
    (convex_openSegment _ _ |>.isPreconnected) ⟨_,midpoint_mem_openSegment _ _⟩
    (fun v:OriginalRefinedSide hD=>v.planeCarrier) (fun v=>v.planeCarrier_isClosed) hcover hsep
  refine ⟨v,?_⟩
  change segment ℝ (J.vertex i) (J.vertex (i+1))⊆v.planeCarrier
  rw [←closure_openSegment]
  exact closure_minimal hv v.planeCarrier_isClosed

/-- The containment forced by topology is exact: every cyclic edge is one entire unchanged original refined piece. -/
theorem original_cyclic_edge_eq_refined_side {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (J:PolygonalCircle)
    (hvertices:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (i:ZMod J.n) (v:OriginalRefinedSide hD) (hsub:J.edgeSegment i⊆v.planeCarrier) :
    J.edgeSegment i=v.planeCarrier := by
  have hleft:J.vertex i=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane v.leftEndpoint∨J.vertex i=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane v.rightEndpoint:=by
    have hh:=v.planeEndpointSet_inter_carrier ⟨(hvertices _).mp ⟨i,rfl⟩,
      hsub (left_mem_segment ℝ _ _)⟩
    simpa only [mem_insert_iff,mem_singleton_iff] using hh
  have hright:J.vertex (i+1)=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane v.leftEndpoint∨
      J.vertex (i+1)=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane v.rightEndpoint:=by
    have hh:=v.planeEndpointSet_inter_carrier ⟨(hvertices _).mp ⟨i+1,rfl⟩,
      hsub (right_mem_segment ℝ _ _)⟩
    simpa only [mem_insert_iff,mem_singleton_iff] using hh
  rw [v.planeCarrier_eq_segment]
  change segment ℝ (J.vertex i) (J.vertex (i+1))=_
  rcases hleft with hl|hl <;> rcases hright with hr|hr
  · exact False.elim (J.adjacent_ne i (hl.trans hr.symm))
  · rw [hl,hr]
  · rw [hl,hr,segment_symm]
  · exact False.elim (J.adjacent_ne i (hl.trans hr.symm))

/-- Distinct genuine refined sides can meet only in the actual marked endpoint set, also in planar coordinates. -/
theorem OriginalRefinedSide.planeCarrier_inter_subset_endpointSet {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v w:OriginalRefinedSide hD) (hne:v≠w) :
    v.planeCarrier∩w.planeCarrier⊆_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hD := by
  rintro x ⟨⟨a,ha,hax⟩,⟨b,hb,hbx⟩⟩
  have hab:a=b:=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane_injective (hax.trans hbx.symm)
  subst b
  exact ⟨a,v.inter_subset_endpointSet w hne ⟨ha,hb⟩,hax⟩

/-- Every actual cyclic edge is exactly one genuine refined original side. -/
theorem original_cyclic_edge_unique_refined_side {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ha:P.area D≠⊤) (J:PolygonalCircle)
    (hcarrier:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hvertices:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (i:ZMod J.n) : ∃!v:OriginalRefinedSide hD,J.edgeSegment i=v.planeCarrier := by
  obtain ⟨v,hv⟩:=original_cyclic_edge_subset_refined_side hD ha J hcarrier hvertices i
  have he:=original_cyclic_edge_eq_refined_side hD J hvertices i v hv
  refine ⟨v,he,?_⟩
  intro w hw
  by_contra hne
  let x:=midpoint ℝ (J.vertex i) (J.vertex (i+1))
  have hx:x∈openSegment ℝ (J.vertex i) (J.vertex (i+1)):=midpoint_mem_openSegment _ _
  have hxe:x∈J.edgeSegment i:=openSegment_subset_segment ℝ _ _ hx
  have hxv:x∈v.planeCarrier:=he ▸ hxe
  have hxw:x∈w.planeCarrier:=hw ▸ hxe
  exact original_cyclic_openEdge_not_endpoint hD J hvertices i x hx
    (v.planeCarrier_inter_subset_endpointSet w (Ne.symm hne) ⟨hxv,hxw⟩)

/-- Every original refined side occurs as one of the real cyclic edges. -/
theorem original_refined_side_has_cyclic_edge {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ha:P.area D≠⊤) (J:PolygonalCircle)
    (hcarrier:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hvertices:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (v:OriginalRefinedSide hD) : ∃i:ZMod J.n,J.edgeSegment i=v.planeCarrier := by
  let x:=midpoint ℝ (_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane
    v.leftEndpoint) (_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane v.rightEndpoint)
  have hxv:x∈v.planeCarrier:=by
    rw [v.planeCarrier_eq_segment]
    exact midpoint_mem_segment _ _
  have hxnot:x∉_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hD:=by
    intro he
    have hh:=(v.planeEndpointSet_inter_carrier ⟨he,hxv⟩)
    have hends:_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane v.leftEndpoint≠_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane v.rightEndpoint:=
      _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane_injective.ne v.endpoints_ne
    rcases hh with hh|hh
    · exact hends ((midpoint_eq_left_iff ℝ).mp hh)
    · exact hends ((midpoint_eq_right_iff ℝ).mp hh)
  have hxJ:x∈J.carrier:=by
    rw [hcarrier,image_iUnion]
    exact mem_iUnion.mpr ⟨v,hxv⟩
  obtain ⟨i,hi⟩:=mem_iUnion.mp hxJ
  obtain ⟨w,hw,_hunique⟩:=original_cyclic_edge_unique_refined_side hD ha J hcarrier hvertices i
  have hweq:w=v:=by
    by_contra hne
    exact hxnot (w.planeCarrier_inter_subset_endpointSet v hne ⟨hw ▸ hi,hxv⟩)
  exact ⟨i,hweq ▸ hw⟩

/-- The actual closed edges of a genuine polygonal circle are distinct. -/
theorem original_polygonalCircle_edge_injective (J:PolygonalCircle) : Function.Injective J.edgeSegment := by
  intro i j he
  by_contra hne
  let x:=midpoint ℝ (J.vertex i) (J.vertex (i+1))
  have hx:x∈J.edgeSegment i:=midpoint_mem_segment _ _
  have hends:=J.edgeSegment_inter_subset_endpoints hne ⟨hx,he ▸ hx⟩
  rcases hends with hl|hr
  · exact J.adjacent_ne i ((midpoint_eq_left_iff ℝ).mp hl)
  · exact J.adjacent_ne i ((midpoint_eq_right_iff ℝ).mp hr)

/-- The faithful bijection from the real cyclic boundary edges to the unchanged original refined sides. -/
def originalCyclicEdgeSideEquiv {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ha:P.area D≠⊤) (J:PolygonalCircle)
    (hcarrier:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hvertices:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD) :
    ZMod J.n≃OriginalRefinedSide hD := by
  let f:ZMod J.n→OriginalRefinedSide hD:=fun i=>
    Classical.choose (original_cyclic_edge_unique_refined_side hD ha J hcarrier hvertices i)
  have hf (i:ZMod J.n) : J.edgeSegment i=(f i).planeCarrier:=
    (Classical.choose_spec (original_cyclic_edge_unique_refined_side hD ha J hcarrier hvertices i)).1
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    exact original_polygonalCircle_edge_injective J ((hf i).trans ((congrArg
      _root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.planeCarrier hij).trans (hf j).symm))
  · intro v
    obtain ⟨i,hi⟩:=original_refined_side_has_cyclic_edge hD ha J hcarrier hvertices v
    refine ⟨i,?_⟩
    have hu:=(Classical.choose_spec (original_cyclic_edge_unique_refined_side hD ha J hcarrier hvertices i)).2
    exact (hu v hi).symm

theorem originalCyclicEdgeSideEquiv_spec {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ha:P.area D≠⊤) (J:PolygonalCircle)
    (hcarrier:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hvertices:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (i:ZMod J.n) :
    J.edgeSegment i=(originalCyclicEdgeSideEquiv hD ha J hcarrier hvertices i).planeCarrier := by
  exact (Classical.choose_spec (original_cyclic_edge_unique_refined_side hD ha J hcarrier hvertices i)).1

/-- A genuine finite cyclic traversal of all actual original refined sides, with a derived bijection preserving each entire literal geometric carrier. -/
theorem finite_area_original_cyclic_side_model {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ha:P.area D≠⊤) : ∃J:PolygonalCircle,∃e:ZMod J.n≃OriginalRefinedSide hD,
      J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
        hD,v.carrier) ∧
      (∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
        originalRefinedEndpointSet hD) ∧
      ∀i,J.edgeSegment i=(e i).planeCarrier := by
  obtain ⟨J,hJ,hvertices⟩:=finite_area_original_exact_vertex_cyclic_model hD ha
  exact ⟨J,originalCyclicEdgeSideEquiv hD ha J hJ hvertices,hJ,hvertices,
    originalCyclicEdgeSideEquiv_spec hD ha J hJ hvertices⟩
end LowDimensionalTopology.Geometry.Fuchsian
