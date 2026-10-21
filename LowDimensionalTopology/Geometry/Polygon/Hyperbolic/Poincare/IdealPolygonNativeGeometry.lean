module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Development.IdealPolygonPoincareData
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
/-- Distinct original finite-or-ideal sides meet natively only at original finite vertices. -/
theorem jordanPolygon_common_sides_vertex {n : ℕ} (Q : DiscPolygon n)
    {i j : Fin n} (hne : i≠j) {z : ℍ}
    (hi : z∈finitePolygonSide Q i) (hj : z∈finitePolygonSide Q j) :
    z∈jordanPolygonNativeVertices Q := by
  have he := (Q.simple_edges i j hne ⟨hi,hj⟩).1
  simp only [mem_insert_iff,mem_singleton_iff] at he
  rcases he with he | he
  · exact ⟨i,he.symm⟩
  · exact ⟨finRotate n i,he.symm⟩

/-- At a true native nonvertex the original Klein point is in the strict side interval,
without any restriction on the status of the original side endpoints. -/
theorem jordanPolygon_nonvertex_klein_openSegment {n : ℕ} (Q : DiscPolygon n)
    {i : Fin n} {x : ℍ} (hx : x∈finitePolygonSide Q i)
    (hv : x∉jordanPolygonNativeVertices Q) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x∈openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices i))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices (finRotate n i))) := by
  have hseg : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x))∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (Q.vertices i) (Q.vertices (finRotate n i)) :=
    ⟨_,hx,rfl⟩
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion] at hseg
  have hne (j : Fin n) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices j)≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x := by
    intro he
    exact hv ⟨j,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective (he.trans
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)).symm)⟩
  exact mem_openSegment_of_ne_left_right (hne i) (hne (finRotate n i)) hseg

/-- The actual original supporting affine equation also holds at ideal endpoints. -/
theorem jordanPolygon_native_side_equation {n : ℕ} (Q : DiscPolygon n) (i : Fin n) :
    ∃(m : ℂ)(t : ℝ),m≠0 ∧
      (∀w : ℍ,w∈(finitePolygonLine Q i).carrier ↔inner ℝ m
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)=t) ∧
      inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices i))=t ∧
      inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices (finRotate n i)))=t := by
  let L := Q.geodesicSide i
  let N := finitePolygonLine Q i
  have he (w : ℍ) : w∈N.carrier ↔inner ℝ N.incenterNormal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)=N.incenterOffset := by
    rw [←N.incenter_affine_eq_zero_iff,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine,sub_eq_zero]
  refine ⟨N.incenterNormal,N.incenterOffset,N.incenterNormal_ne_zero,he,?_,?_⟩
  · exact (L.incenter_closed_affine_eq_zero_iff _).mpr (Q.geodesicSide_endpoints i).1
  · exact (L.incenter_closed_affine_eq_zero_iff _).mpr (Q.geodesicSide_endpoints i).2

/-- A small genuine neighborhood of a nonvertex avoids every other original side,
including sides with ideal endpoints. -/
theorem jordanPolygon_nonvertex_unique_side_near {n : ℕ} (Q : DiscPolygon n)
    (x : (jordanDiscPoincarePolygon Q).Point) (i : Fin n)
    (hx : x.val∈finitePolygonSide Q i) (hv : x.val∉jordanPolygonNativeVertices Q) :
    ∃r : ℝ,0<r ∧∀s : (jordanDiscPoincarePolygon Q).Side,∀p∈s.val,dist p x.val<r →
      s=jordanPolygonSideEquiv Q i := by
  obtain ⟨r,hr,hNear⟩:=PoincareSidePairing.exists_ball_incident_sides
    (jordanDiscPoincarePolygon_locallyFiniteSides Q) (jordanDiscPoincarePolygon_closedSides Q) x
  refine ⟨r,hr,?_⟩
  intro s p hp hpx
  have hxs:=hNear p hpx s hp
  obtain ⟨j,rfl⟩:=(jordanPolygonSideEquiv Q).surjective s
  by_cases hji : j=i
  · exact congrArg (jordanPolygonSideEquiv Q) hji
  · exact (hv (jordanPolygon_common_sides_vertex Q (fun h=>hji h.symm) hx hxs)).elim

/-- The literal original finite Jordan polygon inside is genuinely regular open in the
actual native metric topology; this property is derived rather than imposed. -/
theorem jordanPolygon_interior_regular_open {m : ℕ} (Q : DiscPolygon m)
    :
    interior (closure (jordanDiscPoincarePolygon Q).interior)=(jordanDiscPoincarePolygon Q).interior := by
  let f : ℍ→ℂ:=fun z=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)
  have hfc : Continuous f:=Complex.UnitDisc.continuous_coe.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.continuous
  have hCo : IsOpenMap ((↑) : 𝔻→ℂ) := by
    change IsOpenMap (Subtype.val : Metric.ball (0 : ℂ) 1→ℂ)
    exact Metric.isOpen_ball.isOpenMap_subtype_val
  have hfo : IsOpenMap f:=hCo.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isOpenMap
  change interior (closure (f ⁻¹' Q.complexInterior))=f ⁻¹' Q.complexInterior
  rw [←hfo.preimage_closure_eq_closure_preimage hfc,
    ←hfo.preimage_interior_eq_interior_preimage hfc,Q.interior_closure_complexInterior]

/-- The literal original native Jordan boundary is the genuine frontier of its actual inside. -/
theorem jordanPolygon_frontier_boundary {m : ℕ} (Q : DiscPolygon m)
    :
    frontier (jordanDiscPoincarePolygon Q).interior=(jordanDiscPoincarePolygon Q).boundary := by
  let f : ℍ→ℂ:=fun z=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)
  have hfc : Continuous f:=Complex.UnitDisc.continuous_coe.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.continuous
  have hCo : IsOpenMap ((↑) : 𝔻→ℂ) := by
    change IsOpenMap (Subtype.val : Metric.ball (0 : ℂ) 1→ℂ)
    exact Metric.isOpen_ball.isOpenMap_subtype_val
  have hfo : IsOpenMap f:=hCo.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isOpenMap
  change frontier (f ⁻¹' Q.complexInterior)=_
  rw [←hfo.preimage_frontier_eq_frontier_preimage hfc,Q.frontier_complexInterior,
    jordanDiscPoincarePolygon_boundary]

/-- Every original finite nonvertex side point is in a genuine local open interval of
its supporting h-line, without global convexity of the original Jordan polygon. -/
theorem jordanPolygon_nonvertex_side_interval {m : ℕ} (Q : DiscPolygon m)
    (i : Fin m) (x : ℍ)
    (hx : x∈finitePolygonSide Q i) (hv : x∉jordanPolygonNativeVertices Q) :
    ∀ᶠy in 𝓝 x,y∈finitePolygonSide Q i ↔y∈(finitePolygonLine Q i).carrier := by
  obtain ⟨m₀,t₀,hm,hLine,hleft,hright⟩:=jordanPolygon_native_side_equation Q i
  have hOpen:=jordanPolygon_nonvertex_klein_openSegment Q hx hv
  have hB : ∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x),
      y∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' Q.boundary ↔inner ℝ m₀ y=t₀ := by
    filter_upwards [Q.klein_boundary_line_germ_edge i hOpen] with y hy
    exact hy.trans (_root_.LowDimensionalTopology.Geometry.Fuchsian.polygonLineEquation_iff_support
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (Q.vertices_injective.ne
        (Q.next_ne_self i).symm))
      hm hleft hright y)
  have hNative:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.continuous.continuousAt.eventually hB
  have hb (z : ℍ) : z∈(jordanDiscPoincarePolygon Q).boundary ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' Q.boundary := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image]
    constructor
    · rintro ⟨a,⟨j,rfl⟩,hza⟩
      exact mem_iUnion.mpr ⟨j,hza⟩
    · intro hz
      obtain ⟨j,hj⟩:=mem_iUnion.mp hz
      exact mem_sUnion.mpr ⟨finitePolygonSide Q j,mem_range_self j,hj⟩
  let x' : (jordanDiscPoincarePolygon Q).Point:=
    ⟨x,(jordanDiscPoincarePolygon Q).side_subset_carrier (jordanPolygonSideEquiv Q i) hx⟩
  obtain ⟨r,hr,hNear⟩:=jordanPolygon_nonvertex_unique_side_near Q x' i hx hv
  filter_upwards [hNative,Metric.ball_mem_nhds x hr] with y hy hd
  have hBoundary : y∈(jordanDiscPoincarePolygon Q).boundary ↔y∈(finitePolygonLine Q i).carrier:=
    (hb y).trans (hy.trans (hLine y).symm)
  apply Iff.trans ?_ hBoundary
  constructor
  · intro hys
    exact mem_sUnion.mpr ⟨finitePolygonSide Q i,mem_range_self i,hys⟩
  · intro hyB
    obtain ⟨a,ha,hya⟩:=mem_sUnion.mp hyB
    let a' : (jordanDiscPoincarePolygon Q).Side:=⟨a,ha⟩
    have he:=hNear a' y hya hd
    change y∈(jordanPolygonSideEquiv Q i).val
    exact he ▸ hya



/-- Every original finite Jordan polygon supplies all of the general native geometric
polygon data from its actual original vertices and sides, without assuming any group property. -/
def jordanPolygon_native_geometry {m : ℕ} (Q : DiscPolygon m)
    :
    NativeGeodesicPolygonGeometry (jordanDiscPoincarePolygon Q) (jordanPolygonNativeVertices Q) where
  interior_open:=jordanDiscPoincarePolygon_interior_isOpen Q
  interior_connected:=jordanDiscPoincarePolygon_interior_isConnected Q
  carrier_closure:=jordanDiscPoincarePolygon_carrier Q
  regular_open:=jordanPolygon_interior_regular_open Q
  frontier_boundary:=jordanPolygon_frontier_boundary Q
  locallyFinite:=jordanDiscPoincarePolygon_locallyFiniteSides Q
  side_closed:=jordanDiscPoincarePolygon_closedSides Q
  vertex_discrete:=jordanPolygonNativeVertices_isDiscrete Q
  line s:=finitePolygonLine Q ((jordanPolygonSideEquiv Q).symm s)
  side_subset_line:=by
    intro s
    obtain ⟨i,rfl⟩:=(jordanPolygonSideEquiv Q).surjective s
    change finitePolygonSide Q i⊆(finitePolygonLine Q ((jordanPolygonSideEquiv Q).symm
      (jordanPolygonSideEquiv Q i))).carrier
    rw [(jordanPolygonSideEquiv Q).symm_apply_apply]
    exact finitePolygonSide_subset_line Q i
  side_two_points:=by
    intro s
    obtain ⟨i,rfl⟩:=(jordanPolygonSideEquiv Q).surjective s
    exact nativeCompactifiedSide_nontrivial (Q.vertices i) (Q.vertices (finRotate m i))
      (Q.vertices_injective.ne (Q.next_ne_self i).symm)
  side_meet_vertex:=by
    intro s t hst x hx ht
    obtain ⟨i,rfl⟩:=(jordanPolygonSideEquiv Q).surjective s
    obtain ⟨j,rfl⟩:=(jordanPolygonSideEquiv Q).surjective t
    have hij : i≠j:=fun he=>hst (congrArg (jordanPolygonSideEquiv Q) he)
    exact jordanPolygon_common_sides_vertex Q hij hx ht
  side_interval:=by
    intro s x hx hv
    obtain ⟨i,rfl⟩:=(jordanPolygonSideEquiv Q).surjective s
    change ∀ᶠy in 𝓝 x,y∈finitePolygonSide Q i ↔y∈(finitePolygonLine Q
      ((jordanPolygonSideEquiv Q).symm (jordanPolygonSideEquiv Q i))).carrier
    rw [(jordanPolygonSideEquiv Q).symm_apply_apply]
    exact jordanPolygon_nonvertex_side_interval Q i x hx hv


end LowDimensionalTopology.Geometry.Polygon
