/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Polygon.Triangulation.PolygonTriangulation
public import LowDimensionalTopology.External.LeanPool.ClassificationOfSurfaces.Moise.FreeTriangle
/-! # Genuine native polygon density area and derived mesh additivity

Every boundary and overlap is handled in the actual hyperbolic density measure.
These results prove genuine area additivity for the derived true finite mesh;
Euler and the original polygon corner-angle accounting remain unfinished. -/
set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Set Filter MeasureTheory
open scoped Topology Complex.UnitDisc UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- The genuine complete native support of an actual polygon edge, including ideal endpoints. -/
def DiscPolygon.edgeSupport {n : ℕ} (P : DiscPolygon n) (i : Fin
  n) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_discLine_closedCarrier (P.vertices i) (P.vertices
    (finRotate n i))
    (P.vertices_injective.ne (Ne.symm (P.next_ne_self i)))).exists.choose

theorem DiscPolygon.edgeSupport_incident {n : ℕ} (P : DiscPolygon n) (i : Fin n) :
    P.vertices i ∈ (P.edgeSupport i).closedCarrier ∧
      P.vertices (finRotate n i) ∈ (P.edgeSupport i).closedCarrier :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_discLine_closedCarrier (P.vertices i) (P.vertices
    (finRotate n i))
    (P.vertices_injective.ne (Ne.symm (P.next_ne_self i)))).exists.choose_spec

/-- The actual finite-or-ideal edge lies in its actual complete geodesic. -/
theorem DiscPolygon.edge_subset_support {n : ℕ} (P : DiscPolygon n) (i : Fin n) :
    discPolygonEdge P.vertices i ⊆ (P.edgeSupport i).closedCarrier := by
  have hp := (P.edgeSupport_incident i).1
  have hq := (P.edgeSupport_incident i).2
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment _ _ ⊆ _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_eq_arcHull (P.edgeSupport i) _ _
    (P.vertices_injective.ne (Ne.symm (P.next_ne_self i))) hp hq]
  intro p hx
  exact hx _ (P.edgeSupport i).closedCarrier_isPreconnected subset_rfl hp hq

/-- The entire actual polygon boundary is null for the genuine hyperbolic density volume. -/
theorem DiscPolygon.boundary_halfPlane_volume_zero {n : ℕ} (P : DiscPolygon n) :
    volume {z : ℍ | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) ∈ P.boundary} = 0 := by
  have hs : {z : ℍ | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) ∈ P.boundary} ⊆
      ⋃ i : Fin n,(P.edgeSupport i).toHalfPlane.carrier := by
    intro z hz
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) ∈ ⋃ i,discPolygonEdge P.vertices i at hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    have hh := P.edge_subset_support i hi
    rw [(P.edgeSupport i).closedCarrier_mem_interior_iff,(P.edgeSupport i).mem_carrier,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] at hh
    exact mem_iUnion.mpr ⟨i,hh⟩
  exact measure_mono_null hs (measure_iUnion_null (fun i => (P.edgeSupport i).toHalfPlane.volume_zero))

/-- Closing the genuine polygon adds only an actual density-null geodesic boundary. -/
theorem DiscPolygon.halfPlane_closedCarrier_ae_eq_interior {n : ℕ} (P : DiscPolygon n) :
    {z : ℍ | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) ∈ P.closedCarrier} =ᵐ[volume]
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' P.interior) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp P.boundary_halfPlane_volume_zero] with z hz
  apply propext
  constructor
  · intro hc
    have hh : ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : 𝔻) : ℂ) ∈ closure P.complexInterior := by
      rw [← P.closedCarrier_complex_image]
      exact mem_image_of_mem ((↑) : 𝕔𝔻 → ℂ) hc
    rw [P.closure_complexInterior] at hh
    rcases hh with hi | hb
    · exact hi
    · obtain ⟨p,hp,hpe⟩ := hb
      have he : p = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) := Complex.UnitClosedDisc.coe_injective hpe
      exact (hz (he ▸ hp)).elim
  · intro hi
    exact subset_closure (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel hi)

/-- Closing the true native polygon does not change its actual density volume. -/
theorem DiscPolygon.halfPlane_closedCarrier_volume_eq_interior {n : ℕ} (P : DiscPolygon n) :
    volume {z : ℍ | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) ∈ P.closedCarrier} =
      volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹'
        P.interior) := measure_congr P.halfPlane_closedCarrier_ae_eq_interior

/-- The native polygon area is exactly the actual upper half-plane density volume. -/
theorem DiscPolygon.area_eq_halfPlane_volume {n : ℕ} (P : DiscPolygon n) :
    P.area = volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' P.interior) := by
  rw [DiscPolygon.area,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea_eq_halfPlane_volume _
    P.interior_measurable]
  congr 1
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) ∈ P.interior
    rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  · intro hz
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
      z,hz,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc z⟩

/-- The triangle viewed as a native polygon has exactly the same genuine compactified closed carrier. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.toDiscPolygon_closedCarrier (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    T.toDiscPolygon.closedCarrier = T.closedCarrier := by
  rw [DiscPolygon.closedCarrier,T.toDiscPolygon_interior,← T.closedCarrier_eq_closedModelClosure]

/-- The finite closed native triangle and its true interior agree almost everywhere in actual density volume. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.halfPlane_closedCarrier_ae_eq_interior (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    {z : ℍ | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) ∈ T.closedCarrier} =ᵐ[volume] T.halfPlaneInterior := by
  have hh := T.toDiscPolygon.halfPlane_closedCarrier_ae_eq_interior
  rw [T.toDiscPolygon_closedCarrier,T.toDiscPolygon_interior] at hh
  exact hh

/-- The true interior of each native mesh triangle maps exactly to the actual affine face interior. -/
theorem DiscPolygon.meshTriangle_plane_image_interior {n : ℕ} (P : DiscPolygon n)
    (t : P.kleinTriangleMesh.Triangle) :
    discPolygonKleinPlaneHomeomorph '' (P.meshTriangle t).complexInterior =
      _root_.interior (P.kleinTriangleMesh.triangleCarrier t.1) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.complexInterior,discPolygonKleinPlaneHomeomorph.image_interior]
  congr 1
  change discPolygonKleinPlaneHomeomorph '' (((↑) : 𝕔𝔻 → ℂ) '' (P.meshTriangle t).closedCarrier) = _
  rw [image_image]
  simp only [discPolygonKleinPlaneHomeomorph_closed]
  exact P.meshTriangle_klein_image t

/-- Distinct true mesh faces have disjoint actual native interiors. -/
theorem DiscPolygon.meshTriangle_halfPlaneInterior_pairwise_disjoint {n : ℕ} (P : DiscPolygon n) :
    Pairwise (fun t u : P.kleinTriangleMesh.Triangle =>
      Disjoint (P.meshTriangle t).halfPlaneInterior (P.meshTriangle u).halfPlaneInterior) := by
  intro t u htu
  apply Set.disjoint_left.mpr
  intro z hzt hzu
  have ht : discPolygonKleinPlaneHomeomorph ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : 𝔻) :
    ℂ) ∈
      _root_.interior (P.kleinTriangleMesh.triangleCarrier t.1) := by
    rw [← P.meshTriangle_plane_image_interior]
    exact mem_image_of_mem discPolygonKleinPlaneHomeomorph hzt
  have hu : discPolygonKleinPlaneHomeomorph ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : 𝔻) :
    ℂ) ∈
      _root_.interior (P.kleinTriangleMesh.triangleCarrier u.1) := by
    rw [← P.meshTriangle_plane_image_interior]
    exact mem_image_of_mem discPolygonKleinPlaneHomeomorph hzu
  exact Set.disjoint_left.mp (P.kleinTriangleMesh.disjoint_interior_triangleCarrier
    (Subtype.coe_injective.ne htu)) ht hu

/-- Shared true native mesh boundaries are density-null, so the closed face carriers are pairwise almost disjoint. -/
theorem DiscPolygon.meshTriangle_halfPlane_closedCarrier_pairwise_aedisjoint {n : ℕ} (P : DiscPolygon n) :
    Pairwise (fun t u : P.kleinTriangleMesh.Triangle => AEDisjoint volume
      {z : ℍ | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) ∈ (P.meshTriangle t).closedCarrier}
      {z : ℍ | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) ∈ (P.meshTriangle u).closedCarrier}) := by
  intro t u htu
  exact (P.meshTriangle_halfPlaneInterior_pairwise_disjoint htu).aedisjoint.congr
    (P.meshTriangle t).halfPlane_closedCarrier_ae_eq_interior
    (P.meshTriangle u).halfPlane_closedCarrier_ae_eq_interior

/-- Actual polygon density area is the sum of the areas of its derived finite true triangle mesh. -/
theorem DiscPolygon.area_eq_tsum_meshTriangle_area {n : ℕ} (P : DiscPolygon n) :
    P.area = ∑' t : P.kleinTriangleMesh.Triangle,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (P.meshTriangle t).interior := by
  have hc : {z : ℍ | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) ∈ P.closedCarrier} =
      ⋃ t : P.kleinTriangleMesh.Triangle,
        {z : ℍ | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) ∈ (P.meshTriangle t).closedCarrier} := by
    ext z
    rw [P.closedCarrier_eq_iUnion_meshTriangles]
    simp only [mem_ofPred_eq,mem_iUnion]
  rw [P.area_eq_halfPlane_volume,← P.halfPlane_closedCarrier_volume_eq_interior,hc]
  rw [measure_iUnion₀ P.meshTriangle_halfPlane_closedCarrier_pairwise_aedisjoint]
  · apply tsum_congr
    intro t
    rw [(P.meshTriangle t).halfPlane_closedCarrier_area_eq_interior,← (P.meshTriangle t).area_eq_halfPlane_volume]
  · intro t
    have hm := (P.meshTriangle t).closedCarrier_finite_measurable.preimage _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.continuous.measurable
    exact hm.nullMeasurableSet

/-- The derived true triangle angle defects sum exactly to the genuine density area of an arbitrary polygon. -/
theorem DiscPolygon.area_eq_tsum_meshTriangle_angle_defects {n : ℕ} (P : DiscPolygon n) :
    P.area = ∑' t : P.kleinTriangleMesh.Triangle,
      ENNReal.ofReal (Real.pi-(P.meshTriangle t).alpha-(P.meshTriangle t).beta-(P.meshTriangle t).gamma) := by
  rw [P.area_eq_tsum_meshTriangle_area]
  exact tsum_congr (fun t => (P.meshTriangle t).area_eq_angle_defect)

/-- The genuine density area equals the ordinary finite sum over the derived true triangle mesh. -/
theorem DiscPolygon.area_eq_sum_meshTriangle_area {n : ℕ} (P : DiscPolygon n) :
    P.area = ∑ t : P.kleinTriangleMesh.Triangle,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (P.meshTriangle t).interior := by
  rw [P.area_eq_tsum_meshTriangle_area,tsum_fintype]

/-- The real genuine area is the finite sum of actual triangle angle defects, without truncation. -/
theorem DiscPolygon.area_toReal_eq_sum_meshTriangle_angle_defects {n : ℕ} (P : DiscPolygon n) :
    P.area.toReal = ∑ t : P.kleinTriangleMesh.Triangle,
      (Real.pi-(P.meshTriangle t).alpha-(P.meshTriangle t).beta-(P.meshTriangle t).gamma) := by
  rw [P.area_eq_sum_meshTriangle_area,ENNReal.toReal_sum]
  · exact Finset.sum_congr rfl (fun t _ => (P.meshTriangle t).area_toReal_eq_angle_defect)
  · intro t _
    exact ne_of_lt (P.meshTriangle t).area_pos_lt_top.2

end
end LowDimensionalTopology.Geometry.Polygon
