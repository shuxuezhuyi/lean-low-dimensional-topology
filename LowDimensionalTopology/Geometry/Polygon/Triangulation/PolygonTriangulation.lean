/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonCornerAngles
public import LowDimensionalTopology.External.LeanPool.ClassificationOfSurfaces.Moise.PolygonalPolyhedron
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaFinite
/-! # Genuine finite native triangulations and finite positive polygon density area

Arbitrary actual Jordan polygons, including nonconvex polygons and ideal vertices,
have actual compactified geodesic triangle covers derived from the licensed
planar mesh. No triangulation or convexity hypothesis is added. General Euler,
angle accounting and the polygon area identity remain unfinished. -/
set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Set Filter
open scoped Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- The native bounded interior agrees with the genuine bounded region of its actual Klein polygon. -/
theorem DiscPolygon.kleinPlane_image_interiorRegion {n : ℕ} (P : DiscPolygon n) :
    discPolygonKleinPlaneHomeomorph '' P.complexInterior = P.toPolygonalCircle.interiorRegion := by
  let J := P.toPolygonalCircle
  let h := discPolygonKleinPlaneHomeomorph
  have hb : h.symm '' J.carrier = P.complexBoundary := by
    rw [← P.kleinPlaneHomeomorph_image_boundary,image_image]
    change (fun x => h.symm (h x)) '' P.complexBoundary = _
    simp only [h.symm_apply_apply,image_id']
  obtain ⟨hI,hO,hd,hu,_,_⟩ := polygon_jordan_regions_image h.symm J.isOpen_interiorRegion
    J.isOpen_exteriorRegion J.disjoint_interior_exterior J.interior_union_exterior
    J.frontier_interiorRegion J.frontier_exteriorRegion
  rw [hb] at hu
  have hOc : IsConnected (h.symm '' J.exteriorRegion) :=
    J.isConnected_exteriorRegion.image h.symm h.symm.continuous.continuousOn
  have hIb : Bornology.IsBounded (h.symm '' J.interiorRegion) := by
    have hk : IsCompact (closure (h.symm '' J.interiorRegion)) := by
      rw [← h.symm.image_closure]
      exact J.isBounded_interiorRegion.isCompact_closure.image h.symm.continuous
    exact hk.isBounded.subset subset_closure
  have hOb : ¬ Bornology.IsBounded (h.symm '' J.exteriorRegion) := by
    intro hh
    have he : (h.symm '' J.interiorRegion ∪ h.symm '' J.exteriorRegion) ∪ P.complexBoundary = univ := by
      rw [hu,compl_union_self]
    apply NormedSpace.unbounded_univ ℝ ℂ
    rw [← he]
    exact (hIb.union hh).union P.complexBoundary_isCompact.isBounded
  have hp := P.interior_eq_of_jordan_regions hI hO hd hu hOc hOb
  rw [hp,image_image]
  change (fun x => h (h.symm x)) '' J.interiorRegion = _
  simp only [h.apply_symm_apply,image_id']
  rfl

/-- The actual compactified native closed polygon is exactly the closed planar Jordan region in Klein coordinates. -/
theorem DiscPolygon.kleinPlane_image_closedCarrier {n : ℕ} (P : DiscPolygon n) :
    discPolygonKleinPlane '' P.closedCarrier = P.toPolygonalCircle.closedRegion := by
  have he : discPolygonKleinPlane '' P.closedCarrier =
      discPolygonKleinPlaneHomeomorph '' closure P.complexInterior := by
    rw [← P.closedCarrier_complex_image,image_image]
    simp only [discPolygonKleinPlaneHomeomorph_closed]
  rw [he,discPolygonKleinPlaneHomeomorph.image_closure,P.kleinPlane_image_interiorRegion]
  rfl

/-- A genuine finite affine triangle mesh of the actual closed native polygon, without a triangulation hypothesis. -/
def DiscPolygon.kleinTriangleMesh {n : ℕ} (P : DiscPolygon n) :
    LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh := P.toPolygonalCircle.closedRegionMesh

/-- The mesh covers exactly the actual finite-or-ideal polygon, including all boundary points. -/
theorem DiscPolygon.kleinTriangleMesh_support {n : ℕ} (P : DiscPolygon n) :
    P.kleinTriangleMesh.toPlaneComplex.support = discPolygonKleinPlane '' P.closedCarrier := by
  rw [P.kleinPlane_image_closedCarrier]
  exact P.toPolygonalCircle.closedRegionMesh_support

/-- Affine independence of three genuine Klein vertices constructs a true native triangle. -/
def closedDiscTriangleOfPlaneIndependent (v : Fin 3 → 𝕔𝔻)
    (hv : AffineIndependent ℝ (discPolygonKleinPlane ∘
      v)) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle where
  a := v 0
  b := v 1
  c := v 2
  noncollinear := by
    rintro ⟨L,h0,h1,h2⟩
    obtain ⟨m,t,hm,he⟩ := L.closedKlein_affine_equation
    have hc : Collinear ℝ (range (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ∘ v)) := by
      apply polygonComplex_hyperplane_collinear m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (v 0)) hm (mem_range_self 0)
      rintro q ⟨i,rfl⟩
      have hi : v i ∈ L.closedCarrier := by fin_cases i <;> assumption
      change inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (v
        i)) = inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (v 0))
      rw [(he _).mp hi,(he _).mp h0]
    let e := LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv
    have hh := polygon_collinear_affine_image e.symm.toLinearEquiv.toAffineEquiv.toAffineMap hc
    rw [← range_comp] at hh
    exact (affineIndependent_iff_not_collinear.mp hv) hh

/-- Every ordered vertex used by a true mesh triangle is an actual point of the native closed polygon. -/
theorem DiscPolygon.kleinTriangleMesh_vertex_exists {n : ℕ} (P : DiscPolygon n)
    (t : P.kleinTriangleMesh.Triangle) (i : Fin 3) :
    ∃ p ∈ P.closedCarrier,discPolygonKleinPlane p =
      P.kleinTriangleMesh.position (P.kleinTriangleMesh.orderedVertex t i) := by
  have hp : P.kleinTriangleMesh.position (P.kleinTriangleMesh.orderedVertex t i) ∈
      P.kleinTriangleMesh.toPlaneComplex.support := by
    rw [LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.toPlaneComplex_support]
    refine mem_iUnion.mpr ⟨t.1,mem_iUnion.mpr ⟨t.2,subset_convexHull ℝ _ ?_⟩⟩
    exact ⟨P.kleinTriangleMesh.orderedVertex t i,P.kleinTriangleMesh.orderedVertex_mem t i,rfl⟩
  rw [P.kleinTriangleMesh_support] at hp
  exact hp

/-- Actual compactified native vertices of a genuine mesh triangle. -/
def DiscPolygon.meshTriangleVertex {n : ℕ} (P : DiscPolygon n)
    (t : P.kleinTriangleMesh.Triangle) (i : Fin 3) : 𝕔𝔻 :=
  (P.kleinTriangleMesh_vertex_exists t i).choose

theorem DiscPolygon.meshTriangleVertex_spec {n : ℕ} (P : DiscPolygon n)
    (t : P.kleinTriangleMesh.Triangle) (i : Fin 3) :
    P.meshTriangleVertex t i ∈ P.closedCarrier ∧ discPolygonKleinPlane (P.meshTriangleVertex t i) =
      P.kleinTriangleMesh.position (P.kleinTriangleMesh.orderedVertex t i) :=
  (P.kleinTriangleMesh_vertex_exists t i).choose_spec

/-- The native vertices of every actual mesh triangle are genuinely noncollinear. -/
theorem DiscPolygon.meshTriangleVertex_affineIndependent {n : ℕ} (P : DiscPolygon n)
    (t : P.kleinTriangleMesh.Triangle) :
    AffineIndependent ℝ (discPolygonKleinPlane ∘ P.meshTriangleVertex t) := by
  have he : discPolygonKleinPlane ∘ P.meshTriangleVertex t =
      P.kleinTriangleMesh.position ∘ P.kleinTriangleMesh.orderedVertex t :=
    funext (fun i => (P.meshTriangleVertex_spec t i).2)
  rw [he]
  exact P.kleinTriangleMesh.orderedVertex_affineIndependent t

/-- Every affine mesh face becomes an actual finite-or-ideal native hyperbolic triangle. -/
def DiscPolygon.meshTriangle {n : ℕ} (P : DiscPolygon n) (t : P.kleinTriangleMesh.Triangle) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle := closedDiscTriangleOfPlaneIndependent (P.meshTriangleVertex t)
      (P.meshTriangleVertex_affineIndependent t)

/-- Actual compactified hyperbolic convex hulls become genuine affine convex hulls in the planar Klein model. -/
theorem discPolygonKleinPlane_image_hConvexHull (S : Set 𝕔𝔻) :
    discPolygonKleinPlane '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvexHull S = convexHull ℝ (discPolygonKleinPlane '' S) := by
  let e := LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv
  change (fun p => e.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    p)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvexHull S = _
  rw [← image_image,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvexHull_klein_image]
  change e.symm.toLinearEquiv.toAffineEquiv.toAffineMap '' convexHull ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' S) = _
  rw [e.symm.toLinearEquiv.toAffineEquiv.toAffineMap.image_convexHull]
  rw [image_image]
  rfl

/-- Every true native mesh triangle has exactly its corresponding affine mesh face as Klein image. -/
theorem DiscPolygon.meshTriangle_klein_image {n : ℕ} (P : DiscPolygon n)
    (t : P.kleinTriangleMesh.Triangle) :
    discPolygonKleinPlane '' (P.meshTriangle t).closedCarrier =
      convexHull ℝ (P.kleinTriangleMesh.position '' (t.1 : Set P.kleinTriangleMesh.Vertex)) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.closedCarrier,discPolygonKleinPlane_image_hConvexHull]
  congr 1
  rw [← P.kleinTriangleMesh.range_orderedVertex t,← range_comp]
  ext q
  simp only [mem_image,mem_insert_iff,mem_singleton_iff,mem_range]
  constructor
  · rintro ⟨p,(rfl | rfl | rfl),he⟩
    · exact ⟨0,((P.meshTriangleVertex_spec t 0).2).symm.trans he⟩
    · exact ⟨1,((P.meshTriangleVertex_spec t 1).2).symm.trans he⟩
    · exact ⟨2,((P.meshTriangleVertex_spec t 2).2).symm.trans he⟩
  · rintro ⟨i,rfl⟩
    refine ⟨P.meshTriangleVertex t i,?_,(P.meshTriangleVertex_spec t i).2⟩
    fin_cases i <;> simp [DiscPolygon.meshTriangle,closedDiscTriangleOfPlaneIndependent]

/-- Actual true native mesh triangles cover the entire finite-or-ideal polygon, with no given triangulation hypothesis. -/
theorem DiscPolygon.closedCarrier_eq_iUnion_meshTriangles {n : ℕ} (P : DiscPolygon n) :
    P.closedCarrier = ⋃ t : P.kleinTriangleMesh.Triangle,(P.meshTriangle t).closedCarrier := by
  apply discPolygonKleinPlane_injective.image_injective
  rw [image_iUnion]
  simp_rw [P.meshTriangle_klein_image]
  rw [← P.kleinTriangleMesh_support,
    LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.toPlaneComplex_support]
  ext q
  simp only [mem_iUnion]
  constructor
  · rintro ⟨t,ht,hq⟩
    exact ⟨⟨t,ht⟩,hq⟩
  · rintro ⟨t,hq⟩
    exact ⟨t.1,t.2,hq⟩

/-- Every genuine native mesh triangle stays inside the actual closed polygon. -/
theorem DiscPolygon.meshTriangle_subset_closedCarrier {n : ℕ} (P : DiscPolygon n)
    (t : P.kleinTriangleMesh.Triangle) : (P.meshTriangle t).closedCarrier ⊆ P.closedCarrier := by
  rw [P.closedCarrier_eq_iUnion_meshTriangles]
  exact fun p hp => mem_iUnion.mpr ⟨t,hp⟩

/-- The finite part of the actual closed polygon is measurable. -/
theorem DiscPolygon.closedCarrier_finite_measurable {n : ℕ} (P : DiscPolygon n) :
    MeasurableSet {z : 𝔻 | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈ P.closedCarrier} :=
  (P.closedCarrier_isClosed.preimage
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.continuous).measurableSet

/-- The finite part of the actual closed polygon has finite genuine hyperbolic density area, even with ideal vertices. -/
theorem DiscPolygon.closedCarrier_area_lt_top {n : ℕ} (P : DiscPolygon n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea {z : 𝔻 | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈ P.closedCarrier} < ⊤ := by
  have hc : {z : 𝔻 | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈ P.closedCarrier} =
      ⋃ t : P.kleinTriangleMesh.Triangle,{z : 𝔻 | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈ (P.meshTriangle t).closedCarrier} := by
    ext z
    rw [P.closedCarrier_eq_iUnion_meshTriangles]
    simp only [mem_ofPred_eq,mem_iUnion]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea,hc,image_iUnion]
  have hh := MeasureTheory.measure_biUnion_lt_top (μ :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discAreaMeasure)
    (s := (univ : Set P.kleinTriangleMesh.Triangle))
    (f := fun t => ((↑) : 𝔻 → ℂ) '' {z : 𝔻 | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈
      (P.meshTriangle t).closedCarrier})
    (Set.toFinite _) (fun t _ => by
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea {z : 𝔻 |
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈ (P.meshTriangle t).closedCarrier} < ⊤
      rw [(P.meshTriangle t).closedCarrier_area_eq_angle_defect]
      exact ENNReal.ofReal_lt_top)
  simpa using hh

/-- Every actual native Jordan polygon has finite genuine hyperbolic area. -/
theorem DiscPolygon.area_lt_top {n : ℕ} (P : DiscPolygon n) : P.area < ⊤ := by
  apply lt_of_le_of_lt (MeasureTheory.measure_mono (image_mono (show P.interior ⊆
    {z : 𝔻 | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈
      P.closedCarrier} from ?_))) P.closedCarrier_area_lt_top
  intro z hz
  exact subset_closure (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel hz)

/-- Every actual native Jordan polygon has strictly positive genuine density area. -/
theorem DiscPolygon.area_pos {n : ℕ} (P : DiscPolygon n) : 0 < P.area := by
  let polygonTriangulationNativeMetric : MetricSpace 𝔻 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  obtain ⟨q,hq⟩ := P.interior_isConnected.nonempty
  obtain ⟨r,hr,hrP⟩ := Metric.isOpen_iff.mp P.interior_isOpen q hq
  have hs : {z : 𝔻 | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist q z ≤ r/2} ⊆ P.interior := by
    intro z hz
    apply hrP
    change dist z q < r
    rw [dist_comm,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance]
    exact lt_of_le_of_lt hz (by linarith)
  have hpos : 0 < _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea {z : 𝔻 | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist q z ≤ r/2} := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea_closedBall q (r/2) (by positivity)]
    apply ENNReal.ofReal_pos.mpr
    have hh : 0 < Real.sinh (r/2/2) := Real.sinh_pos_iff.mpr (by positivity)
    positivity
  exact lt_of_lt_of_le hpos (MeasureTheory.measure_mono (image_mono hs))

/-- The genuine finite native mesh has at least one actual triangle. -/
theorem DiscPolygon.kleinTriangleMesh_nonempty {n : ℕ} (P : DiscPolygon n) :
    Nonempty P.kleinTriangleMesh.Triangle := by
  obtain ⟨q,hq⟩ := P.interior_isConnected.nonempty
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q ∈ P.closedCarrier := subset_closure (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel hq)
  rw [P.closedCarrier_eq_iUnion_meshTriangles] at hc
  obtain ⟨t,_⟩ := mem_iUnion.mp hc
  exact ⟨t⟩

end
end LowDimensionalTopology.Geometry.Polygon
