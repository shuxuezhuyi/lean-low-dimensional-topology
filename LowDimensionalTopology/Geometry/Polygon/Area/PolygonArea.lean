/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the adapted planar mesh frontier argument: Ryan McCorvie, Jack McCarthy
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Polygon.Triangulation.PolygonMeshStraightAngles
public import LowDimensionalTopology.Geometry.Polygon.Triangulation.PolygonMeshBoundaryEuler
public import Mathlib.Analysis.Convex.Strict.Extreme
public import LowDimensionalTopology.Geometry.Polygon.Tangential.PolygonTangentialPolygons

/-! # Exact native polygon area and prescribed-angle criterion

The original finite-or-ideal Jordan polygon determines its own genuine mesh.
Its actual corner angles, including reflex and straight corners, yield the
unconditional area formula. Additional boundary mesh vertices contribute pi;
any omitted original corner is necessarily straight and has zero turning.
The strict angle-sum bound completes the exact convex realization criterion.

The short used-vertex frontier decomposition adapts the existing LeanPool
frontier argument; all imported original copyrights and licenses are retained.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped Complex.UnitDisc Classical ENNReal
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

theorem DiscPolygon.meshNativeVertex_mem_boundary_iff {n : ℕ} (P : DiscPolygon n)
    (v : P.UsedMeshVertex) :
    P.meshNativeVertex v ∈ P.boundary ↔ v.1 ∈ P.kleinTriangleMesh.boundaryVertices := by
  rw [LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.boundaryVertices,
    Finset.mem_filter]
  simp only [v.property, true_and]
  have hs : P.kleinTriangleMesh.toPlaneComplex.support = P.toPolygonalCircle.closedRegion :=
    P.kleinTriangleMesh_support.trans P.kleinPlane_image_closedCarrier
  rw [hs,P.toPolygonalCircle.frontier_closedRegion,P.toPolygonalCircle_carrier,
    ← (P.usedMeshVertex_spec v.1 v.2).2]
  exact discPolygonKleinPlane_injective.mem_set_image.symm

theorem DiscPolygon.boundary_openEdge_of_not_vertex {n : ℕ} (P : DiscPolygon n)
    (p : 𝕔𝔻) (hp : p ∈ P.boundary) (hv : ∀ i, p ≠ P.vertices i) :
    ∃ i : Fin n, _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p ∈ openSegment ℝ
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i))) := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp hp
  have hk := mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate hi
  rw [discPolygonEdge,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment] at hk
  exact ⟨i,mem_openSegment_of_ne_left_right
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (hv i).symm)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (hv (finRotate n i)).symm) hk⟩

theorem DiscPolygon.ideal_boundary_is_vertex {n : ℕ} (P : DiscPolygon n)
    (p : 𝕔𝔻) (hp : p ∈ P.boundary) (hnorm : ‖(p : ℂ)‖ = 1) :
    ∃ i : Fin n, p = P.vertices i := by
  by_contra h
  push Not at h
  obtain ⟨i,hi⟩ := P.boundary_openEdge_of_not_vertex p hp h
  have ha : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
    i) ∈ Metric.closedBall (0 : ℂ) 1 :=
    mem_closedBall_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein _).norm_le_one
  have hb : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n
    i)) ∈ Metric.closedBall (0 : ℂ) 1 :=
    mem_closedBall_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein _).norm_le_one
  have hab : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
    i) ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i)) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (P.vertices_injective.ne
      (P.next_ne_self i).symm)
  have hh := (strictConvex_closedBall ℝ (0 : ℂ) 1).openSegment_subset ha hb hab hi
  rw [interior_closedBall (0 : ℂ) one_ne_zero] at hh
  have he := (norm_closedKleinCoordinate_eq_one_iff p).mpr hnorm
  simp only [Metric.mem_ball,dist_zero_right,he,lt_self_iff_false] at hh

theorem DiscPolygon.meshAngleSumAt_of_added_finite_boundary {n : ℕ} (P : DiscPolygon n)
    (v : P.UsedMeshVertex) (z : 𝔻) (hz : P.meshNativeVertex v =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hp : P.meshNativeVertex v ∈ P.boundary)
    (hv : ∀ i, P.meshNativeVertex v ≠ P.vertices i) : P.meshAngleSumAt v = Real.pi := by
  obtain ⟨i,hi⟩ := P.boundary_openEdge_of_not_vertex (P.meshNativeVertex v) hp hv
  rw [hz] at hi
  exact P.meshAngleSumAt_of_edge_interior v i z hz hi

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.ideal_mem_closedCarrier_is_corner (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle)
    (p : 𝕔𝔻) (hp : p ∈ T.closedCarrier) (hnorm : ‖(p : ℂ)‖ = 1) :
    ∃ i : Fin 3, p = T.cornerVertex i := by
  have hHull : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p ∈ convexHull ℝ
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' ({T.a,T.b,T.c} : Set 𝕔𝔻)) := by
    rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvexHull_klein_image]
    exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate hp
  have hSub : convexHull ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' ({T.a,T.b,T.c} :
    Set 𝕔𝔻)) ⊆
      Metric.closedBall (0 : ℂ) 1 := by
    apply convexHull_min ?_ (convex_closedBall (0 : ℂ) 1)
    rintro q ⟨w,hw,rfl⟩
    exact mem_closedBall_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein
      _).norm_le_one
  have hExtreme : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p ∈ (Metric.closedBall (0 : ℂ) 1).extremePoints ℝ := by
    apply StrictConvexSpace.sphere_subset_extremePoints_closedBall (0 : ℂ) one_ne_zero
    exact (mem_sphere_zero_iff_norm).mpr ((norm_closedKleinCoordinate_eq_one_iff p).mpr hnorm)
  have hHullEx := inter_extremePoints_subset_extremePoints_of_subset hSub ⟨hHull,hExtreme⟩
  obtain ⟨w,hw,he⟩ := extremePoints_convexHull_subset hHullEx
  have hwp := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective he
  rcases hw with rfl | rfl | rfl
  · exact ⟨0,hwp.symm⟩
  · exact ⟨1,hwp.symm⟩
  · exact ⟨2,hwp.symm⟩

/-- Every genuine ideal point of the closed polygon is a vertex of the actual derived mesh. -/
theorem DiscPolygon.ideal_closedCarrier_is_usedMeshVertex {n : ℕ} (P : DiscPolygon n)
    (p : 𝕔𝔻) (hp : p ∈ P.closedCarrier) (hnorm : ‖(p : ℂ)‖ = 1) :
    ∃ v : P.UsedMeshVertex, P.meshNativeVertex v = p := by
  rw [P.closedCarrier_eq_iUnion_meshTriangles] at hp
  obtain ⟨t,ht⟩ := mem_iUnion.mp hp
  obtain ⟨i,hi⟩ := (P.meshTriangle t).ideal_mem_closedCarrier_is_corner p ht hnorm
  let v : P.UsedMeshVertex := ⟨P.kleinTriangleMesh.orderedVertex t i,
    P.kleinTriangleMesh.mem_usedVertices.mpr
      ⟨t.1,t.2,P.kleinTriangleMesh.orderedVertex_mem t i⟩⟩
  refine ⟨v,?_⟩
  exact (P.usedMeshVertex_eq_meshTriangleVertex v.1 v.2 t i rfl).trans
    ((P.meshTriangle_cornerVertex_eq t i).symm.trans hi.symm)

/-- A frontier point avoiding the used vertices lies in an actual open boundary edge. -/
theorem mesh_frontier_open_boundaryEdge
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    {p : LeanEval.Topology.ClassificationOfSurfaces.Moise.Plane}
    (hp : p ∈ frontier M.toPlaneComplex.support)
    (hv : ∀ v ∈ M.usedVertices, p ≠ M.position v) :
    ∃ a b : M.Vertex, a ≠ b ∧
      segment ℝ (M.position a) (M.position b) ⊆ frontier M.toPlaneComplex.support ∧
      p ∈ openSegment ℝ (M.position a) (M.position b) := by
  have hpUnion : p ∈ frontier (⋃ t ∈ M.triangles, M.triangleCarrier t) := by
    rw [M.toPlaneComplex_support] at hp
    exact hp
  have hpf := M.frontier_biUnion_subset M.triangles hpUnion
  obtain ⟨t,ht,hpt⟩ := mem_iUnion₂.mp hpf
  obtain ⟨e,hecard,het,hpe⟩ := M.exists_edge_of_mem_frontier_triangle ht hpt
  have hNo : p ∉ M.position '' (e : Set M.Vertex) := by
    rintro ⟨v,hve,he⟩
    exact hv v (M.mem_usedVertices.mpr ⟨t,ht,het hve⟩) he.symm
  have hBoundary : M.IsBoundaryEdge e := by
    by_contra hn
    have hint := M.edgeCarrier_diff_vertices_subset_interior_support ht hecard het hn ⟨hpe,hNo⟩
    exact disjoint_interior_frontier.le_bot ⟨hint,hp⟩
  have hSub := M.boundaryEdgeCarrier_subset_frontier hBoundary
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hecard
  have hSeg : convexHull ℝ (M.position '' (({a,b} : Finset M.Vertex) : Set M.Vertex)) =
      segment ℝ (M.position a) (M.position b) := by
    simp only [Finset.coe_insert,Finset.coe_singleton,image_insert_eq,image_singleton,convexHull_pair]
  rw [hSeg] at hpe hSub
  refine ⟨a,b,hab,hSub,mem_openSegment_of_ne_left_right ?_ ?_ hpe⟩
  · exact (hv a (M.mem_usedVertices.mpr ⟨t,ht,het (by simp)⟩)).symm
  · exact (hv b (M.mem_usedVertices.mpr ⟨t,ht,het (by simp)⟩)).symm

/-- A straight boundary segment through a genuine Jordan vertex forces its two incident sides to be collinear. -/
theorem polygonalCircle_collinear_of_boundary_openSegment
    (J : LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (i : ZMod J.n) {a b : LeanEval.Topology.ClassificationOfSurfaces.Moise.Plane}
    (hab : a ≠ b) (hs : segment ℝ a b ⊆ J.carrier)
    (hi : J.vertex i ∈ openSegment ℝ a b) :
    Collinear ℝ ({J.vertex (i-1),J.vertex i,J.vertex (i+1)} : Set _) := by
  let L := affineSpan ℝ ({a,b} : Set _)
  have hBase : segment ℝ a b ⊆ L :=
    L.convex.segment_subset (subset_affineSpan ℝ _ (by simp)) (subset_affineSpan ℝ _ (by simp))
  have hCenter : J.vertex i ∈ L := hBase (openSegment_subset_segment ℝ _ _ hi)
  obtain ⟨⟨y,hy,hyB,hyE⟩,⟨z,hz,hzB,hzE⟩⟩ := J.exists_basePoints_on_incident_edges hab hs hi
  have hNext : J.vertex (i+1) ∈ L := by
    have hyLine : y ∈ affineSpan ℝ ({J.vertex i,J.vertex (i+1)} : Set _) :=
      (affineSpan ℝ ({J.vertex i,J.vertex (i+1)} : Set _)).convex.segment_subset
        (subset_affineSpan ℝ _ (by simp)) (subset_affineSpan ℝ _ (by simp)) hyE
    have hc := collinear_insert_of_mem_affineSpan_pair hyLine
    have hn := hc.mem_affineSpan_of_mem_of_ne (by simp : J.vertex i ∈ ({y,J.vertex i,J.vertex (i+1)} : Set _))
      (by simp : y ∈ ({y,J.vertex i,J.vertex (i+1)} : Set _))
      (by simp : J.vertex (i+1) ∈ ({y,J.vertex i,J.vertex (i+1)} : Set _)) hy.symm
    exact (affineSpan_le.mpr (by
      rintro q (rfl | rfl)
      · exact hCenter
      · exact hBase hyB) : affineSpan ℝ ({J.vertex i,y} : Set _) ≤ L) hn
  have hPrev : J.vertex (i-1) ∈ L := by
    have hzLine : z ∈ affineSpan ℝ ({J.vertex (i-1),J.vertex i} : Set _) := by
      have hh : z ∈ segment ℝ (J.vertex (i-1)) (J.vertex i) := by
        simpa only [LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.edgeSegment,sub_add_cancel] using hzE
      exact (affineSpan ℝ ({J.vertex (i-1),J.vertex i} : Set _)).convex.segment_subset
        (subset_affineSpan ℝ _ (by simp)) (subset_affineSpan ℝ _ (by simp)) hh
    have hc := collinear_insert_of_mem_affineSpan_pair hzLine
    have hn := hc.mem_affineSpan_of_mem_of_ne (by simp : J.vertex i ∈ ({z,J.vertex (i-1),J.vertex i} : Set _))
      (by simp : z ∈ ({z,J.vertex (i-1),J.vertex i} : Set _))
      (by simp : J.vertex (i-1) ∈ ({z,J.vertex (i-1),J.vertex i} : Set _)) hz.symm
    exact (affineSpan_le.mpr (by
      rintro q (rfl | rfl)
      · exact hCenter
      · exact hBase hzB) : affineSpan ℝ ({J.vertex i,z} : Set _) ≤ L) hn
  exact (collinear_insert_insert_insert_of_mem_affineSpan_pair hPrev hCenter hNext).subset (by
    intro q hq
    simp only [mem_insert_iff,mem_singleton_iff] at hq ⊢
    tauto)

theorem DiscPolygon.klein_neighbors_collinear_of_not_usedMeshVertex {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (hv : ∀ v : P.UsedMeshVertex, P.meshNativeVertex v ≠ P.vertices i) :
    Collinear ℝ ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices ((finRotate
      n).symm i)),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i),_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i))} : Set ℂ) := by
  let J := P.toPolygonalCircle
  let M := P.kleinTriangleMesh
  have hSupport : M.toPlaneComplex.support = J.closedRegion :=
    P.kleinTriangleMesh_support.trans P.kleinPlane_image_closedCarrier
  have hCenter : J.vertex (P.jordanIndexEquiv i) = discPolygonKleinPlane (P.vertices i) := by
    change discPolygonKleinPlane (P.vertices (P.jordanIndexEquiv.symm (P.jordanIndexEquiv i))) = _
    rw [Equiv.symm_apply_apply]
  have hp : discPolygonKleinPlane (P.vertices i) ∈ frontier M.toPlaneComplex.support := by
    rw [hSupport,J.frontier_closedRegion,← hCenter]
    exact J.vertex_mem_carrier _
  have hAvoid : ∀ v ∈ M.usedVertices, discPolygonKleinPlane (P.vertices i) ≠ M.position v := by
    intro v hused he
    apply hv ⟨v,hused⟩
    apply discPolygonKleinPlane_injective
    exact (P.usedMeshVertex_spec v hused).2.trans he.symm
  obtain ⟨a,b,hab,hs,hi⟩ := mesh_frontier_open_boundaryEdge M hp hAvoid
  rw [hSupport,J.frontier_closedRegion] at hs
  rw [← hCenter] at hi
  have hcJ := polygonalCircle_collinear_of_boundary_openSegment J (P.jordanIndexEquiv i)
    (M.position_injective.ne hab) hs hi
  let e := LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv
  have hc := polygon_collinear_affine_image e.toLinearEquiv.toAffineEquiv.toAffineMap hcJ
  simp only [image_insert_eq,image_singleton] at hc
  have hPrev := P.jordanIndexEquiv_sub_one (P.jordanIndexEquiv i)
  rw [Equiv.symm_apply_apply] at hPrev
  have hNext := P.jordanIndexEquiv_add_one (P.jordanIndexEquiv i)
  rw [Equiv.symm_apply_apply] at hNext
  change Collinear ℝ ({e (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i-(1 : ZMod n))),
    e (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i)),
    e (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i+(1 : ZMod n)))} : Set ℂ) at hc
  dsimp only [e] at hc
  simpa only [P.toPolygonalCircle_complex_vertex,hPrev,hNext,Equiv.symm_apply_apply] using hc

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.klein_vertices_not_collinear (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    ¬ Collinear ℝ ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.b,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.c} : Set ℂ) := by
  intro hc
  have hh := polygon_collinear_affine_image T.coordinateAffine hc
  simp only [image_insert_eq,image_singleton] at hh
  change Collinear ℝ ({T.coordinate T.b,T.coordinate T.a,T.coordinate T.c} : Set (ℝ × ℝ)) at hh
  rw [T.coordinate_a,T.coordinate_b,T.coordinate_c] at hh
  have hm := hh.mem_affineSpan_of_mem_of_ne
    (by simp : ((1,0) : ℝ × ℝ) ∈ ({(1,0),(0,0),(0,1)} : Set (ℝ × ℝ)))
    (by simp : ((0,0) : ℝ × ℝ) ∈ ({(1,0),(0,0),(0,1)} : Set (ℝ × ℝ)))
    (by simp : ((0,1) : ℝ × ℝ) ∈ ({(1,0),(0,0),(0,1)} : Set (ℝ × ℝ))) (by norm_num)
  obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hm
  have hh := congrArg Prod.snd ht
  norm_num [AffineMap.lineMap_apply] at hh

theorem DiscPolygon.angle_eq_pi_of_not_usedMeshVertex {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (hv : ∀ v : P.UsedMeshVertex, P.meshNativeVertex v ≠ P.vertices i) :
    P.angle i = Real.pi := by
  have hc := P.klein_neighbors_collinear_of_not_usedMeshVertex i hv
  have hi : ‖(P.vertices i : ℂ)‖ < 1 := by
    by_contra hn
    have he : ‖(P.vertices i : ℂ)‖ = 1 := le_antisymm (P.vertices i).norm_le_one (not_lt.mp hn)
    exact P.klein_neighbors_not_collinear_of_ideal i he hc
  let z := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (P.vertices i) hi
  have hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ hi).symm
  have hSame : (P.cornerRayPrev i z hz).supportLine = (P.cornerRayNext i z hz).supportLine := by
    by_contra hne
    exact (P.properCornerTriangle i z hz hne).klein_vertices_not_collinear hc
  exact P.angle_eq_pi_of_same_support i z hz hSame

theorem DiscPolygon.meshAngleSumAt_of_added_boundary {n : ℕ} (P : DiscPolygon n)
    (v : P.UsedMeshVertex) (hp : P.meshNativeVertex v ∈ P.boundary)
    (hv : ∀ i, P.meshNativeVertex v ≠ P.vertices i) : P.meshAngleSumAt v = Real.pi := by
  have hi : ‖(P.meshNativeVertex v : ℂ)‖ < 1 := by
    by_contra hn
    have he := le_antisymm (P.meshNativeVertex v).norm_le_one (not_lt.mp hn)
    obtain ⟨i,heq⟩ := P.ideal_boundary_is_vertex (P.meshNativeVertex v) hp he
    exact hv i heq
  let z := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (P.meshNativeVertex v) hi
  have hz : P.meshNativeVertex v = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ hi).symm
  exact P.meshAngleSumAt_of_added_finite_boundary v z hz hp hv

def DiscPolygon.meshBoundaryTurning {n : ℕ} (P : DiscPolygon n) (v : P.UsedMeshVertex) : ℝ :=
  if P.meshNativeVertex v ∈ P.boundary then Real.pi-P.meshAngleSumAt v else 0

theorem DiscPolygon.meshBoundaryTurning_of_original {n : ℕ} (P : DiscPolygon n)
    (v : P.UsedMeshVertex) (i : Fin n) (hv : P.meshNativeVertex v = P.vertices i) :
    P.meshBoundaryTurning v = Real.pi-P.angle i := by
  have hb : P.meshNativeVertex v ∈ P.boundary := hv ▸ mem_iUnion.mpr ⟨i,closedModelDiscHSegment_left_mem _ _⟩
  rw [DiscPolygon.meshBoundaryTurning,ite_eq_left hb,P.meshAngleSumAt_of_original_corner v i hv]

theorem DiscPolygon.meshBoundaryTurning_eq_zero_of_not_original {n : ℕ} (P : DiscPolygon n)
    (v : P.UsedMeshVertex) (hv : ∀ i, P.meshNativeVertex v ≠ P.vertices i) :
    P.meshBoundaryTurning v = 0 := by
  unfold DiscPolygon.meshBoundaryTurning
  split_ifs with hb
  · rw [P.meshAngleSumAt_of_added_boundary v hb hv,sub_self]
  · rfl

theorem DiscPolygon.sum_meshBoundaryTurning {n : ℕ} (P : DiscPolygon n) :
    ∑ v : P.UsedMeshVertex,P.meshBoundaryTurning v = ∑ i : Fin n,(Real.pi-P.angle i) := by
  symm
  have hExists (i : Fin n) (hi : Real.pi-P.angle i ≠ 0) :
      ∃ v : P.UsedMeshVertex, P.meshNativeVertex v = P.vertices i := by
    by_contra hn
    push Not at hn
    exact hi (by rw [P.angle_eq_pi_of_not_usedMeshVertex i hn,sub_self])
  let j (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) (hi : Real.pi-P.angle i ≠ 0) :=
    (hExists i hi).choose
  have hj (i : Fin n) (him : i ∈ (Finset.univ : Finset (Fin n))) (hi : Real.pi-P.angle i ≠ 0) :
      P.meshNativeVertex (j i him hi) = P.vertices i := (hExists i hi).choose_spec
  apply Finset.sum_bij_ne_zero j (by intros; exact Finset.mem_univ _)
  · intro i him hi k hkm hk he
    exact P.vertices_injective ((hj i him hi).symm.trans
      ((congrArg P.meshNativeVertex he).trans (hj k hkm hk)))
  · intro v hvm hv
    have ho : ∃ i : Fin n,P.meshNativeVertex v = P.vertices i := by
      by_contra hn
      push Not at hn
      exact hv (P.meshBoundaryTurning_eq_zero_of_not_original v hn)
    obtain ⟨i,hi⟩ := ho
    have hnon : Real.pi-P.angle i ≠ 0 := by
      rw [← P.meshBoundaryTurning_of_original v i hi]
      exact hv
    refine ⟨i,Finset.mem_univ _,hnon,P.meshNativeVertex_injective ?_⟩
    exact (hj i (Finset.mem_univ _) hnon).trans hi.symm
  · intro i him hi
    exact (P.meshBoundaryTurning_of_original (j i him hi) i (hj i him hi)).symm

theorem DiscPolygon.meshAngleSumAt_of_not_boundary {n : ℕ} (P : DiscPolygon n)
    (v : P.UsedMeshVertex) (hb : P.meshNativeVertex v ∉ P.boundary) :
    P.meshAngleSumAt v = 2*Real.pi := by
  have hp : (P.meshNativeVertex v : ℂ) ∈ closure P.complexInterior := by
    rw [← P.closedCarrier_complex_image]
    exact mem_image_of_mem ((↑) : 𝕔𝔻 → ℂ) (P.usedMeshVertex_spec v.1 v.2).1
  rw [P.closure_complexInterior] at hp
  have hi : (P.meshNativeVertex v : ℂ) ∈ P.complexInterior := by
    rcases hp with hi | hb'
    · exact hi
    · obtain ⟨p,hp,he⟩ := hb'
      exact (hb ((Complex.UnitClosedDisc.coe_injective he) ▸ hp)).elim
  have hnorm : ‖(P.meshNativeVertex v : ℂ)‖ < 1 := by
    have hh := P.complexInterior_subset_disc hi
    simpa only [Metric.mem_ball,dist_zero_right] using hh
  let z := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (P.meshNativeVertex v) hnorm
  have hz : P.meshNativeVertex v = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ hnorm).symm
  have hzI : z ∈ P.interior := by exact hi
  exact P.meshAngleSumAt_of_interior v z hz hzI

theorem DiscPolygon.sum_meshBoundaryIndicator {n : ℕ} (P : DiscPolygon n) :
    (∑ v : P.UsedMeshVertex,if P.meshNativeVertex v ∈ P.boundary then Real.pi else 0) =
      P.kleinTriangleMesh.boundaryVertices.card*Real.pi := by
  have hs := Finset.sum_subtype (F := inferInstance)
    (p := fun v : P.kleinTriangleMesh.Vertex => v ∈ P.kleinTriangleMesh.usedVertices)
    P.kleinTriangleMesh.usedVertices (by intro v; rfl)
    (fun v : P.kleinTriangleMesh.Vertex => if v ∈ P.kleinTriangleMesh.boundaryVertices then Real.pi else 0)
  have hPoint : (∑ v : P.UsedMeshVertex,if P.meshNativeVertex v ∈ P.boundary then Real.pi else 0) =
      ∑ v : P.UsedMeshVertex,if v.1 ∈ P.kleinTriangleMesh.boundaryVertices then Real.pi else 0 := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [P.meshNativeVertex_mem_boundary_iff v]
    by_cases hb : v.1 ∈ P.kleinTriangleMesh.boundaryVertices
    · rw [ite_eq_left hb,ite_eq_left hb]
    · rw [ite_eq_right hb,ite_eq_right hb]
  rw [hPoint,← hs]
  have hfilter : P.kleinTriangleMesh.usedVertices.filter
      (fun v => v ∈ P.kleinTriangleMesh.boundaryVertices) = P.kleinTriangleMesh.boundaryVertices := by
    ext v
    simp only [Finset.mem_filter,
      LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.boundaryVertices]
    tauto
  rw [← Finset.sum_filter,hfilter]
  simp

/-- The true area depends only on the original genuine cyclic corner angles. -/
theorem DiscPolygon.area_toReal_eq_original_angle_defect {n : ℕ} (P : DiscPolygon n) :
    P.area.toReal = ((n : ℝ)-2)*Real.pi-∑ i : Fin n,P.angle i := by
  let M := P.kleinTriangleMesh
  have hEuler := M.boundaryDiskCharacteristic_of_polygonalDisk P.toPolygonalCircle
    (P.kleinTriangleMesh_support.trans P.kleinPlane_image_closedCarrier)
  unfold LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.boundaryDiskCharacteristic at hEuler
  have hER : 2*(M.usedVertices.card : ℝ)-(M.triangles.card : ℝ)-(M.boundaryVertices.card : ℝ)=2 := by
    exact_mod_cast hEuler
  have hV : (Fintype.card P.UsedMeshVertex : ℝ) = (M.usedVertices.card : ℝ) := by
    norm_cast
    exact Fintype.card_coe M.usedVertices
  have hF : (Fintype.card M.Triangle : ℝ) = (M.triangles.card : ℝ) := by
    norm_cast
    exact Fintype.card_coe M.triangles
  have hPoint (v : P.UsedMeshVertex) :
      P.meshAngleSumAt v + P.meshBoundaryTurning v =
        2*Real.pi-(if P.meshNativeVertex v ∈ P.boundary then Real.pi else 0) := by
    by_cases hb : P.meshNativeVertex v ∈ P.boundary
    · rw [DiscPolygon.meshBoundaryTurning,ite_eq_left hb,ite_eq_left hb]
      ring
    · rw [DiscPolygon.meshBoundaryTurning,ite_eq_right hb,ite_eq_right hb,
        P.meshAngleSumAt_of_not_boundary v hb]
      ring
  have hSum := Finset.sum_congr (s₁ := (Finset.univ : Finset P.UsedMeshVertex)) rfl (fun v hv => hPoint v)
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,P.sum_meshBoundaryTurning,
    P.sum_meshBoundaryIndicator] at hSum
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.sum_sub_distrib,
    Fintype.card_fin] at hSum
  rw [P.area_toReal_eq_meshAngleSumAt]
  rw [hV] at hSum
  rw [hF]
  have hEpi := congrArg (fun r : ℝ => r*Real.pi) hER
  nlinarith only [hSum,hEpi]

/-- The exact genuine density area, including ideal and nonconvex polygons. -/
theorem DiscPolygon.area_eq_original_angle_defect {n : ℕ} (P : DiscPolygon n) :
    P.area = ENNReal.ofReal (((n : ℝ)-2)*Real.pi-∑ i : Fin n,P.angle i) := by
  rw [← P.area_toReal_eq_original_angle_defect,ENNReal.ofReal_toReal (ne_of_lt P.area_lt_top)]

/-- Every actual polygon satisfies the strict original angle-sum inequality. -/
theorem DiscPolygon.angle_sum_lt {n : ℕ} (P : DiscPolygon n) :
    ∑ i : Fin n,P.angle i < ((n : ℝ)-2)*Real.pi := by
  have hp := ENNReal.toReal_pos (ne_of_gt P.area_pos) (ne_of_lt P.area_lt_top)
  rw [P.area_toReal_eq_original_angle_defect] at hp
  linarith only [hp]

/-- Prescribed admissible angles occur in a true polygon exactly under the strict original bound. -/
theorem exists_discPolygon_angles_iff {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) :
    (∃ P : DiscPolygon n,∀ i,P.angle i=θ i) ↔ ∑ i,θ i < ((n : ℝ)-2)*Real.pi := by
  constructor
  · rintro ⟨P,hP⟩
    simpa only [hP] using P.angle_sum_lt
  · intro hsum
    obtain ⟨P,hc,ha,hd⟩ := exists_tangentialDiscPolygon θ hθ hsum
    exact ⟨P,ha⟩

/-- The same exact angle criterion admits an actual convex realization. -/
theorem exists_convexDiscPolygon_angles_iff {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) :
    (∃ P : DiscPolygon n,P.IsConvex ∧ ∀ i,P.angle i=θ i) ↔ ∑ i,θ i < ((n : ℝ)-2)*Real.pi := by
  constructor
  · rintro ⟨P,hc,ha⟩
    exact (exists_discPolygon_angles_iff θ hθ).mp ⟨P,ha⟩
  · intro hsum
    obtain ⟨P,hc,ha,hd⟩ := exists_tangentialDiscPolygon θ hθ hsum
    exact ⟨P,hc,ha⟩

/-- The full angle criterion can additionally realize a genuine native incircle. -/
theorem exists_tangentialDiscPolygon_angles_iff {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) :
    (∃ P : DiscPolygon n,P.IsConvex ∧ (∀ i,P.angle i=θ i) ∧ ∃ d,P.HasIncircleAt 0 d) ↔
      ∑ i,θ i < ((n : ℝ)-2)*Real.pi := by
  constructor
  · rintro ⟨P,hc,ha,hd⟩
    exact (exists_discPolygon_angles_iff θ hθ).mp ⟨P,ha⟩
  · exact exists_tangentialDiscPolygon θ hθ

end
end LowDimensionalTopology.Geometry.Polygon
