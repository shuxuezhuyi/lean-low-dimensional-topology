module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.ProperSectorAngularMeasure
public import LowDimensionalTopology.Geometry.Polygon.Triangulation.PolygonMeshEuler

/-! Actual mesh vertices, native triangle corner angles and genuine global area accounting. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped Complex.UnitDisc ENNReal Classical
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

def _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.cornerVertex (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (i : Fin 3) : 𝕔𝔻 :=
  ![T.a, T.b, T.c] i

def _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.cornerMeasure (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (i : Fin 3) : ℝ :=
  ![T.alpha, T.beta, T.gamma] i

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.finiteCarrier_cycle (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    T.cycle.finiteCarrier = T.finiteCarrier := by
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.finiteCarrier,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.closedCarrier,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.cycle]
  congr 2
  ext p
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.subtendedAngle_at_corner (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (i : Fin 3)
    (z : 𝔻) (h : T.cornerVertex i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle T.finiteCarrier z = T.cornerMeasure i := by
  fin_cases i
  · exact T.subtendedAngle_at_finite z h
  · have hh := T.cycle.subtendedAngle_at_finite z h
    rw [T.finiteCarrier_cycle] at hh
    exact hh
  · have hh := T.cycle.cycle.subtendedAngle_at_finite z h
    rw [T.cycle.finiteCarrier_cycle, T.finiteCarrier_cycle] at hh
    exact hh

theorem DiscPolygon.meshTriangle_subtendedAngle_sum {n : ℕ} (P : DiscPolygon n)
    {z : 𝔻} (hz : z ∈ P.interior) :
    ∑ t ∈ Finset.univ.filter (fun t : P.kleinTriangleMesh.Triangle =>
      z ∈ (P.meshTriangle t).finiteCarrier),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (P.meshTriangle t).finiteCarrier z = 2 * Real.pi := by
  have hs := congrArg ENNReal.toReal (P.meshTriangle_angularFraction_sum hz)
  rw [ENNReal.toReal_sum (fun t ht => by
    unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction
    exact measure_ne_top _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure _), ENNReal.toReal_one] at hs
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle, ← Finset.mul_sum, hs, mul_one]

/-- Every used abstract mesh vertex is an actual point of the original compactified polygon. -/
theorem DiscPolygon.usedMeshVertex_exists {n : ℕ} (P : DiscPolygon n)
    (v : P.kleinTriangleMesh.Vertex) (hv : v ∈ P.kleinTriangleMesh.usedVertices) :
    ∃ p ∈ P.closedCarrier, discPolygonKleinPlane p = P.kleinTriangleMesh.position v := by
  have hp : P.kleinTriangleMesh.position v ∈ P.kleinTriangleMesh.toPlaneComplex.support := by
    obtain ⟨t, ht, hvt⟩ := P.kleinTriangleMesh.mem_usedVertices.mp hv
    rw [LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.toPlaneComplex_support]
    refine mem_iUnion₂.mpr ⟨t, ht, subset_convexHull ℝ _ ?_⟩
    exact ⟨v, hvt, rfl⟩
  rw [P.kleinTriangleMesh_support] at hp
  exact hp

def DiscPolygon.usedMeshVertex {n : ℕ} (P : DiscPolygon n)
    (v : P.kleinTriangleMesh.Vertex) (hv : v ∈ P.kleinTriangleMesh.usedVertices) : 𝕔𝔻 :=
  (P.usedMeshVertex_exists v hv).choose

theorem DiscPolygon.usedMeshVertex_spec {n : ℕ} (P : DiscPolygon n)
    (v : P.kleinTriangleMesh.Vertex) (hv : v ∈ P.kleinTriangleMesh.usedVertices) :
    P.usedMeshVertex v hv ∈ P.closedCarrier ∧
      discPolygonKleinPlane (P.usedMeshVertex v hv) = P.kleinTriangleMesh.position v :=
  (P.usedMeshVertex_exists v hv).choose_spec

theorem DiscPolygon.usedMeshVertex_mem_triangle_iff {n : ℕ} (P : DiscPolygon n)
    (v : P.kleinTriangleMesh.Vertex) (hv : v ∈ P.kleinTriangleMesh.usedVertices)
    (t : P.kleinTriangleMesh.Triangle) :
    P.usedMeshVertex v hv ∈ (P.meshTriangle t).closedCarrier ↔ v ∈ t.1 := by
  have he (h : P.usedMeshVertex v hv ∈ (P.meshTriangle t).closedCarrier) :
      P.kleinTriangleMesh.position v ∈ P.kleinTriangleMesh.triangleCarrier t.1 := by
    have hh := mem_image_of_mem discPolygonKleinPlane h
    rw [P.meshTriangle_klein_image, (P.usedMeshVertex_spec v hv).2] at hh
    exact hh
  constructor
  · exact fun h => P.kleinTriangleMesh.mem_triangle_of_position_mem hv t.2 (he h)
  · intro hvt
    apply discPolygonKleinPlane_injective.mem_set_image.mp
    rw [P.meshTriangle_klein_image, (P.usedMeshVertex_spec v hv).2]
    exact subset_convexHull ℝ _ ⟨v, hvt, rfl⟩

theorem DiscPolygon.meshTriangle_cornerVertex_eq {n : ℕ} (P : DiscPolygon n)
    (t : P.kleinTriangleMesh.Triangle) (i : Fin 3) :
    (P.meshTriangle t).cornerVertex i = P.meshTriangleVertex t i := by
  fin_cases i <;> rfl

theorem DiscPolygon.usedMeshVertex_eq_meshTriangleVertex {n : ℕ} (P : DiscPolygon n)
    (v : P.kleinTriangleMesh.Vertex) (hv : v ∈ P.kleinTriangleMesh.usedVertices)
    (t : P.kleinTriangleMesh.Triangle) (i : Fin 3)
    (hi : P.kleinTriangleMesh.orderedVertex t i = v) :
    P.usedMeshVertex v hv = P.meshTriangleVertex t i := by
  apply discPolygonKleinPlane_injective
  rw [(P.usedMeshVertex_spec v hv).2, (P.meshTriangleVertex_spec t i).2, hi]

theorem DiscPolygon.usedMeshVertex_corner_exists {n : ℕ} (P : DiscPolygon n)
    (v : P.kleinTriangleMesh.Vertex) (hv : v ∈ P.kleinTriangleMesh.usedVertices)
    (t : P.kleinTriangleMesh.Triangle) (hvt : v ∈ t.1) :
    ∃ i : Fin 3, (P.meshTriangle t).cornerVertex i = P.usedMeshVertex v hv := by
  have hh : v ∈ Set.range (P.kleinTriangleMesh.orderedVertex t) := by
    rw [P.kleinTriangleMesh.range_orderedVertex]
    exact hvt
  obtain ⟨i, hi⟩ := hh
  exact ⟨i, (P.meshTriangle_cornerVertex_eq t i).trans
    (P.usedMeshVertex_eq_meshTriangleVertex v hv t i hi).symm⟩

/-- The original angle belonging to a true compactified triangle vertex, and zero elsewhere. -/
def _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.angleAtPoint (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (p : 𝕔𝔻) : ℝ :=
  if p = T.a then T.alpha else if p = T.b then T.beta else if p = T.c then T.gamma else 0

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.angleAtPoint_cornerVertex (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (i : Fin 3) :
    T.angleAtPoint (T.cornerVertex i) = T.cornerMeasure i := by
  fin_cases i <;> simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.angleAtPoint, _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.cornerVertex, _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.cornerMeasure,
    T.c_ne_a, T.a_ne_b.symm, T.b_ne_c.symm]

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.angleAtPoint_eq_zero_of_not_mem (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle)
    {p : 𝕔𝔻} (hp : p ∉ T.closedCarrier) : T.angleAtPoint p = 0 := by
  have ha : p ≠ T.a := by
    rintro rfl
    exact hp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.subset_closedDiscHConvexHull {T.a,T.b,T.c} (by simp))
  have hb : p ≠ T.b := by
    rintro rfl
    exact hp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.subset_closedDiscHConvexHull {T.a,T.b,T.c} (by simp))
  have hc : p ≠ T.c := by
    rintro rfl
    exact hp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.subset_closedDiscHConvexHull {T.a,T.b,T.c} (by simp))
  simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.angleAtPoint, ha, hb, hc]

theorem DiscPolygon.meshTriangle_angleAtPoint_eq_subtendedAngle {n : ℕ} (P : DiscPolygon n)
    (v : P.kleinTriangleMesh.Vertex) (hv : v ∈ P.kleinTriangleMesh.usedVertices)
    (z : 𝔻) (hz : P.usedMeshVertex v hv = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (t : P.kleinTriangleMesh.Triangle) (hvt : v ∈ t.1) :
    (P.meshTriangle t).angleAtPoint (P.usedMeshVertex v hv) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (P.meshTriangle t).finiteCarrier z := by
  obtain ⟨i, hi⟩ := P.usedMeshVertex_corner_exists v hv t hvt
  rw [← hi, (P.meshTriangle t).angleAtPoint_cornerVertex]
  exact ((P.meshTriangle t).subtendedAngle_at_corner i z (hi.trans hz)).symm

theorem DiscPolygon.meshTriangle_angleAtPoint_sum_of_interior {n : ℕ} (P : DiscPolygon n)
    (v : P.kleinTriangleMesh.Vertex) (hv : v ∈ P.kleinTriangleMesh.usedVertices)
    (z : 𝔻) (hz : P.usedMeshVertex v hv = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) (hzP :
      z ∈ P.interior) :
    ∑ t : P.kleinTriangleMesh.Triangle,
      (P.meshTriangle t).angleAtPoint (P.usedMeshVertex v hv) = 2 * Real.pi := by
  classical
  have he (t : P.kleinTriangleMesh.Triangle) :
      z ∈ (P.meshTriangle t).finiteCarrier ↔ v ∈ t.1 := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈ (P.meshTriangle t).closedCarrier ↔ _
    rw [← hz]
    exact P.usedMeshVertex_mem_triangle_iff v hv t
  rw [← P.meshTriangle_subtendedAngle_sum hzP]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hvt : v ∈ t.1
  · rw [ite_eq_left ((he t).mpr hvt)]
    exact P.meshTriangle_angleAtPoint_eq_subtendedAngle v hv z hz t hvt
  · rw [ite_eq_right (fun h => hvt ((he t).mp h))]
    exact (P.meshTriangle t).angleAtPoint_eq_zero_of_not_mem
      (fun h => hvt ((P.usedMeshVertex_mem_triangle_iff v hv t).mp h))

/-- Vertices which actually occur in the original polygon's derived finite mesh. -/
abbrev DiscPolygon.UsedMeshVertex {n : ℕ} (P : DiscPolygon n) :=
  {v : P.kleinTriangleMesh.Vertex // v ∈ P.kleinTriangleMesh.usedVertices}

def DiscPolygon.meshNativeVertex {n : ℕ} (P : DiscPolygon n) (v : P.UsedMeshVertex) : 𝕔𝔻 :=
  P.usedMeshVertex v.1 v.2

theorem DiscPolygon.meshNativeVertex_injective {n : ℕ} (P : DiscPolygon n) :
    Function.Injective P.meshNativeVertex := by
  intro v w he
  apply Subtype.ext
  apply P.kleinTriangleMesh.position_injective
  exact ((P.usedMeshVertex_spec v.1 v.2).2).symm.trans
    ((congrArg discPolygonKleinPlane he).trans (P.usedMeshVertex_spec w.1 w.2).2)

theorem DiscPolygon.meshTriangle_angleAtPoint_sum_vertices {n : ℕ} (P : DiscPolygon n)
    (t : P.kleinTriangleMesh.Triangle) :
    ∑ v : P.UsedMeshVertex, (P.meshTriangle t).angleAtPoint (P.meshNativeVertex v) =
      (P.meshTriangle t).alpha + (P.meshTriangle t).beta + (P.meshTriangle t).gamma := by
  let j : Fin 3 → P.UsedMeshVertex := fun i =>
    ⟨P.kleinTriangleMesh.orderedVertex t i,
      P.kleinTriangleMesh.mem_usedVertices.mpr
        ⟨t.1,t.2,P.kleinTriangleMesh.orderedVertex_mem t i⟩⟩
  have hj : Function.Injective j := by
    intro i k h
    have hh : P.kleinTriangleMesh.orderedVertex t i = P.kleinTriangleMesh.orderedVertex t k :=
      congrArg (fun v : P.UsedMeshVertex => v.1) h
    exact P.kleinTriangleMesh.orderedVertex_injective t hh
  have hval (i : Fin 3) : P.meshNativeVertex (j i) = (P.meshTriangle t).cornerVertex i :=
    (P.usedMeshVertex_eq_meshTriangleVertex _ _ t i rfl).trans
      (P.meshTriangle_cornerVertex_eq t i).symm
  have hs : ∑ v : P.UsedMeshVertex, (P.meshTriangle t).angleAtPoint (P.meshNativeVertex v) =
      ∑ v ∈ Finset.univ.image j, (P.meshTriangle t).angleAtPoint (P.meshNativeVertex v) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v hv hvj
    apply (P.meshTriangle t).angleAtPoint_eq_zero_of_not_mem
    intro hmem
    have hvt := (P.usedMeshVertex_mem_triangle_iff v.1 v.2 t).mp hmem
    have hi : v.1 ∈ Set.range (P.kleinTriangleMesh.orderedVertex t) := by
      rw [P.kleinTriangleMesh.range_orderedVertex]
      exact hvt
    obtain ⟨i,hi⟩ := hi
    apply hvj
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,Subtype.ext hi⟩
  rw [hs, Finset.sum_image (fun i _ k _ h => hj h)]
  simp only [hval, _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.angleAtPoint_cornerVertex]
  simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.cornerMeasure, Fin.sum_univ_succ,
    add_assoc]

def DiscPolygon.meshAngleSumAt {n : ℕ} (P : DiscPolygon n) (v : P.UsedMeshVertex) : ℝ :=
  ∑ t : P.kleinTriangleMesh.Triangle, (P.meshTriangle t).angleAtPoint (P.meshNativeVertex v)

theorem DiscPolygon.meshAngleSumAt_of_interior {n : ℕ} (P : DiscPolygon n)
    (v : P.UsedMeshVertex) (z : 𝔻) (hz : P.meshNativeVertex v =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hzP : z ∈ P.interior) : P.meshAngleSumAt v = 2 * Real.pi :=
  P.meshTriangle_angleAtPoint_sum_of_interior v.1 v.2 z hz hzP

theorem DiscPolygon.sum_meshAngleSumAt {n : ℕ} (P : DiscPolygon n) :
    ∑ v : P.UsedMeshVertex, P.meshAngleSumAt v =
      ∑ t : P.kleinTriangleMesh.Triangle,
        ((P.meshTriangle t).alpha + (P.meshTriangle t).beta + (P.meshTriangle t).gamma) := by
  unfold DiscPolygon.meshAngleSumAt
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun t _ => P.meshTriangle_angleAtPoint_sum_vertices t)

theorem DiscPolygon.area_toReal_eq_meshAngleSumAt {n : ℕ} (P : DiscPolygon n) :
    P.area.toReal = Fintype.card P.kleinTriangleMesh.Triangle * Real.pi -
      ∑ v : P.UsedMeshVertex, P.meshAngleSumAt v := by
  rw [P.area_toReal_eq_sum_meshTriangle_angle_defects, P.sum_meshAngleSumAt]
  simp only [sub_sub, add_assoc]
  rw [Finset.sum_sub_distrib]
  simp


end
end LowDimensionalTopology.Geometry.Polygon
