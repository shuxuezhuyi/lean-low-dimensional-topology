/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Support.CyclicDiscPolygonSupports
public import LowDimensionalTopology.Geometry.Polygon.Hexagon.HexagonNormals
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.SaccheriQuadrilaterals
/-! # Genuine convex Jordan polygons for the right-hexagon incidence model

Actual side normals are oriented by the supplied genuine support-side positions.
Their cyclic geometry derives the entire bounded body and an interior center, and
constructs an actual convex Jordan hexagon. Its true numerical angles are all right;
its actual path-distance side lengths and both source metric identities are identified.
The converse from an arbitrary Jordan right hexagon is a separate obligation.
-/
@[expose] public section
namespace LowDimensionalTopology.Geometry.Polygon
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc Topology
noncomputable section

def RightHexagon.polygonVertices (Q : RightHexagon) (i : Fin 6) : 𝕔𝔻 :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (Q.vertex i))

theorem RightHexagon.polygonVertices_injective (Q : RightHexagon) : Function.Injective Q.polygonVertices :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective.comp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective.comp Q.vertex_injective)

theorem RightHexagon.polygonNormal_norm_pos (Q : RightHexagon) (i : Fin 6) :
    0<‖(Q.side i).incenterNormal‖ := by
  apply norm_pos_iff.mpr
  intro he
  have h := (Q.side i).incenterNormal_lorentz_unit
  rw [he,norm_zero,zero_pow (by omega : 2≠0)] at h
  nlinarith only [h,sq_nonneg (Q.side i).incenterOffset]

theorem RightHexagon.polygonSeed_time_ne_zero (Q : RightHexagon) (i : Fin 6) :
    (Q.side i).normalTimeAt (Q.vertex (i+2))≠0 := by
  have h0 : i+2≠i := by fin_cases i <;> decide
  have h1 : i+2≠i+1 := by fin_cases i <;> decide
  have h := Q.same_side i (i+2) (i+2) h0 h1 h0 h1
  intro he
  rw [he,zero_mul] at h
  exact (lt_irrefl _ h).elim

def RightHexagon.polygonOrientation (Q : RightHexagon) (i : Fin 6) : ℝ :=
  (Q.side i).normalTimeAt (Q.vertex (i+2))/|(Q.side i).normalTimeAt (Q.vertex (i+2))|

theorem RightHexagon.polygonOrientation_abs (Q : RightHexagon) (i : Fin 6) :
    |Q.polygonOrientation i|=1 := by
  rw [RightHexagon.polygonOrientation,abs_div,abs_abs,div_self (abs_ne_zero.mpr (Q.polygonSeed_time_ne_zero i))]

def RightHexagon.polygonNormal (Q : RightHexagon) (i : Fin 6) : ℂ :=
  (Q.polygonOrientation i/‖(Q.side i).incenterNormal‖) • (Q.side i).incenterNormal

def RightHexagon.polygonOffset (Q : RightHexagon) (i : Fin 6) : ℝ :=
  (Q.polygonOrientation i/‖(Q.side i).incenterNormal‖)*(Q.side i).incenterOffset

theorem RightHexagon.polygonNormal_norm (Q : RightHexagon) (i : Fin 6) : ‖Q.polygonNormal i‖=1 := by
  rw [RightHexagon.polygonNormal,norm_smul,Real.norm_eq_abs,abs_div,Q.polygonOrientation_abs,
    abs_of_pos (Q.polygonNormal_norm_pos i),one_div,inv_mul_cancel₀ (Q.polygonNormal_norm_pos i).ne']

theorem RightHexagon.polygonSupport_gap (Q : RightHexagon) (i : Fin 6) (z : ℍ) :
    inner ℝ (Q.polygonNormal i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)))-Q.polygonOffset i=
      -(Q.polygonOrientation i*(Q.side i).normalTimeAt z)/
        (‖(Q.side i).incenterNormal‖*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight z) := by
  have hn := Q.polygonNormal_norm_pos i
  have hH := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_pos z
  have he := (Q.side i).normalTimeAt_eq_affine z
  change (Q.side i).normalTimeAt z= -_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight z*
    (inner ℝ (Q.side i).incenterNormal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
      z)-(Q.side i).incenterOffset) at he
  rw [RightHexagon.polygonNormal,RightHexagon.polygonOffset,real_inner_smul_left,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion]
  change (Q.polygonOrientation i/‖(Q.side i).incenterNormal‖)*inner ℝ (Q.side i).incenterNormal
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)-(Q.polygonOrientation i/‖(Q.side
      i).incenterNormal‖)*(Q.side i).incenterOffset=_
  field_simp [hn.ne',hH.ne']
  nlinarith only [congrArg (fun t : ℝ=>Q.polygonOrientation i*t) he]

theorem RightHexagon.side_contains_vertex (Q : RightHexagon) (i : Fin 6) : Q.vertex i∈(Q.side i).carrier := by
  have he : ∀ j : Fin 6,(j-1)+1=j := by decide
  have h := Q.right_angle (i-1)
  rw [he] at h
  exact h.2.1

theorem RightHexagon.polygon_incident (Q : RightHexagon) (i : Fin 6) :
    inner ℝ (Q.polygonNormal i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      (Q.polygonVertices i))=Q.polygonOffset i ∧
    inner ℝ (Q.polygonNormal i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.polygonVertices (finRotate 6 i)))=Q.polygonOffset i := by
  have hnxt : ∀ j : Fin 6,finRotate 6 j=j+1 := by decide
  have h0 := ((Q.side i).normalTimeAt_eq_zero_iff (Q.vertex i)).mpr (Q.side_contains_vertex i)
  have h1 := ((Q.side i).normalTimeAt_eq_zero_iff (Q.vertex (i+1))).mpr (Q.right_angle i).1
  constructor
  · apply sub_eq_zero.mp
    change inner ℝ (Q.polygonNormal i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (Q.vertex i))))-Q.polygonOffset i=0
    rw [Q.polygonSupport_gap,h0,mul_zero,neg_zero,zero_div]
  · rw [hnxt]
    apply sub_eq_zero.mp
    change inner ℝ (Q.polygonNormal i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (Q.vertex (i+1)))))-Q.polygonOffset i=0
    rw [Q.polygonSupport_gap,h1,mul_zero,neg_zero,zero_div]

theorem RightHexagon.polygon_nonincident (Q : RightHexagon) (i j : Fin 6)
    (hji : j≠i) (hjnext : j≠finRotate 6 i) :
    inner ℝ (Q.polygonNormal i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.polygonVertices j))<Q.polygonOffset i := by
  have hnxt : ∀ k : Fin 6,finRotate 6 k=k+1 := by decide
  rw [hnxt] at hjnext
  have h0 : i+2≠i := by fin_cases i <;> decide
  have h1 : i+2≠i+1 := by fin_cases i <;> decide
  have h := Q.same_side i (i+2) j h0 h1 hji hjnext
  have hprod : 0<Q.polygonOrientation i*(Q.side i).normalTimeAt (Q.vertex j) := by
    rw [RightHexagon.polygonOrientation,div_mul_eq_mul_div]
    exact div_pos h (abs_pos.mpr (Q.polygonSeed_time_ne_zero i))
  apply sub_neg.mp
  change inner ℝ (Q.polygonNormal i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (Q.vertex j))))-Q.polygonOffset i<0
  rw [Q.polygonSupport_gap]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hprod)
    (mul_pos (Q.polygonNormal_norm_pos i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_pos
      (Q.vertex j)))

def RightHexagon.polygonSupportData (Q : RightHexagon) : CyclicDiscPolygonSupportData 6 where
  three_le := by norm_num
  vertices := Q.polygonVertices
  vertices_injective := Q.polygonVertices_injective
  normals := Q.polygonNormal
  normal_norm := Q.polygonNormal_norm
  offsets := Q.polygonOffset
  incident := Q.polygon_incident
  nonincident := Q.polygon_nonincident

def RightHexagon.toDiscPolygon (Q : RightHexagon) : DiscPolygon 6 := Q.polygonSupportData.toDiscPolygon

theorem RightHexagon.toDiscPolygon_isConvex (Q : RightHexagon) : Q.toDiscPolygon.IsConvex :=
  Q.polygonSupportData.toDiscPolygon_isConvex


theorem RightHexagon.polygonSupportLine_eq (Q : RightHexagon) (i : Fin 6) :
    Q.polygonSupportData.toCenteredData.supportLine i=(Q.side i).toDiscLine := by
  let S := Q.polygonSupportData.toCenteredData
  apply (S.supportLine i).eq_of_two_closed_points _
    (S.vertices_injective.ne (centeredPolygonSupport_next_ne_self S.three_le i).symm)
    (S.incident_mem_support i).1 (S.incident_mem_support i).2
  · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (Q.vertex i))∈(Q.side i).toDiscLine.closedCarrier
    apply ((Q.side i).toDiscLine.closedCarrier_mem_interior_iff _).mpr
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.mem_carrier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_toHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
    exact Q.side_contains_vertex i
  · have hnxt : ∀ j : Fin 6,finRotate 6 j=j+1 := by decide
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (Q.vertex (finRotate 6 i)))∈(Q.side i).toDiscLine.closedCarrier
    rw [hnxt]
    apply ((Q.side i).toDiscLine.closedCarrier_mem_interior_iff _).mpr
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.mem_carrier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_toHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
    exact (Q.right_angle i).1

theorem RightHexagon.toDiscPolygon_vertices (Q : RightHexagon) (i : Fin 6) :
    Q.toDiscPolygon.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (Q.vertex i)) := rfl

theorem RightHexagon.toDiscPolygon_angle (Q : RightHexagon) (i : Fin 6) :
    Q.toDiscPolygon.angle i=Real.pi/2 := by
  change Q.polygonSupportData.toCenteredData.toDiscPolygon.angle i=Real.pi/2
  rw [Q.polygonSupportData.toCenteredData.angle_eq_cornerTriangle]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.alpha_eq_pi_div_two_of_normalPairing_zero
  rw [Q.polygonSupportData.toCenteredData.cornerTriangle_sideB,
    Q.polygonSupportData.toCenteredData.cornerTriangle_sideC,Q.polygonSupportLine_eq,Q.polygonSupportLine_eq,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_toHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_toHalfPlane]
  have h := Q.right_angle ((finRotate 6).symm i)
  have hp : ∀ j : Fin 6,((finRotate 6).symm j)+1=j := by decide
  rw [hp] at h
  exact (Q.side i).normalPairing_orthogonal _ (Q.vertex i)
    ⟨h.2.1,h.1,by rw [real_inner_comm];exact h.2.2⟩

def RightHexagon.discEdgeLength (Q : RightHexagon) (i : Fin 6) : ℝ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (Q.vertex i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (Q.vertex (i+1)))

theorem RightHexagon.discEdgeLength_eq (Q : RightHexagon) (i : Fin 6) : Q.discEdgeLength i=Q.edgeLength i := by
  rw [RightHexagon.discEdgeLength,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  rfl

theorem RightHexagon.toDiscPolygon_edgeLength (Q : RightHexagon) (i : Fin 6) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength (Q.toDiscPolygon.vertices
      i) (Q.toDiscPolygon.vertices (finRotate 6 i))=
      ENNReal.ofReal (Q.edgeLength i) := by
  have hnxt : ∀ j : Fin 6,finRotate 6 j=j+1 := by decide
  rw [Q.toDiscPolygon_vertices,Q.toDiscPolygon_vertices,hnxt,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength_finite]
  exact congrArg ENNReal.ofReal (Q.discEdgeLength_eq i)

theorem RightHexagon.discEdgeLength_cosh_sinh_sinh_identity (Q : RightHexagon) :
    Real.cosh (Q.discEdgeLength 3)*Real.sinh (Q.discEdgeLength 4)*Real.sinh (Q.discEdgeLength 2)=
      Real.cosh (Q.discEdgeLength 0)+Real.cosh (Q.discEdgeLength 4)*Real.cosh (Q.discEdgeLength 2) := by
  simp only [Q.discEdgeLength_eq]
  exact Q.cosh_sinh_sinh_identity

theorem RightHexagon.discEdgeLength_sinh_opposite_ratios_eq (Q : RightHexagon) :
    Real.sinh (Q.discEdgeLength 0)/Real.sinh (Q.discEdgeLength 3)=
      Real.sinh (Q.discEdgeLength 4)/Real.sinh (Q.discEdgeLength 1) ∧
    Real.sinh (Q.discEdgeLength 4)/Real.sinh (Q.discEdgeLength 1)=
      Real.sinh (Q.discEdgeLength 2)/Real.sinh (Q.discEdgeLength 5) := by
  simp only [Q.discEdgeLength_eq]
  exact Q.sinh_opposite_side_ratios_eq

theorem RightHexagon.toDiscPolygon_remaining_sides_eq (Q R : RightHexagon)
    (ha : Q.discEdgeLength 0=R.discEdgeLength 0)
    (hb : Q.discEdgeLength 4=R.discEdgeLength 4)
    (hc : Q.discEdgeLength 2=R.discEdgeLength 2) :
    Q.discEdgeLength 3=R.discEdgeLength 3 ∧ Q.discEdgeLength 1=R.discEdgeLength 1 ∧
      Q.discEdgeLength 5=R.discEdgeLength 5 := by
  simp only [Q.discEdgeLength_eq,R.discEdgeLength_eq] at ha hb hc ⊢
  exact Q.remaining_sides_eq_of_alternating_eq R ha hb hc

end
end LowDimensionalTopology.Geometry.Polygon
