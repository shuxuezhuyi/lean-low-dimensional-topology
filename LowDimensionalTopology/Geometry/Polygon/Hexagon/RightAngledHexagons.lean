/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Support.ConvexDiscPolygonSupports
public import LowDimensionalTopology.Geometry.Polygon.FinitePolygonConvexity
public import LowDimensionalTopology.Geometry.Polygon.Hexagon.HexagonPolygonAdapters
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.SaccheriPolygonAdapters
/-! # Intrinsic metric formulas for arbitrary actual right-angled hexagons

Every genuine Jordan hexagon whose six actual numerical angles are right is
proved finite and convex, then represented by its actual sides and vertices in
the previously verified incidence model. The reconstructed actual polygon equals
the input, and all six lengths are precisely the genuine native path distances.
The source sine and cosine laws, cyclic variants, and alternating-side uniqueness
therefore hold without any extra convexity, support or metric-formula hypothesis.
-/
@[expose] public section
namespace LowDimensionalTopology.Geometry.Polygon
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc Topology
noncomputable section

def DiscPolygon.rightVertex {n : ℕ} (P : DiscPolygon n) (ha : ∀ i : Fin n,P.angle i=Real.pi/2) (i : Fin n) : 𝔻 :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (P.vertices i) (P.vertex_finite_of_angle_pos i (by rw [ha];positivity))

theorem DiscPolygon.rightVertex_spec {n : ℕ} (P : DiscPolygon n) (ha : ∀ i : Fin n,P.angle i=Real.pi/2)
    (i : Fin n) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.rightVertex ha
      i)=P.vertices i := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ _

theorem DiscPolygon.rightVertex_injective {n : ℕ} (P : DiscPolygon n) (ha : ∀ i : Fin n,P.angle i=Real.pi/2) :
    Function.Injective (P.rightVertex ha) := by
  intro i j he
  apply P.vertices_injective
  rw [← P.rightVertex_spec ha i,← P.rightVertex_spec ha j,he]

theorem DiscPolygon.rightVertex_halfPlaneKlein {n : ℕ} (P : DiscPolygon n)
    (ha : ∀ i : Fin n,P.angle i=Real.pi/2) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.rightVertex ha i))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,← _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,P.rightVertex_spec]

theorem DiscPolygon.right_support_time {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (ha : ∀ i : Fin n,P.angle i=Real.pi/2) (i : Fin n) :
    ∃ k : ℝ,k≠0 ∧ ∀ j : Fin n,
      (P.geodesicSide i).toHalfPlane.normalTimeAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
        (P.rightVertex ha j))=
        -_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.rightVertex ha j))*k*
          (inner ℝ ((P.supportDataOfExtreme hc (P.all_vertices_extreme_of_right_angles hc ha)).normals i)
              (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices j))-
            (P.supportDataOfExtreme hc (P.all_vertices_extreme_of_right_angles hc ha)).offsets i) := by
  let hE:=P.all_vertices_extreme_of_right_angles hc ha
  let S:=P.supportDataOfExtreme hc hE
  obtain ⟨k,hk,hn,ht⟩:=S.toCenteredData.support_normal_proportional i
  rw [P.supportDataOfExtreme_supportLine hc hE] at hn ht
  refine ⟨k,hk,?_⟩
  intro j
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalTimeAt_eq_affine]
  change -_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight _*(inner ℝ (P.geodesicSide
    i).incenterNormal
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate _)-(P.geodesicSide i).incenterOffset)=_
  rw [P.rightVertex_halfPlaneKlein ha j,hn,ht,real_inner_smul_left]
  change -_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.rightVertex ha j))*
      (k*inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
        j))-k*S.offsets i)=
    -_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.rightVertex ha j))*k*
      (inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
        j))-S.offsets i)
  ring

theorem DiscPolygon.right_support_same_side {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (ha : ∀ i : Fin n,P.angle i=Real.pi/2) (i j k : Fin n)
    (hji : j≠i) (hjn : j≠finRotate n i) (hki : k≠i) (hkn : k≠finRotate n i) :
    0<(P.geodesicSide i).toHalfPlane.normalTimeAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      (P.rightVertex ha j))*
      (P.geodesicSide i).toHalfPlane.normalTimeAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.rightVertex ha k)) := by
  let S:=P.supportDataOfExtreme hc (P.all_vertices_extreme_of_right_angles hc ha)
  obtain ⟨c,hc0,he⟩:=P.right_support_time hc ha i
  rw [he,he]
  have hj : inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
    j))-S.offsets i<0 :=
    sub_neg.mpr (S.nonincident i j hji hjn)
  have hk : inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
    k))-S.offsets i<0 :=
    sub_neg.mpr (S.nonincident i k hki hkn)
  have hpos:=mul_pos
    (mul_pos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_pos
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.rightVertex ha j)))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_pos
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.rightVertex ha k))))
    (mul_pos (mul_self_pos.mpr hc0) (mul_pos_of_neg_of_neg hj hk))
  convert hpos using 1
  ring

def DiscPolygon.asRightHexagon (P : DiscPolygon 6) (hc : P.IsConvex)
    (ha : ∀ i : Fin 6,P.angle i=Real.pi/2) : RightHexagon where
  vertex i:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.rightVertex ha i)
  vertex_injective:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective.comp (P.rightVertex_injective ha)
  side i:=(P.geodesicSide i).toHalfPlane
  right_angle i:=by
    have hz:=(P.rightVertex_spec ha (i+1)).symm
    have hp:=P.adjacent_sides_orthogonal_of_angle_right (i+1) (P.rightVertex ha (i+1)) hz (ha (i+1))
    have hprev : (finRotate 6).symm (i+1)=i := by fin_cases i <;> decide
    rw [hprev] at hp
    exact ((P.geodesicSide i).orthogonalAt_iff_halfPlane (P.geodesicSide (i+1)) _).mp hp
  same_side i j k hji hjn hki hkn:=by
    have hnxt : ∀ a : Fin 6,finRotate 6 a=a+1 := by decide
    apply P.right_support_same_side hc ha i j k hji (by simpa only [hnxt] using hjn)
      hki (by simpa only [hnxt] using hkn)


theorem DiscPolygon.asRightHexagon_toDiscPolygon (P : DiscPolygon 6) (hc : P.IsConvex)
    (ha : ∀ i : Fin 6,P.angle i=Real.pi/2) : (P.asRightHexagon hc ha).toDiscPolygon=P := by
  apply DiscPolygon.eq_of_vertices_eq
  funext i
  rw [RightHexagon.toDiscPolygon_vertices]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.rightVertex ha i)))=P.vertices i
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,P.rightVertex_spec]

theorem DiscPolygon.asRightHexagon_edgeLength (P : DiscPolygon 6) (hc : P.IsConvex)
    (ha : ∀ i : Fin 6,P.angle i=Real.pi/2) (i : Fin 6) :
    (P.asRightHexagon hc ha).edgeLength i=(P.sideLength i).toReal := by
  have hn : finRotate 6 i=i+1 := by fin_cases i <;> decide
  change dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.rightVertex ha
    i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.rightVertex ha (i+1)))=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength (P.vertices i) (P.vertices (finRotate 6
      i))).toReal
  rw [hn,← P.rightVertex_spec ha i,← P.rightVertex_spec ha
    (i+1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength_finite,
    ENNReal.toReal_ofReal (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane];exact dist_nonneg),_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]



/-- The genuine numerical interior angles of the actual Jordan polygon are all right. -/
def DiscPolygon.IsRightAngled {n : ℕ} (P : DiscPolygon n) : Prop := ∀ i : Fin n,P.angle i=Real.pi/2

/-- No convexity, supporting-side, incidence-model or metric-formula hypothesis is required. -/
def DiscPolygon.rightHexagon (P : DiscPolygon 6) (ha : P.IsRightAngled) : RightHexagon :=
  P.asRightHexagon (P.isConvex_of_right_angles ha) ha

theorem DiscPolygon.rightHexagon_toDiscPolygon (P : DiscPolygon 6) (ha : P.IsRightAngled) :
    (P.rightHexagon ha).toDiscPolygon=P :=
  P.asRightHexagon_toDiscPolygon (P.isConvex_of_right_angles ha) ha

theorem DiscPolygon.rightHexagon_edgeLength (P : DiscPolygon 6) (ha : P.IsRightAngled) (i : Fin 6) :
    (P.rightHexagon ha).edgeLength i=(P.sideLength i).toReal :=
  P.asRightHexagon_edgeLength (P.isConvex_of_right_angles ha) ha i

theorem DiscPolygon.right_sideLength_toReal_pos (P : DiscPolygon 6) (ha : P.IsRightAngled) (i : Fin 6) :
    0<(P.sideLength i).toReal := by
  rw [← P.rightHexagon_edgeLength ha i]
  exact (P.rightHexagon ha).edgeLength_pos i

/-- For every actual native Jordan right-angled hexagon. -/
theorem DiscPolygon.rightHexagon_sinh_opposite_side_ratios_eq (P : DiscPolygon 6) (ha : P.IsRightAngled) :
    Real.sinh (P.sideLength 0).toReal/Real.sinh (P.sideLength 3).toReal=
        Real.sinh (P.sideLength 4).toReal/Real.sinh (P.sideLength 1).toReal ∧
      Real.sinh (P.sideLength 4).toReal/Real.sinh (P.sideLength 1).toReal=
        Real.sinh (P.sideLength 2).toReal/Real.sinh (P.sideLength 5).toReal := by
  have h:=(P.rightHexagon ha).sinh_opposite_side_ratios_eq
  simpa only [RightHexagon.sideA₁,RightHexagon.sideA₂,RightHexagon.sideA₃,
    RightHexagon.sideB₁,RightHexagon.sideB₂,RightHexagon.sideB₃,P.rightHexagon_edgeLength ha] using h

/-- For the genuine path lengths of every actual right-angled hexagon. -/
theorem DiscPolygon.rightHexagon_cosh_sinh_sinh_identity (P : DiscPolygon 6) (ha : P.IsRightAngled) :
    Real.cosh (P.sideLength 3).toReal*Real.sinh (P.sideLength 4).toReal*Real.sinh (P.sideLength 2).toReal=
      Real.cosh (P.sideLength 0).toReal+Real.cosh (P.sideLength 4).toReal*Real.cosh (P.sideLength 2).toReal := by
  have h:=(P.rightHexagon ha).cosh_sinh_sinh_identity
  simpa only [RightHexagon.sideA₁,RightHexagon.sideA₂,RightHexagon.sideA₃,RightHexagon.sideB₁,
    P.rightHexagon_edgeLength ha] using h

theorem DiscPolygon.right_hexagon_cosine_rules (P : DiscPolygon 6) (ha : P.IsRightAngled) :
    Real.cosh (P.sideLength 3).toReal*Real.sinh (P.sideLength 4).toReal*Real.sinh (P.sideLength 2).toReal=
        Real.cosh (P.sideLength 0).toReal+Real.cosh (P.sideLength 4).toReal*Real.cosh (P.sideLength 2).toReal ∧
      Real.cosh (P.sideLength 1).toReal*Real.sinh (P.sideLength 0).toReal*Real.sinh (P.sideLength 2).toReal=
        Real.cosh (P.sideLength 4).toReal+Real.cosh (P.sideLength 0).toReal*Real.cosh (P.sideLength 2).toReal ∧
      Real.cosh (P.sideLength 5).toReal*Real.sinh (P.sideLength 0).toReal*Real.sinh (P.sideLength 4).toReal=
        Real.cosh (P.sideLength 2).toReal+Real.cosh (P.sideLength 0).toReal*Real.cosh (P.sideLength 4).toReal := by
  have h:=(P.rightHexagon ha).cosine_rules_cyclic
  simpa only [RightHexagon.sideA₁,RightHexagon.sideA₂,RightHexagon.sideA₃,
    RightHexagon.sideB₁,RightHexagon.sideB₂,RightHexagon.sideB₃,P.rightHexagon_edgeLength ha] using h

/-- Equality of the three actual alternating path lengths forces equality of the other three. -/
theorem DiscPolygon.right_hexagon_remaining_sides (P Q : DiscPolygon 6)
    (hP : P.IsRightAngled) (hQ : Q.IsRightAngled)
    (h₁ : (P.sideLength 0).toReal=(Q.sideLength 0).toReal)
    (h₂ : (P.sideLength 4).toReal=(Q.sideLength 4).toReal)
    (h₃ : (P.sideLength 2).toReal=(Q.sideLength 2).toReal) :
    (P.sideLength 3).toReal=(Q.sideLength 3).toReal ∧
      (P.sideLength 1).toReal=(Q.sideLength 1).toReal ∧
      (P.sideLength 5).toReal=(Q.sideLength 5).toReal := by
  have h:=(P.rightHexagon hP).remaining_sides_eq_of_alternating_eq (Q.rightHexagon hQ)
    (by simpa only [RightHexagon.sideA₁,P.rightHexagon_edgeLength hP,Q.rightHexagon_edgeLength hQ] using h₁)
    (by simpa only [RightHexagon.sideA₂,P.rightHexagon_edgeLength hP,Q.rightHexagon_edgeLength hQ] using h₂)
    (by simpa only [RightHexagon.sideA₃,P.rightHexagon_edgeLength hP,Q.rightHexagon_edgeLength hQ] using h₃)
  simpa only [RightHexagon.sideB₁,RightHexagon.sideB₂,RightHexagon.sideB₃,
    P.rightHexagon_edgeLength hP,Q.rightHexagon_edgeLength hQ] using h


end
end LowDimensionalTopology.Geometry.Polygon
