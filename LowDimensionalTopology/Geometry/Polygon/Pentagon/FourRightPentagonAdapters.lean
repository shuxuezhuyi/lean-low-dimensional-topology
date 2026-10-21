/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.LambertPolygonConverse
public import LowDimensionalTopology.Geometry.Polygon.Support.StrictPolygonSupports
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonCornerRegions
public import LowDimensionalTopology.Geometry.Polygon.Pentagon.PentagonNormals
/-! # Actual four-right pentagons and genuine path lengths

The polygon predicate uses its actual numerical Jordan interior angles. With an
explicit remaining-angle bound, strict genuine supports give the incidence
model, its actual fifth angle and all three original finite edge lengths. This
bound is kept visible; its necessity for arbitrary four-right pentagons is a
separate obligation. In the all-right case the bound follows immediately, and
both source specializations hold for every actual Jordan pentagon.
-/
@[expose] public section
namespace LowDimensionalTopology.Geometry.Polygon
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc Topology
noncomputable section

/-- Four genuine numerical right angles; no convexity or remaining-angle conclusion is supplied. -/
def DiscPolygon.IsFourRightPentagon (P : DiscPolygon 5) : Prop :=
  ∀ i : Fin 5,i≠0 → P.angle i=Real.pi/2

def DiscPolygon.pentagonFiniteVertex (P : DiscPolygon 5) (hR : P.IsFourRightPentagon)
    (i : Fin 5) (hi : i≠0) : 𝔻 :=
  P.anglePositiveVertex i (by rw [hR i hi];positivity)

theorem DiscPolygon.pentagonFiniteVertex_spec (P : DiscPolygon 5) (hR : P.IsFourRightPentagon)
    (i : Fin 5) (hi : i≠0) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.pentagonFiniteVertex
      hR i hi)=P.vertices i :=
  P.anglePositiveVertex_spec i _

theorem DiscPolygon.pentagon_orthogonal (P : DiscPolygon 5) (hR : P.IsFourRightPentagon)
    (i : Fin 5) (hi : i≠0) :
    (P.geodesicSide ((finRotate 5).symm i)).OrthogonalAt (P.geodesicSide i) (P.pentagonFiniteVertex hR i hi) :=
  P.adjacent_sides_orthogonal_of_angle_right i _ (P.pentagonFiniteVertex_spec hR i hi).symm (hR i hi)

theorem DiscPolygon.strict_support_same_side {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (ha : ∀ i : Fin n,P.angle i<Real.pi) (i j k : Fin n) (z w : 𝔻)
    (hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z=P.vertices j) (hw :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w=P.vertices k)
    (hji : j≠i) (hjn : j≠finRotate n i) (hki : k≠i) (hkn : k≠finRotate n i) :
    0<(P.geodesicSide i).toHalfPlane.normalTimeAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)*
      (P.geodesicSide i).toHalfPlane.normalTimeAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) := by
  let S:=P.strictSupportData hc ha
  obtain ⟨c,hc0,hn,ht⟩:=S.toCenteredData.support_normal_proportional i
  rw [P.strictSupportData_supportLine hc ha] at hn ht
  change (P.geodesicSide i).incenterNormal=c • S.normals i at hn
  change (P.geodesicSide i).incenterOffset=c*S.offsets i at ht
  have hzK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices j):=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,hz]
  have hwK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices k):=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,hw]
  have hj : inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
    j))-S.offsets i<0:=
    sub_neg.mpr (S.nonincident i j hji hjn)
  have hk : inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
    k))-S.offsets i<0:=
    sub_neg.mpr (S.nonincident i k hki hkn)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalTimeAt_eq_affine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalTimeAt_eq_affine]
  change 0<(-_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight _*(inner ℝ (P.geodesicSide
    i).incenterNormal
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate _)-(P.geodesicSide i).incenterOffset))*
    (-_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight _*(inner ℝ (P.geodesicSide
      i).incenterNormal
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate _)-(P.geodesicSide i).incenterOffset))
  rw [hzK,hwK,hn,ht]
  simp only [real_inner_smul_left]
  have hp:=mul_pos (mul_self_pos.mpr hc0)
    (mul_pos (mul_pos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_pos
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_pos
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w))) (mul_pos_of_neg_of_neg hj hk))
  convert hp using 1
  ring

def DiscPolygon.asFourRightPentagon (P : DiscPolygon 5) (hc : P.IsConvex)
    (ha : ∀ i : Fin 5,P.angle i<Real.pi) (hR : P.IsFourRightPentagon) : FourRightPentagon where
  corner:=P.strictCornerTriangle hc ha 0
  a:=P.pentagonFiniteVertex hR 2 (by decide)
  b:=P.pentagonFiniteVertex hR 1 (by decide)
  d:=P.pentagonFiniteVertex hR 4 (by decide)
  e:=P.pentagonFiniteVertex hR 3 (by decide)
  vertex_d:=(P.pentagonFiniteVertex_spec hR 4 (by decide)).symm
  vertex_b:=(P.pentagonFiniteVertex_spec hR 1 (by decide)).symm
  top:=P.geodesicSide 2
  right:=P.geodesicSide 1
  left:=P.geodesicSide 3
  angle_a:=by
    have h:=P.pentagon_orthogonal hR 2 (by decide)
    exact ⟨h.2.1,h.1,(real_inner_comm _ _).trans h.2.2⟩
  angle_b:=by
    rw [P.strictCornerTriangle_sideB]
    have h:=P.pentagon_orthogonal hR 1 (by decide)
    exact ⟨h.2.1,h.1,(real_inner_comm _ _).trans h.2.2⟩
  angle_e:=P.pentagon_orthogonal hR 3 (by decide)
  angle_d:=by
    rw [P.strictCornerTriangle_sideC]
    exact P.pentagon_orthogonal hR 4 (by decide)
  convex_a:=by
    change 0<((P.strictCornerTriangle hc ha 0).coordinate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel _)).1 ∧
      0<((P.strictCornerTriangle hc ha 0).coordinate
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel _)).2
    rw [P.pentagonFiniteVertex_spec]
    exact P.strictCornerTriangle_vertex_coordinates_pos hc ha 0 2 (by decide) (by decide) (by decide)
  convex_e:=by
    change 0<((P.strictCornerTriangle hc ha 0).coordinate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel _)).1 ∧
      0<((P.strictCornerTriangle hc ha 0).coordinate
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel _)).2
    rw [P.pentagonFiniteVertex_spec]
    exact P.strictCornerTriangle_vertex_coordinates_pos hc ha 0 3 (by decide) (by decide) (by decide)
  top_same_side:=P.strict_support_same_side hc ha 2 1 4 _ _
    (P.pentagonFiniteVertex_spec hR 1 (by decide)) (P.pentagonFiniteVertex_spec hR 4 (by decide))
    (by decide) (by decide) (by decide) (by decide)

theorem DiscPolygon.fourRightPentagon_angle_eq (P : DiscPolygon 5) (hc : P.IsConvex)
    (ha : ∀ i : Fin 5,P.angle i<Real.pi) (hR : P.IsFourRightPentagon) :
    (P.asFourRightPentagon hc ha hR).angle=P.angle 0 := P.strictCornerTriangle_angle hc ha 0

theorem DiscPolygon.fourRightPentagon_angle_bounds (P : DiscPolygon 5) (hR : P.IsFourRightPentagon)
    (hφ : P.angle 0<Real.pi) : ∀ i : Fin 5,P.angle i<Real.pi := by
  intro i
  by_cases hi : i=0
  · simpa only [hi] using hφ
  · rw [hR i hi]
    linarith only [Real.pi_pos]

/-- This adapter explicitly retains the remaining-angle bound until its general polygon necessity is proved. -/
def DiscPolygon.fourRightPentagonOfAngleLtPi (P : DiscPolygon 5) (hR : P.IsFourRightPentagon)
    (hφ : P.angle 0<Real.pi) : FourRightPentagon :=
  P.asFourRightPentagon (P.isConvex_of_angles_le_pi (fun i=>(P.fourRightPentagon_angle_bounds hR hφ i).le))
    (P.fourRightPentagon_angle_bounds hR hφ) hR

theorem DiscPolygon.fourRightPentagonOfAngleLtPi_angle (P : DiscPolygon 5) (hR : P.IsFourRightPentagon)
    (hφ : P.angle 0<Real.pi) : (P.fourRightPentagonOfAngleLtPi hR hφ).angle=P.angle 0 :=
  P.fourRightPentagon_angle_eq _ _ hR

theorem DiscPolygon.fourRightPentagonOfAngleLtPi_sideA (P : DiscPolygon 5) (hR : P.IsFourRightPentagon)
    (hφ : P.angle 0<Real.pi) : (P.fourRightPentagonOfAngleLtPi hR hφ).sideA=(P.sideLength 1).toReal := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (P.pentagonFiniteVertex hR 2 (by decide)) (P.pentagonFiniteVertex hR 1 (by decide))=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength (P.vertices 1) (P.vertices 2)).toReal
  rw [←P.pentagonFiniteVertex_spec hR 1 (by decide),←P.pentagonFiniteVertex_spec hR 2 (by decide),
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength_finite,ENNReal.toReal_ofReal (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane];exact dist_nonneg)]
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane,dist_comm]

theorem DiscPolygon.fourRightPentagonOfAngleLtPi_sideB (P : DiscPolygon 5) (hR : P.IsFourRightPentagon)
    (hφ : P.angle 0<Real.pi) : (P.fourRightPentagonOfAngleLtPi hR hφ).sideB=(P.sideLength 2).toReal := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (P.pentagonFiniteVertex hR 2 (by decide)) (P.pentagonFiniteVertex hR 3 (by decide))=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength (P.vertices 2) (P.vertices 3)).toReal
  rw [←P.pentagonFiniteVertex_spec hR 2 (by decide),←P.pentagonFiniteVertex_spec hR 3 (by decide),
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength_finite,ENNReal.toReal_ofReal (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane];exact dist_nonneg)]

theorem DiscPolygon.fourRightPentagonOfAngleLtPi_sideC (P : DiscPolygon 5) (hR : P.IsFourRightPentagon)
    (hφ : P.angle 0<Real.pi) : (P.fourRightPentagonOfAngleLtPi hR hφ).sideC=(P.sideLength 3).toReal := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (P.pentagonFiniteVertex hR 3 (by decide)) (P.pentagonFiniteVertex hR 4 (by decide))=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength (P.vertices 3) (P.vertices 4)).toReal
  rw [←P.pentagonFiniteVertex_spec hR 3 (by decide),←P.pentagonFiniteVertex_spec hR 4 (by decide),
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength_finite,ENNReal.toReal_ofReal (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane];exact dist_nonneg)]

theorem DiscPolygon.fourRightPentagonOfAngleLtPi_adjacentSide (P : DiscPolygon 5) (hR : P.IsFourRightPentagon)
    (hφ : P.angle 0<Real.pi) (z : 𝔻) (hz : P.vertices
      0=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (P.fourRightPentagonOfAngleLtPi hR hφ).d z=(P.sideLength 4).toReal := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (P.pentagonFiniteVertex hR 4 (by decide)) z=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength (P.vertices 4) (P.vertices 0)).toReal
  rw [hz,←P.pentagonFiniteVertex_spec hR 4 (by decide),_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength_finite,
    ENNReal.toReal_ofReal (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane];exact dist_nonneg)]

/-- Actual side-length formula under an explicit remaining-angle bound. -/
theorem DiscPolygon.fourRightPentagon_cosh_identity_of_angle_lt_pi (P : DiscPolygon 5) (hR : P.IsFourRightPentagon)
    (hφ : P.angle 0<Real.pi) :
    Real.cosh (P.sideLength 1).toReal*Real.cosh (P.sideLength 3).toReal+Real.cos (P.angle 0)=
      Real.sinh (P.sideLength 1).toReal*Real.cosh (P.sideLength 2).toReal*Real.sinh (P.sideLength 3).toReal := by
  have h:=(P.fourRightPentagonOfAngleLtPi hR hφ).cosh_side_cosh_side_add_cos_angle_identity
  simpa only [P.fourRightPentagonOfAngleLtPi_angle hR hφ,P.fourRightPentagonOfAngleLtPi_sideA hR hφ,
    P.fourRightPentagonOfAngleLtPi_sideB hR hφ,P.fourRightPentagonOfAngleLtPi_sideC hR hφ] using h

/-- The source all-right-angle specialization holds for every actual right-angled Jordan pentagon. -/
theorem DiscPolygon.rightPentagon_tanh_cosh_tanh_identity (P : DiscPolygon 5) (hR : P.IsFourRightPentagon)
    (h0 : P.angle 0=Real.pi/2) :
    Real.tanh (P.sideLength 1).toReal*Real.cosh (P.sideLength 2).toReal*Real.tanh (P.sideLength 3).toReal=1 := by
  have hφ : P.angle 0<Real.pi:=by rw [h0];linarith only [Real.pi_pos]
  have he : (P.fourRightPentagonOfAngleLtPi hR hφ).angle=Real.pi/2:=
    (P.fourRightPentagonOfAngleLtPi_angle hR hφ).trans h0
  have h:=(P.fourRightPentagonOfAngleLtPi hR hφ).tanh_side_cosh_side_tanh_side_eq_one_of_right he
  simpa only [P.fourRightPentagonOfAngleLtPi_sideA hR hφ,P.fourRightPentagonOfAngleLtPi_sideB hR hφ,
    P.fourRightPentagonOfAngleLtPi_sideC hR hφ] using h

/-- The second exact source all-right-angle specialization uses the actual fifth path side length. -/
theorem DiscPolygon.rightPentagon_sinh_mul_sinh_eq_cosh_opposite (P : DiscPolygon 5) (hR : P.IsFourRightPentagon)
    (h0 : P.angle 0=Real.pi/2) :
    Real.sinh (P.sideLength 1).toReal*Real.sinh (P.sideLength 2).toReal=Real.cosh (P.sideLength 4).toReal := by
  have hφ : P.angle 0<Real.pi:=by rw [h0];linarith only [Real.pi_pos]
  have he : (P.fourRightPentagonOfAngleLtPi hR hφ).angle=Real.pi/2:=
    (P.fourRightPentagonOfAngleLtPi_angle hR hφ).trans h0
  obtain ⟨z,hz,h⟩:=(P.fourRightPentagonOfAngleLtPi hR
    hφ).exists_finite_corner_and_sinh_side_mul_eq_cosh_opposite_of_right he
  have hv : P.vertices 0=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z:=hz
  simpa only [P.fourRightPentagonOfAngleLtPi_sideA hR hφ,P.fourRightPentagonOfAngleLtPi_sideB hR hφ,
    P.fourRightPentagonOfAngleLtPi_adjacentSide hR hφ z hv] using h

end
end LowDimensionalTopology.Geometry.Polygon
