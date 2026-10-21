/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Polygon.Support.ConvexDiscPolygonSupports
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonStraightAngles
/-! # Strict actual supporting lines from genuine polygon angle bounds -/
@[expose] public section
namespace LowDimensionalTopology.Geometry.Polygon
open Set InnerProductGeometry
open scoped Complex.UnitDisc Topology
noncomputable section

theorem DiscPolygon.finite_corner_proper_of_angle_ne_pi {n : ℕ} (P : DiscPolygon n) (i : Fin n)
    (z : 𝔻) (hz : P.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) (ha : P.angle
      i≠Real.pi) :
    (P.cornerRayPrev i z hz).supportLine≠(P.cornerRayNext i z hz).supportLine :=
  fun he => ha (P.angle_eq_pi_of_same_support i z hz he)

theorem DiscPolygon.all_vertices_extreme_of_angles_lt_pi {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (ha : ∀ i : Fin n,P.angle i<Real.pi) :
    ∀ i : Fin n,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
      i)∈P.kleinBody.extremePoints ℝ :=
  P.all_vertices_extreme_of_finite_proper hc (fun i z hz =>
    P.finite_corner_proper_of_angle_ne_pi i z hz (ha i).ne)

def DiscPolygon.strictSupportData {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (ha : ∀ i : Fin n,P.angle i<Real.pi) : CyclicDiscPolygonSupportData n :=
  P.supportDataOfExtreme hc (P.all_vertices_extreme_of_angles_lt_pi hc ha)

theorem DiscPolygon.strictSupportData_vertices {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (ha : ∀ i : Fin n,P.angle i<Real.pi) : (P.strictSupportData hc ha).vertices=P.vertices := rfl

theorem DiscPolygon.strictSupportData_toDiscPolygon {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (ha : ∀ i : Fin n,P.angle i<Real.pi) : (P.strictSupportData hc ha).toDiscPolygon=P :=
  P.supportDataOfExtreme_toDiscPolygon hc (P.all_vertices_extreme_of_angles_lt_pi hc ha)

theorem DiscPolygon.strictSupportData_supportLine {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (ha : ∀ i : Fin n,P.angle i<Real.pi) (i : Fin n) :
    ((P.strictSupportData hc ha).toCenteredData.supportLine i)=P.geodesicSide i :=
  P.supportDataOfExtreme_supportLine hc (P.all_vertices_extreme_of_angles_lt_pi hc ha) i

def DiscPolygon.strictCornerTriangle {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (ha : ∀ i : Fin n,P.angle i<Real.pi) (i : Fin
      n) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle :=
  (P.strictSupportData hc ha).toCenteredData.cornerTriangle i

theorem DiscPolygon.strictCornerTriangle_angle {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (ha : ∀ i : Fin n,P.angle i<Real.pi) (i : Fin n) :
    (P.strictCornerTriangle hc ha i).alpha=P.angle i := by
  have h:=(P.strictSupportData hc ha).toDiscPolygon_angle i
  rw [P.strictSupportData_toDiscPolygon hc ha] at h
  exact h.symm

theorem DiscPolygon.strictCornerTriangle_sideB {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (ha : ∀ i : Fin n,P.angle i<Real.pi) (i : Fin n) :
    (P.strictCornerTriangle hc ha i).sideLineB=P.geodesicSide i := by
  rw [DiscPolygon.strictCornerTriangle,CenteredDiscPolygonSupportData.cornerTriangle_sideB,P.strictSupportData_supportLine]

theorem DiscPolygon.strictCornerTriangle_sideC {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (ha : ∀ i : Fin n,P.angle i<Real.pi) (i : Fin n) :
    (P.strictCornerTriangle hc ha i).sideLineC=P.geodesicSide ((finRotate n).symm i) := by
  rw [DiscPolygon.strictCornerTriangle,CenteredDiscPolygonSupportData.cornerTriangle_sideC,P.strictSupportData_supportLine]

theorem DiscPolygon.strictCornerTriangle_vertex_coordinates_pos {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (ha : ∀ i : Fin n,P.angle i<Real.pi) (i j : Fin n)
    (hji : j≠i) (hjprev : j≠(finRotate n).symm i) (hjnext : j≠finRotate n i) :
    0<((P.strictCornerTriangle hc ha i).coordinate (P.vertices j)).1 ∧
      0<((P.strictCornerTriangle hc ha i).coordinate (P.vertices j)).2 := by
  let S:=(P.strictSupportData hc ha).toCenteredData
  constructor
  · exact (S.cornerTriangle_outgoing_cut i (P.vertices j)).mp (S.nonincident i j hji hjnext)
  · apply (S.cornerTriangle_incoming_cut i (P.vertices j)).mp
    exact S.nonincident ((finRotate n).symm i) j hjprev
      (by simpa only [Equiv.apply_symm_apply] using hji)


theorem DiscPolygon.strict_quadrilateral_opposite_chord (P : DiscPolygon 4) (hc : P.IsConvex)
    (ha : ∀ i : Fin 4,P.angle i<Real.pi) :
    1<((P.strictCornerTriangle hc ha 0).coordinate (P.vertices 2)).1+
      ((P.strictCornerTriangle hc ha 0).coordinate (P.vertices 2)).2 := by
  let S:=(P.strictSupportData hc ha).toCenteredData
  let T:=P.strictCornerTriangle hc ha 0
  have hp:=P.strictCornerTriangle_vertex_coordinates_pos hc ha 0 2 (by decide) (by decide) (by decide)
  have hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine (S.normals 2) (S.offsets 2) T.a<0 :=
    sub_neg.mpr (S.nonincident 2 0 (by decide) (by decide))
  have hD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine (S.normals 2) (S.offsets 2) T.b=0 :=
    sub_eq_zero.mpr (S.incident 2).2
  have hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine (S.normals 2) (S.offsets 2) T.c<0 :=
    sub_neg.mpr (S.nonincident 2 1 (by decide) (by decide))
  have hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine (S.normals 2) (S.offsets
    2) (P.vertices 2)=0 :=
    sub_eq_zero.mpr (S.incident 2).1
  have he:=T.kleinAffine_reconstruction (S.normals 2) (S.offsets 2) (P.vertices 2)
  rw [hA,hD,mul_zero,add_zero] at he
  by_contra hn
  have hsum : 0≤1-(T.coordinate (P.vertices 2)).1-(T.coordinate (P.vertices 2)).2 := by
    change ¬1<(T.coordinate (P.vertices 2)).1+(T.coordinate (P.vertices 2)).2 at hn
    linarith
  have hterm1:=mul_nonpos_of_nonneg_of_nonpos hsum hC.le
  have hterm2:=mul_neg_of_pos_of_neg hp.2 hB
  linarith only [he,hterm1,hterm2]


end
end LowDimensionalTopology.Geometry.Polygon
