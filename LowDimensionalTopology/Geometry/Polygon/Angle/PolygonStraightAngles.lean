/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonBoundaryConvexity
/-! # Actual straight polygon corner angles

Genuine no-backtracking at a collinear polygon corner forces its two actual
forward rays to be opposite and hence gives exactly angle pi.
-/
set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Set Filter
open scoped Topology Complex.UnitDisc UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- Any collinear genuine native corner lies between its two actual neighbors. -/
theorem DiscPolygon.klein_vertex_between_of_collinear {n : ℕ} (P : DiscPolygon n) (i : Fin n)
    (hc : Collinear ℝ ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices ((finRotate
      n).symm i)),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
        i),_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n
        i))} : Set ℂ)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i) ∈ openSegment ℝ
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices ((finRotate n).symm i)))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i))) := by
  let e := LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv
  have hc' := polygon_collinear_affine_image e.symm.toLinearEquiv.toAffineEquiv.toAffineMap hc
  simp only [image_insert_eq,image_singleton] at hc'
  have hindex := P.jordanIndexEquiv_sub_one (P.jordanIndexEquiv i)
  rw [Equiv.symm_apply_apply] at hindex
  have hindexn := P.jordanIndexEquiv_add_one (P.jordanIndexEquiv i)
  rw [Equiv.symm_apply_apply] at hindexn
  have hcJ : Collinear ℝ ({P.toPolygonalCircle.vertex (P.jordanIndexEquiv i-(1 : ZMod n)),
      P.toPolygonalCircle.vertex (P.jordanIndexEquiv i),
      P.toPolygonalCircle.vertex (P.jordanIndexEquiv i+(1 : ZMod n))} : Set _) := by
    change Collinear ℝ ({e.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
      (P.jordanIndexEquiv.symm (P.jordanIndexEquiv i-1)))),
      e.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
        (P.jordanIndexEquiv.symm (P.jordanIndexEquiv i)))),
      e.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
        (P.jordanIndexEquiv.symm (P.jordanIndexEquiv i+1))))} : Set _)
    rw [hindex,Equiv.symm_apply_apply,hindexn]
    exact hc'
  have h := polygonalCircle_collinear_vertex_between P.toPolygonalCircle (P.jordanIndexEquiv i) hcJ
  have hopen : e '' openSegment ℝ (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i-(1 : ZMod n)))
      (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i+(1 : ZMod n))) =
      openSegment ℝ (e (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i-(1 : ZMod n))))
        (e (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i+(1 : ZMod n)))) :=
    image_openSegment ℝ e.toLinearEquiv.toAffineEquiv.toAffineMap _ _
  have h' := mem_image_of_mem e h
  rw [hopen] at h'
  change e (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i)) ∈ _ at h'
  change e (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i)) ∈ openSegment ℝ
    (e (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i-(1 : ZMod n))))
    (e (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i+(1 : ZMod n)))) at h'
  change LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv
    (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i)) ∈ openSegment ℝ
      (LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv
        (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i-(1 : ZMod n))))
      (LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv
        (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i+(1 : ZMod n)))) at h'
  simpa only [P.toPolygonalCircle_complex_vertex,hindex,hindexn,Equiv.symm_apply_apply] using h'

/-- The left endpoint of a genuine segment is an actual extreme point. -/
theorem polygon_segment_left_extreme {a e b c : ℂ} (hae : a ≠ e)
    (hb : b ∈ segment ℝ a e) (hc : c ∈ segment ℝ a e)
    (ha : a ∈ openSegment ℝ b c) : b = a := by
  rw [segment_eq_image_lineMap] at hb hc
  obtain ⟨s,hs,rfl⟩ := hb
  obtain ⟨t,ht,rfl⟩ := hc
  rw [openSegment_eq_image_lineMap] at ha
  obtain ⟨u,hu,he⟩ := ha
  have hscalar : AffineMap.lineMap s t u = 0 := by
    apply AffineMap.lineMap_injective ℝ hae
    rw [AffineMap.apply_lineMap,he,AffineMap.lineMap_apply_zero]
  change u*(t-s)+s = 0 at hscalar
  have hs0 : s = 0 := by
    by_contra hn
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hn)
    have hpos : 0 < (1-u)*s := mul_pos (sub_pos.mpr hu.2) hspos
    have hnonneg : 0 ≤ u*t := mul_nonneg hu.1.le ht.1
    nlinarith only [hscalar,hpos,hnonneg]
  rw [hs0,AffineMap.lineMap_apply_zero]

/-- On the same genuine h-line, the actual longitudinal orientation determines a ray uniquely. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.eq_of_support_tangentSign {z : ℍ} (R S :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt z)
    (hL : R.supportLine = S.supportLine) (hs : R.tangentSign = S.tangentSign) : R = S := by
  have hφ : R.longitudinal = S.longitudinal := by
    funext x
    exact congrArg (fun L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine => L.longitudinal (x :
      ℂ)) hL
  have hdir : (R.longitudinal z < R.longitudinal R.directionPoint) ↔
      S.longitudinal z < S.longitudinal S.directionPoint := by
    by_cases hR : R.longitudinal z < R.longitudinal R.directionPoint <;>
      by_cases hS : S.longitudinal z < S.longitudinal S.directionPoint
    · exact iff_of_true hR hS
    · have h := hs
      norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.tangentSign,hR,hS] at h
    · have h := hs
      norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.tangentSign,hR,hS] at h
    · exact iff_of_false hR hS
  apply Subtype.ext
  ext x
  by_cases hx : x ∈ R.supportLine.carrier
  · have hxS : x ∈ S.supportLine.carrier := hL ▸ hx
    rw [R.mem_iff_longitudinal hx,S.mem_iff_longitudinal hxS]
    rw [hφ]
    by_cases hr : S.longitudinal z < S.longitudinal R.directionPoint
    · have hs' := hdir.mp (by simpa only [hφ] using hr)
      simp only [hr,hs',ite_true]
    · have hs' : ¬ S.longitudinal z < S.longitudinal S.directionPoint :=
        fun hh => hr (by simpa only [hφ] using hdir.mpr hh)
      simp only [hr,hs',ite_false]
  · exact iff_of_false (fun h => hx (R.subset_support h))
      (fun h => hx (hL.symm ▸ S.subset_support h))

/-- Two distinct actual rays on one support have opposite Euclidean forward tangents. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.tangentVector_neg_of_same_support {z : ℍ} (R S :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt z)
    (hL : R.supportLine = S.supportLine) (hRS : R ≠ S) : S.tangentVector = -R.tangentVector := by
  have hsign : R.tangentSign ≠ S.tangentSign := fun he => hRS (R.eq_of_support_tangentSign S hL he)
  have hn : S.tangentSign = -R.tangentSign := by
    have hp : (S.tangentSign-R.tangentSign)*(S.tangentSign+R.tangentSign) = 0 := by
      nlinarith only [R.tangentSign_sq,S.tangentSign_sq]
    have hz := (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr (Ne.symm hsign))
    linarith only [hz]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.tangentVector,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.tangentVector,hn,← hL,neg_smul]

/-- The actual Euclidean forward-tangent angle of opposite H rays is exactly pi. -/
theorem hInteriorAngleMeasure_eq_pi_of_same_support {z : ℍ} (R S :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt z)
    (hL : R.supportLine = S.supportLine) (hRS : R ≠ S) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S = Real.pi := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure,R.tangentVector_neg_of_same_support S hL
    hRS]
  exact InnerProductGeometry.angle_self_neg_of_nonzero R.tangentVector_ne_zero

/-- Every actual native ray has the genuine compactified finite-to-ideal segment as its closure. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.exists_closedClosure_segment {z : 𝔻} (R :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt z) :
    ∃ w : 𝕔𝔻, ‖(w : ℂ)‖ = 1 ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure R.val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) w := by
  obtain ⟨w,hw,he⟩ := R.idealEndpoint_mem
  have hwn : ‖w‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hw
  let W := Complex.UnitClosedDisc.mk w hwn.le
  have hE : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended W = R.idealEndpoint := he
  refine ⟨W,hwn,?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_ray z W
    hwn,hE,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay_eq_of_isDiscHLineRay R.isRay]
  rfl

/-- The actual two adjacent forward rays at any finite genuine polygon vertex are distinct. -/
theorem DiscPolygon.cornerRays_ne {n : ℕ} (P : DiscPolygon n) (i : Fin n) (z : 𝔻)
    (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) : P.cornerRayPrev i z hz ≠ P.cornerRayNext i z hz := by
  intro he
  have hL := congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.supportLine he
  have hc := P.klein_neighbors_collinear_of_same_support i z hz hL
  have hmid := P.klein_vertex_between_of_collinear i hc
  let R := P.cornerRayPrev i z hz
  have hb : P.vertices ((finRotate n).symm
    i) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure R.val :=
    discRayTowardClosed_endpoint_mem z _ (by
      rw [← hz]
      exact fun hh => P.prev_ne_self i (P.vertices_injective hh).symm)
  have hn : P.vertices (finRotate n
    i) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.cornerRayNext i z hz).val :=
    discRayTowardClosed_endpoint_mem z _ (by
      rw [← hz]
      exact fun hh => P.next_ne_self i (P.vertices_injective hh).symm)
  rw [← he] at hn
  obtain ⟨w,hw,hR⟩ := R.exists_closedClosure_segment
  rw [← hz] at hR
  have hne : P.vertices i ≠ w := by
    intro hh
    have hn := congrArg (fun p : 𝕔𝔻 => ‖(p : ℂ)‖) hh
    rw [hz,hw] at hn
    exact (ne_of_lt z.norm_lt_one) hn
  have hbK := mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (hR ▸ hb)
  have hnK := mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (hR ▸ hn)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment] at hbK hnK
  have hh := polygon_segment_left_extreme (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hne) hbK hnK hmid
  exact P.prev_ne_self i (P.vertices_injective
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective hh))

/-- A same-support true finite polygon corner has exactly its genuine straight interior angle. -/
theorem DiscPolygon.angle_eq_pi_of_same_support {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hL : (P.cornerRayPrev i z hz).supportLine = (P.cornerRayNext i z hz).supportLine) :
    P.angle i = Real.pi := by
  apply P.angle_eq_pi_of_straight i z hz
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure_eq_halfPlane]
  apply hInteriorAngleMeasure_eq_pi_of_same_support
  · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.support_eq_iff _ _).mp hL
  · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRayHalfPlaneEquiv z).injective.ne (P.cornerRays_ne i z
    hz)

end
end LowDimensionalTopology.Geometry.Polygon
