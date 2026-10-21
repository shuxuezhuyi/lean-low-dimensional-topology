/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.SaccheriPolygonAdapters
public import LowDimensionalTopology.Geometry.Polygon.Support.ConvexDiscPolygonSupports
/-! # Intrinsic Lambert geometry for arbitrary actual Jordan quadrilaterals

Three genuine right angles force the convex position required by the incidence
model. Timelike Lorentz coordinates give this implication also when the fourth
vertex is ideal. Reversing the model's actual cyclic support data reconstructs
the input Jordan polygon exactly, proving its genuine interior angle and
convexity. No convexity or fourth-angle bound is supplied as a hypothesis.

Both source identities are stated with the actual polygon side lengths. The
second explicitly uses a finite fourth vertex, since its adjacent side must be
a real length; the first includes the ideal case.
-/
@[expose] public section
namespace LowDimensionalTopology.Geometry.Polygon
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc Topology
noncomputable section

theorem lorentz_positive_time (X p : ℂ) (H : ℝ) (hH : 0<H)
    (hu : H^2-‖X‖^2=1) (hp : ‖p‖≤1) : 0<H-inner ℝ X p := by
  have hi:=(real_inner_mul_inner_self_le X p)
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hi
  have hp2 : ‖p‖^2≤1:=by nlinarith [norm_nonneg p]
  have hbound : (inner ℝ X p)^2≤‖X‖^2 := by
    nlinarith [mul_nonneg (sq_nonneg ‖X‖) (sub_nonneg.mpr hp2)]
  by_contra hn
  have hge : H≤ inner ℝ X p:=by linarith
  have hs : H^2≤(inner ℝ X p)^2:=(sq_le_sq₀ hH.le (hH.le.trans hge)).mpr hge
  nlinarith only [hs,hbound,hu]

def restTime (a : ℍ) (p : 𝕔𝔻) : ℝ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a-inner ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p)

def restSpatial (a : ℍ) (p : 𝕔𝔻) : ℂ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.sideNormalBoost (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) 1

theorem restTime_pos (a : ℍ) (p : 𝕔𝔻) : 0<restTime a p := by
  apply lorentz_positive_time _ _ _ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_pos a)
  · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_lorentz_unit a
  · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein p).norm_le_one

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.restSpatial_dual (L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a : ℍ) (p : 𝕔𝔻) :
    inner ℝ (L.normalSpatialAt a) (restSpatial a p)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine L.incenterNormal L.incenterOffset p+L.normalTimeAt a*restTime a p := by
  have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.sideNormalBoost_inner (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a)
    L.incenterNormal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) L.incenterOffset 1
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_lorentz_unit a) (by linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_pos a])
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalSpatialAt,restSpatial,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalTimeAt,restTime,mul_one,real_inner_comm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial a)] using h

theorem restTime_finite (a z : ℍ) :
    restTime a (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))=Real.cosh (dist a z)/_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight z := by
  have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePoint_cosh_distance a z
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial,inner_smul_right] at h
  unfold restTime
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a-inner ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)=_
  apply (eq_div_iff (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_pos z).ne').mpr
  unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial
  nlinarith only [h]

theorem restTime_center (a : ℍ) :
    restTime a (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a))=1/_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a := by
  rw [restTime_finite,dist_self,Real.cosh_zero]

theorem restSpatial_center (a : ℍ) : restSpatial a (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a))=0 := by
  have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePoint_boost_norm a a
  rw [dist_self,Real.cosh_zero,one_pow,sub_self] at h
  have hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.sideNormalBoost (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial
        a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a)=0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp h)
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.sideNormalBoost (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial
        a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a)=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a • restSpatial a (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a)) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.sideNormalBoost (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a •
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
        a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a • _root_.LowDimensionalTopology.Geometry.Hyperbolic.sideNormalBoost (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate a) 1
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.sideNormalBoost,real_inner_smul_left,smul_smul,smul_add,div_eq_mul_inv]
    module
  rw [he] at hz
  exact (smul_eq_zero.mp hz).resolve_left (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_pos
    a).ne'


theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.restAffine_center (L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine L.incenterNormal L.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a))=
      -L.normalTimeAt a*restTime a (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a)) := by
  have h:=L.restSpatial_dual a (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a))
  rw [restSpatial_center,inner_zero_right] at h
  linarith only [h]

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.restAffine_on_transverse (K N M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a d : ℍ)
    (ha : K.OrthogonalAt N a) (hd : N.OrthogonalAt M d) (p : 𝕔𝔻)
    (hp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine K.incenterNormal K.incenterOffset
      p=0) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine M.incenterNormal M.incenterOffset p=-M.normalTimeAt a*restTime a p := by
  have hKa:=(K.normalTimeAt_eq_zero_iff a).mpr ha.1
  have hNa:=(N.normalTimeAt_eq_zero_iff a).mpr ha.2.1
  have hK:=K.normalSpatialAt_norm_sq a
  have hN:=N.normalSpatialAt_norm_sq a
  rw [hKa,zero_pow (by decide : 2≠0),add_zero] at hK
  rw [hNa,zero_pow (by decide : 2≠0),add_zero] at hN
  have hKN:=K.normalSpatialAt_inner N a
  rw [K.normalPairing_orthogonal N a ha,hKa,zero_mul,add_zero] at hKN
  have hNM:=N.normalPairing_orthogonal M d hd
  have hMN : M.normalPairing N=0 := by
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalPairing,real_inner_comm,mul_comm] using hNM
  have hMNsp:=M.normalSpatialAt_inner N a
  rw [hMN,hNa,mul_zero,add_zero] at hMNsp
  have hKp:=K.restSpatial_dual a p
  rw [hp,hKa,zero_mul,add_zero] at hKp
  have horth:=complex_inner_zero_of_orthogonal_complements (K.normalSpatialAt a) (N.normalSpatialAt a)
    (restSpatial a p) (M.normalSpatialAt a) hK hN hKN ((real_inner_comm _ _).trans hKp) hMNsp
  have hdual:=M.restSpatial_dual a p
  rw [real_inner_comm, horth] at hdual
  linarith only [hdual]

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.transverse_affine_product_pos (K N M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a d : ℍ)
    (ha : K.OrthogonalAt N a) (hd : N.OrthogonalAt M d) (haM : a∉M.carrier)
    (p : 𝕔𝔻) (hp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine K.incenterNormal
      K.incenterOffset p=0) :
    0<_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine M.incenterNormal M.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a))*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine M.incenterNormal M.incenterOffset p := by
  have hne : M.normalTimeAt a≠0:=fun he => haM ((M.normalTimeAt_eq_zero_iff a).mp he)
  rw [M.restAffine_center,K.restAffine_on_transverse N M a d ha hd p hp]
  have hpos:=mul_pos (mul_self_pos.mpr hne)
    (mul_pos (restTime_pos a (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a))) (restTime_pos a p))
  convert hpos using 1
  ring

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.restTime_reconstruction (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (a : ℍ) (p : 𝕔𝔻) :
    restTime a p=(1-(T.coordinate p).1-(T.coordinate p).2)*restTime a T.a+
      (T.coordinate p).1*restTime a T.b+(T.coordinate p).2*restTime a T.c := by
  have h:=T.kleinAffine_reconstruction (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial
    a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a) p
  unfold restTime _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine at *
  linarith only [h]

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.restSpatial_reconstruction (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (a : ℍ) (p : 𝕔𝔻) :
    restSpatial a p=(1-(T.coordinate p).1-(T.coordinate p).2) • restSpatial a T.a+
      (T.coordinate p).1 • restSpatial a T.b+(T.coordinate p).2 • restSpatial a T.c := by
  unfold restSpatial _root_.LowDimensionalTopology.Geometry.Hyperbolic.sideNormalBoost
  rw [T.klein_reconstruction p]
  simp only [inner_add_left,inner_sub_left,real_inner_smul_left,sub_smul,div_eq_mul_inv]
  module



theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.perpendicular_other_point_not_mem (N M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a d : ℍ)
    (hd : N.OrthogonalAt M d) (ha : a∈N.carrier) (had : a≠d) : a∉M.carrier := by
  intro ham
  exact (N.ne_of_orthogonalAt M d hd) (N.eq_of_two_points M had ha hd.1 ham hd.2.1)

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.coordinates_pos_of_side_products (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (p : 𝕔𝔻)
    (hx : 0<_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineB.incenterNormal
      T.sideLineB.incenterOffset p*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset T.b)
    (hy : 0<_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineC.incenterNormal
      T.sideLineC.incenterOffset p*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset T.c) :
    0<(T.coordinate p).1 ∧ 0<(T.coordinate p).2 := by
  have hbA:=(T.sideLineB.closed_incenter_affine_zero_iff _).mpr T.a_mem_sideLineB
  have hbC:=(T.sideLineB.closed_incenter_affine_zero_iff _).mpr T.c_mem_sideLineB
  have hcA:=(T.sideLineC.closed_incenter_affine_zero_iff _).mpr T.a_mem_sideLineC
  have hcB:=(T.sideLineC.closed_incenter_affine_zero_iff _).mpr T.b_mem_sideLineC
  have heB:=T.kleinAffine_reconstruction T.sideLineB.incenterNormal T.sideLineB.incenterOffset p
  have heC:=T.kleinAffine_reconstruction T.sideLineC.incenterNormal T.sideLineC.incenterOffset p
  rw [hbA,hbC,mul_zero,mul_zero,zero_add,add_zero] at heB
  rw [hcA,hcB,mul_zero,mul_zero,zero_add,zero_add] at heC
  rw [heB,mul_assoc] at hx
  rw [heC,mul_assoc] at hy
  exact ⟨pos_of_mul_pos_left hx (mul_self_nonneg _),pos_of_mul_pos_left hy (mul_self_nonneg _)⟩



theorem closedDiscKleinAffine_finite_cayley (n : ℂ) (t : ℝ) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine n t (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine n t z := rfl

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.three_right_convex_position (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle)
    (K N : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a b d : ℍ)
    (hvb : T.c=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc b))
    (hvd : T.b=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc d))
    (ha : K.OrthogonalAt N a)
    (hb : K.OrthogonalAt T.sideLineB.toHalfPlane b)
    (hd : N.OrthogonalAt T.sideLineC.toHalfPlane d)
    (hab : a≠b) (had : a≠d) :
    (0<(T.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a))).1 ∧
      0<(T.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a))).2) ∧
      1<(T.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a))).1+
        (T.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a))).2 := by
  let R:=T.sideLineB.toHalfPlane
  let M:=T.sideLineC.toHalfPlane
  let A:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a)
  let x:=(T.coordinate A).1
  let y:=(T.coordinate A).2
  let w:=1-x-y
  have haNK : N.OrthogonalAt K a:=⟨ha.2.1,ha.1,(real_inner_comm _ _).trans ha.2.2⟩
  have haM : a∉M.carrier:=N.perpendicular_other_point_not_mem M a d hd ha.2.1 had
  have haR : a∉R.carrier:=K.perpendicular_other_point_not_mem R a b hb ha.1 hab
  have hKB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine K.incenterNormal K.incenterOffset T.c=0 := by
    rw [hvb,closedDiscKleinAffine_finite_cayley]
    exact (K.incenter_affine_eq_zero_iff b).mpr hb.1
  have hND : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine N.incenterNormal N.incenterOffset T.b=0 := by
    rw [hvd,closedDiscKleinAffine_finite_cayley]
    exact (N.incenter_affine_eq_zero_iff d).mpr hd.1
  have hprodM:=K.transverse_affine_product_pos N M a d ha hd haM T.c hKB
  have hprodR:=N.transverse_affine_product_pos K R a b haNK hb haR T.b hND
  have hxy:=T.coordinates_pos_of_side_products A hprodR hprodM
  refine ⟨hxy,?_⟩
  have htM : M.normalTimeAt a≠0:=fun hh=>haM ((M.normalTimeAt_eq_zero_iff a).mp hh)
  have htR : R.normalTimeAt a≠0:=fun hh=>haR ((R.normalTimeAt_eq_zero_iff a).mp hh)
  have hMC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine M.incenterNormal M.incenterOffset T.a=0:=
    (T.sideLineC.closed_incenter_affine_zero_iff _).mpr T.a_mem_sideLineC
  have hMD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine M.incenterNormal M.incenterOffset T.b=0:=
    (T.sideLineC.closed_incenter_affine_zero_iff _).mpr T.b_mem_sideLineC
  have hRC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine R.incenterNormal R.incenterOffset T.a=0:=
    (T.sideLineB.closed_incenter_affine_zero_iff _).mpr T.a_mem_sideLineB
  have hRB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine R.incenterNormal R.incenterOffset T.c=0:=
    (T.sideLineB.closed_incenter_affine_zero_iff _).mpr T.c_mem_sideLineB
  have hMB:=K.restAffine_on_transverse N M a d ha hd T.c hKB
  have hRD:=N.restAffine_on_transverse K R a b haNK hb T.b hND
  have hrec:=T.restSpatial_reconstruction a A
  have hdotM:=congrArg (fun v : ℂ=>inner ℝ (M.normalSpatialAt a) v) hrec
  have hdotR:=congrArg (fun v : ℂ=>inner ℝ (R.normalSpatialAt a) v) hrec
  change inner ℝ (M.normalSpatialAt a) (restSpatial a
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a)))=
    inner ℝ (M.normalSpatialAt a) (w • restSpatial a T.a+x • restSpatial a T.b+y • restSpatial a T.c) at hdotM
  change inner ℝ (R.normalSpatialAt a) (restSpatial a
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a)))=
    inner ℝ (R.normalSpatialAt a) (w • restSpatial a T.a+x • restSpatial a T.b+y • restSpatial a T.c) at hdotR
  rw [restSpatial_center,inner_zero_right] at hdotM hdotR
  simp only [inner_add_right,inner_smul_right] at hdotM hdotR
  rw [M.restSpatial_dual a T.a,M.restSpatial_dual a T.b,M.restSpatial_dual a T.c,hMC,hMD,hMB] at hdotM
  rw [R.restSpatial_dual a T.a,R.restSpatial_dual a T.b,R.restSpatial_dual a T.c,hRC,hRB,hRD] at hdotR
  have heM : w*restTime a T.a+x*restTime a T.b=0 := by
    apply (mul_eq_zero.mp (show M.normalTimeAt a*(w*restTime a T.a+x*restTime a T.b)=0 from by
      linear_combination -hdotM)).resolve_left htM
  have heR : w*restTime a T.a+y*restTime a T.c=0 := by
    apply (mul_eq_zero.mp (show R.normalTimeAt a*(w*restTime a T.a+y*restTime a T.c)=0 from by
      linear_combination -hdotR)).resolve_left htR
  have htime:=T.restTime_reconstruction a A
  change restTime a (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a))=
    w*restTime a T.a+x*restTime a T.b+y*restTime a T.c at htime
  rw [restTime_center] at htime
  have hw : w*restTime a T.a<0 := by
    have hp : 0<1/_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a:=one_div_pos.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_pos a)
    linarith only [htime,heM,heR,hp]
  have hwneg:=neg_of_mul_neg_left hw (restTime_pos a T.a).le
  change 1<x+y
  dsimp [w] at hwneg
  linarith only [hwneg]


def DiscPolygon.anglePositiveVertex {n : ℕ} (P : DiscPolygon n) (i : Fin n) (hi : 0<P.angle i) : 𝔻 :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (P.vertices i) (P.vertex_finite_of_angle_pos i
    hi)

theorem DiscPolygon.anglePositiveVertex_spec {n : ℕ} (P : DiscPolygon n) (i : Fin n) (hi : 0<P.angle i) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.anglePositiveVertex i
      hi)=P.vertices i := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ _

theorem DiscPolygon.lambert_angle_right (P : DiscPolygon 4) (hL : P.IsLambert) (i : Fin 4) (hi : i≠0) :
    P.angle i=Real.pi/2 := by
  fin_cases i
  · exact (hi rfl).elim
  · exact hL.1
  · exact hL.2.1
  · exact hL.2.2


theorem DiscPolygon.lambert_angle_pos (P : DiscPolygon 4) (hL : P.IsLambert) (i : Fin 4) (hi : i≠0) :
    0<P.angle i := by
  rw [P.lambert_angle_right hL i hi]
  positivity


def DiscPolygon.lambertFiniteVertex (P : DiscPolygon 4) (hL : P.IsLambert) (i : Fin 4) (hi : i≠0) : 𝔻 :=
  P.anglePositiveVertex i (P.lambert_angle_pos hL i hi)

theorem DiscPolygon.lambertFiniteVertex_spec (P : DiscPolygon 4) (hL : P.IsLambert) (i : Fin 4) (hi : i≠0) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.lambertFiniteVertex hL i hi)=P.vertices i :=
  P.anglePositiveVertex_spec i _

theorem DiscPolygon.lambert_orthogonal (P : DiscPolygon 4) (hL : P.IsLambert) (i : Fin 4) (hi : i≠0) :
    (P.geodesicSide ((finRotate 4).symm i)).OrthogonalAt (P.geodesicSide i) (P.lambertFiniteVertex hL i hi) :=
  P.adjacent_sides_orthogonal_of_angle_right i _ (P.lambertFiniteVertex_spec hL i hi).symm
    (P.lambert_angle_right hL i hi)

theorem DiscPolygon.lambert_opposite_supports_ne (P : DiscPolygon 4) (hL : P.IsLambert) :
    P.geodesicSide 0≠P.geodesicSide 3 := by
  let a:=P.lambertFiniteVertex hL 2 (by decide)
  let b:=P.lambertFiniteVertex hL 1 (by decide)
  let d:=P.lambertFiniteVertex hL 3 (by decide)
  have ha : (P.geodesicSide 1).OrthogonalAt (P.geodesicSide 2) a:=P.lambert_orthogonal hL 2 (by decide)
  have hb' : (P.geodesicSide 0).OrthogonalAt (P.geodesicSide 1) b:=P.lambert_orthogonal hL 1 (by decide)
  have hb : (P.geodesicSide 1).OrthogonalAt (P.geodesicSide 0) b:=
    ⟨hb'.2.1,hb'.1,(real_inner_comm _ _).trans hb'.2.2⟩
  have hd : (P.geodesicSide 2).OrthogonalAt (P.geodesicSide 3) d:=P.lambert_orthogonal hL 3 (by decide)
  have he:=(P.geodesicSide 1).toHalfPlane.lambert_normal_pairing
    (P.geodesicSide 2).toHalfPlane (P.geodesicSide 0).toHalfPlane (P.geodesicSide 3).toHalfPlane
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane d)
    (((P.geodesicSide 1).orthogonalAt_iff_halfPlane _ a).mp ha)
    (((P.geodesicSide 1).orthogonalAt_iff_halfPlane _ b).mp hb)
    (((P.geodesicSide 2).orthogonalAt_iff_halfPlane _ d).mp hd)
  intro heq
  rw [heq] at he
  have hu:=(P.geodesicSide 3).toHalfPlane.incenterNormal_lorentz_unit
  change ‖_‖^2-_ ^2=1 at hu
  change inner ℝ _ _-_ * _= -(_ * _) at he
  rw [real_inner_self_eq_norm_sq] at he
  nlinarith [sq_nonneg ((P.geodesicSide 3).toHalfPlane.normalTimeAt
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane a))]

def DiscPolygon.lambertCorner (P : DiscPolygon 4) (hL :
  P.IsLambert) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle where
  a:=P.vertices 0
  b:=P.vertices 3
  c:=P.vertices 1
  noncollinear:=by
    rintro ⟨J,hC,hD,hB⟩
    have hJ3 : J=P.geodesicSide 3:=J.eq_of_two_closed_points _
      (P.vertices_injective.ne (by decide : (3:Fin 4)≠0)) hD hC
      (P.geodesicSide_endpoints 3).1 (P.geodesicSide_endpoints 3).2
    have hJ0 : J=P.geodesicSide 0:=J.eq_of_two_closed_points _
      (P.vertices_injective.ne (by decide : (0:Fin 4)≠1)) hC hB
      (P.geodesicSide_endpoints 0).1 (P.geodesicSide_endpoints 0).2
    exact P.lambert_opposite_supports_ne hL (hJ0.symm.trans hJ3)

theorem DiscPolygon.lambertCorner_sideB (P : DiscPolygon 4) (hL : P.IsLambert) :
    (P.lambertCorner hL).sideLineB=P.geodesicSide 0 :=
  (P.lambertCorner hL).sideLineB.eq_of_two_closed_points _
    (P.vertices_injective.ne (by decide : (0:Fin 4)≠1))
    (P.lambertCorner hL).a_mem_sideLineB (P.lambertCorner hL).c_mem_sideLineB
    (P.geodesicSide_endpoints 0).1 (P.geodesicSide_endpoints 0).2

theorem DiscPolygon.lambertCorner_sideC (P : DiscPolygon 4) (hL : P.IsLambert) :
    (P.lambertCorner hL).sideLineC=P.geodesicSide 3 :=
  (P.lambertCorner hL).sideLineC.eq_of_two_closed_points _
    (P.vertices_injective.ne (by decide : (3:Fin 4)≠0))
    (P.lambertCorner hL).b_mem_sideLineC (P.lambertCorner hL).a_mem_sideLineC
    (P.geodesicSide_endpoints 3).1 (P.geodesicSide_endpoints 3).2

theorem DiscPolygon.lambert_vertex_position (P : DiscPolygon 4) (hL : P.IsLambert) :
    (0<((P.lambertCorner hL).discCoordinate (P.lambertFiniteVertex hL 2 (by decide))).1 ∧
      0<((P.lambertCorner hL).discCoordinate (P.lambertFiniteVertex hL 2 (by decide))).2) ∧
    1<((P.lambertCorner hL).discCoordinate (P.lambertFiniteVertex hL 2 (by decide))).1+
      ((P.lambertCorner hL).discCoordinate (P.lambertFiniteVertex hL 2 (by decide))).2 := by
  let a:=P.lambertFiniteVertex hL 2 (by decide)
  let b:=P.lambertFiniteVertex hL 1 (by decide)
  let d:=P.lambertFiniteVertex hL 3 (by decide)
  have hvb : (P.lambertCorner hL).c=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane b)):=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
    exact (P.lambertFiniteVertex_spec hL 1 (by decide)).symm
  have hvd : (P.lambertCorner hL).b=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane d)):=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
    exact (P.lambertFiniteVertex_spec hL 3 (by decide)).symm
  have ha:=((P.geodesicSide 1).orthogonalAt_iff_halfPlane _ a).mp (P.lambert_orthogonal hL 2 (by decide))
  have hb' := P.lambert_orthogonal hL 1 (by decide)
  have hb := ((P.geodesicSide 1).orthogonalAt_iff_halfPlane (P.geodesicSide 0) b).mp
    ⟨hb'.2.1,hb'.1,(real_inner_comm _ _).trans hb'.2.2⟩
  have hd := ((P.geodesicSide 2).orthogonalAt_iff_halfPlane _ d).mp (P.lambert_orthogonal hL 3 (by decide))
  have hab : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane a≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane b:=by
    intro he
    have he' := congrArg (fun z=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) he
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane] at he'
    rw [P.lambertFiniteVertex_spec hL 2 (by decide),P.lambertFiniteVertex_spec hL 1 (by decide)] at he'
    exact (by decide : (2:Fin 4)≠1) (P.vertices_injective he')
  have had : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane a≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane d:=by
    intro he
    have he' := congrArg (fun z=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) he
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane] at he'
    rw [P.lambertFiniteVertex_spec hL 2 (by decide),P.lambertFiniteVertex_spec hL 3 (by decide)] at he'
    exact (by decide : (2:Fin 4)≠3) (P.vertices_injective he')
  rw [←P.lambertCorner_sideB hL] at hb
  rw [←P.lambertCorner_sideC hL] at hd
  have hp:=(P.lambertCorner hL).three_right_convex_position
    (P.geodesicSide 1).toHalfPlane (P.geodesicSide 2).toHalfPlane
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane d) hvb hvd ha hb hd hab had
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.discCoordinate] using hp

def DiscPolygon.asLambertQuadrilateral (P : DiscPolygon 4) (hL : P.IsLambert) : LambertQuadrilateral where
  corner:=P.lambertCorner hL
  a:=P.lambertFiniteVertex hL 2 (by decide)
  b:=P.lambertFiniteVertex hL 1 (by decide)
  d:=P.lambertFiniteVertex hL 3 (by decide)
  vertex_d:=(P.lambertFiniteVertex_spec hL 3 (by decide)).symm
  vertex_b:=(P.lambertFiniteVertex_spec hL 1 (by decide)).symm
  bottom:=P.geodesicSide 1
  left:=P.geodesicSide 2
  angle_a:=P.lambert_orthogonal hL 2 (by decide)
  angle_b:=by
    rw [P.lambertCorner_sideB]
    have h:=P.lambert_orthogonal hL 1 (by decide)
    exact ⟨h.2.1,h.1,(real_inner_comm _ _).trans h.2.2⟩
  angle_d:=by
    rw [P.lambertCorner_sideC]
    exact P.lambert_orthogonal hL 3 (by decide)
  convex_corner:=(P.lambert_vertex_position hL).1
  opposite_chord:=(P.lambert_vertex_position hL).2

def CyclicDiscPolygonSupportData.reverseFour (S : CyclicDiscPolygonSupportData 4) :
    CyclicDiscPolygonSupportData 4 where
  three_le:=S.three_le
  vertices i:=S.vertices (-i)
  vertices_injective:=S.vertices_injective.comp neg_injective
  normals i:=S.normals (-i-1)
  normal_norm i:=S.normal_norm _
  offsets i:=S.offsets (-i-1)
  incident i:=by
    have h:=S.incident (-i-1)
    have h1 : finRotate 4 (-i-1)= -i:=by rw [finRotate_apply];abel
    have h2 : -(finRotate 4 i)= -i-1:=by rw [finRotate_apply];abel
    rw [h1] at h
    rw [h2]
    exact ⟨h.2,h.1⟩
  nonincident i j hji hjn:=by
    apply S.nonincident (-i-1) (-j)
    · intro he
      have hj : j=finRotate 4 i:=by
        rw [finRotate_apply]
        have h:=congrArg Neg.neg he
        simpa only [neg_neg,neg_sub,neg_neg,sub_neg_eq_add,add_comm] using h
      exact hjn hj
    · intro he
      rw [finRotate_apply] at he
      have he' : -j= -i:=by simpa only [sub_add_cancel] using he
      exact hji (neg_injective he')

def CenteredDiscPolygonSupportData.toCyclicData {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    CyclicDiscPolygonSupportData n where
  three_le:=S.three_le
  vertices:=S.vertices
  vertices_injective:=S.vertices_injective
  normals:=S.normals
  normal_norm:=S.normal_norm
  offsets:=S.offsets
  incident:=S.incident
  nonincident:=S.nonincident

def DiscPolygon.lambertReversedSupportData (P : DiscPolygon 4) (hL : P.IsLambert) :
    CyclicDiscPolygonSupportData 4 :=
  (P.asLambertQuadrilateral hL).polygonSupportData.toCyclicData.reverseFour

theorem DiscPolygon.lambertReversedSupportData_vertices (P : DiscPolygon 4) (hL : P.IsLambert) :
    (P.lambertReversedSupportData hL).vertices=P.vertices := by
  funext i
  fin_cases i <;>
    norm_num [DiscPolygon.lambertReversedSupportData,CyclicDiscPolygonSupportData.reverseFour,
      CenteredDiscPolygonSupportData.toCyclicData,LambertQuadrilateral.polygonSupportData,
      LambertQuadrilateral.polygonVertices,DiscPolygon.asLambertQuadrilateral,DiscPolygon.lambertCorner]
  exact P.lambertFiniteVertex_spec hL 2 (by decide)

theorem DiscPolygon.lambertReversedSupportData_toDiscPolygon (P : DiscPolygon 4) (hL : P.IsLambert) :
    (P.lambertReversedSupportData hL).toDiscPolygon=P :=
  DiscPolygon.eq_of_vertices_eq _ P (P.lambertReversedSupportData_vertices hL)

theorem DiscPolygon.lambert_isConvex (P : DiscPolygon 4) (hL : P.IsLambert) : P.IsConvex := by
  rw [←P.lambertReversedSupportData_toDiscPolygon hL]
  exact (P.lambertReversedSupportData hL).toDiscPolygon_isConvex

theorem DiscPolygon.lambert_angle_eq (P : DiscPolygon 4) (hL : P.IsLambert) :
    P.angle 0=(P.asLambertQuadrilateral hL).angle := by
  have he:=(P.lambertReversedSupportData hL).toDiscPolygon_angle 0
  rw [P.lambertReversedSupportData_toDiscPolygon hL] at he
  refine he.trans ?_
  change ((P.lambertReversedSupportData hL).toCenteredData.cornerTriangle 0).alpha=
    (P.asLambertQuadrilateral hL).corner.alpha
  apply (P.asLambertQuadrilateral hL).corner.alpha_eq_of_adjacent_pair
  · rfl
  · rfl

theorem DiscPolygon.lambert_fourth_angle_range (P : DiscPolygon 4) (hL : P.IsLambert) :
    P.angle 0∈Ico (0:ℝ) (Real.pi/2) := by
  rw [P.lambert_angle_eq hL]
  exact (P.asLambertQuadrilateral hL).angle_mem_Ico

theorem DiscPolygon.lambert_sideA₁_eq (P : DiscPolygon 4) (hL : P.IsLambert) :
    (P.asLambertQuadrilateral hL).sideA₁=(P.sideLength 1).toReal := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (P.lambertFiniteVertex hL 2 (by decide)) (P.lambertFiniteVertex hL 1 (by decide))=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength (P.vertices 1) (P.vertices 2)).toReal
  rw [←P.lambertFiniteVertex_spec hL 1 (by decide),←P.lambertFiniteVertex_spec hL 2 (by decide),
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength_finite,ENNReal.toReal_ofReal (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane];exact dist_nonneg)]
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane,dist_comm]

theorem DiscPolygon.lambert_sideA₂_eq (P : DiscPolygon 4) (hL : P.IsLambert) :
    (P.asLambertQuadrilateral hL).sideA₂=(P.sideLength 2).toReal := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (P.lambertFiniteVertex hL 2 (by decide)) (P.lambertFiniteVertex hL 3 (by decide))=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength (P.vertices 2) (P.vertices 3)).toReal
  rw [←P.lambertFiniteVertex_spec hL 2 (by decide),←P.lambertFiniteVertex_spec hL 3 (by decide),
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength_finite,ENNReal.toReal_ofReal (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane];exact dist_nonneg)]

theorem DiscPolygon.lambert_adjacent_side_eq (P : DiscPolygon 4) (hL : P.IsLambert)
    (z : 𝔻) (hz : P.vertices 0=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (P.asLambertQuadrilateral hL).d z=(P.sideLength 3).toReal := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (P.lambertFiniteVertex hL 3 (by decide)) z=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength (P.vertices 3) (P.vertices 0)).toReal
  rw [hz,←P.lambertFiniteVertex_spec hL 3 (by decide),_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength_finite,
    ENNReal.toReal_ofReal (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane];exact dist_nonneg)]

/-- For every actual Lambert Jordan quadrilateral, including an ideal fourth vertex. -/
theorem DiscPolygon.lambert_sinh_adjacent_mul_eq_cos_angle (P : DiscPolygon 4) (hL : P.IsLambert) :
    Real.sinh (P.sideLength 1).toReal*Real.sinh (P.sideLength 2).toReal=Real.cos (P.angle 0) := by
  rw [P.lambert_angle_eq hL,←P.lambert_sideA₁_eq hL,←P.lambert_sideA₂_eq hL]
  exact (P.asLambertQuadrilateral hL).sinh_adjacent_mul_eq_cos_angle

/-- finiteness is explicit because the displayed adjacent side is a real length. -/
theorem DiscPolygon.lambert_cosh_side_eq_cosh_opposite_mul_sin (P : DiscPolygon 4) (hL : P.IsLambert)
    (z : 𝔻) (hz : P.vertices 0=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    Real.cosh (P.sideLength 1).toReal=Real.cosh (P.sideLength 3).toReal*Real.sin (P.angle 0) := by
  rw [P.lambert_angle_eq hL,←P.lambert_sideA₁_eq hL,←P.lambert_adjacent_side_eq hL z hz]
  exact (P.asLambertQuadrilateral hL).cosh_side_eq_cosh_opposite_mul_sin z hz

end
end LowDimensionalTopology.Geometry.Polygon
