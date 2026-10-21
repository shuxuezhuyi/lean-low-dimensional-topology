module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.GeodesicInversiveProducts
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
noncomputable section











theorem complex_inner_zero_of_orthogonal_complements (K N L M : ℂ)
    (hK : ‖K‖ ^ 2 = 1) (hN : ‖N‖ ^ 2 = 1) (hKN : inner ℝ K N = 0)
    (hLK : inner ℝ L K = 0) (hMN : inner ℝ M N = 0) : inner ℝ L M = 0 := by
  have hg := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_gram_three K N L
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
    hK,hN,hKN,hLK] at hg
  have hd : ‖L - (inner ℝ N L) • N‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hN,inner_smul_right,
      real_inner_comm N L]
    nlinarith only [hg]
  have hL : L = (inner ℝ N L) • N := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hd))
  rw [hL,real_inner_smul_left,real_inner_comm M N,hMN,mul_zero]

/-- Three actual right-angle incidences force the opposite side pairing. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.lambert_normal_pairing (K N L M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a b d : ℍ)
    (ha : K.OrthogonalAt N a) (hb : K.OrthogonalAt L b) (hd : N.OrthogonalAt M d) :
    L.normalPairing M = -(L.normalTimeAt a * M.normalTimeAt a) := by
  have hKa := (K.normalTimeAt_eq_zero_iff a).mpr ha.1
  have hNa := (N.normalTimeAt_eq_zero_iff a).mpr ha.2.1
  have hK := K.normalSpatialAt_norm_sq a
  have hN := N.normalSpatialAt_norm_sq a
  rw [hKa,zero_pow (by omega : 2 ≠ 0),add_zero] at hK
  rw [hNa,zero_pow (by omega : 2 ≠ 0),add_zero] at hN
  have hKN := K.normalSpatialAt_inner N a
  have hLK := L.normalSpatialAt_inner K a
  have hMN := M.normalSpatialAt_inner N a
  have hKL := K.normalPairing_orthogonal L b hb
  have hNM := N.normalPairing_orthogonal M d hd
  have hKL' : L.normalPairing K = 0 := by
    change inner ℝ K.incenterNormal L.incenterNormal - K.incenterOffset * L.incenterOffset = 0 at hKL
    change inner ℝ L.incenterNormal K.incenterNormal - L.incenterOffset * K.incenterOffset = 0
    rw [real_inner_comm K.incenterNormal L.incenterNormal]
    nlinarith only [hKL]
  have hNM' : M.normalPairing N = 0 := by
    change inner ℝ N.incenterNormal M.incenterNormal - N.incenterOffset * M.incenterOffset = 0 at hNM
    change inner ℝ M.incenterNormal N.incenterNormal - M.incenterOffset * N.incenterOffset = 0
    rw [real_inner_comm N.incenterNormal M.incenterNormal]
    nlinarith only [hNM]
  rw [K.normalPairing_orthogonal N a ha,hKa,zero_mul,add_zero] at hKN
  rw [hKL',hKa,mul_zero,add_zero] at hLK
  rw [hNM',hNa,mul_zero,add_zero] at hMN
  have he := complex_inner_zero_of_orthogonal_complements _ _ _ _ hK hN hKN hLK hMN
  rw [L.normalSpatialAt_inner M a] at he
  linarith only [he]

/-- The first Lambert identity is intrinsic and includes an ideal fourth vertex. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.lambert_sinh_product (K N L M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a b d : ℍ)
    (ha : K.OrthogonalAt N a) (hb : K.OrthogonalAt L b) (hd : N.OrthogonalAt M d) :
    Real.sinh (L.pointDist a) * Real.sinh (M.pointDist a) =
      _root_.LowDimensionalTopology.Geometry.Inversive.inversiveProduct L.extendedCircle.realModel M.extendedCircle.realModel := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlane_inversiveProduct_eq_normal_product]
  change _ = |L.normalPairing M|
  rw [K.lambert_normal_pairing N L M a b d ha hb hd,abs_neg,abs_mul,
    L.normalTimeAt_abs,M.normalTimeAt_abs]




/-- A Gram determinant gives the diagonal length of every actual Lambert configuration. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.lambert_diagonal_cosh_sq (K N L M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a b d w : ℍ)
    (ha : K.OrthogonalAt N a) (hb : K.OrthogonalAt L b) (hd : N.OrthogonalAt M d)
    (hwL : w ∈ L.carrier) (hwM : w ∈ M.carrier) :
    Real.cosh (dist a w) ^ 2 * (1 - L.normalPairing M ^ 2) =
      Real.cosh (L.pointDist a) ^ 2 * Real.cosh (M.pointDist a) ^ 2 := by
  let X := _root_.LowDimensionalTopology.Geometry.Hyperbolic.sideNormalBoost (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight a)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial
      w) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight w)
  have hg := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_gram_three (L.normalSpatialAt
    a) (M.normalSpatialAt a) X
  have hLM : inner ℝ (L.normalSpatialAt a) (M.normalSpatialAt a) = 0 := by
    rw [L.normalSpatialAt_inner M a,K.lambert_normal_pairing N L M a b d ha hb hd]
    ring
  have hXL : inner ℝ X (L.normalSpatialAt a) = L.normalTimeAt a * Real.cosh (dist a w) := by
    rw [real_inner_comm (L.normalSpatialAt a) X]
    exact L.normalSpatialAt_inner_boost_point a w hwL
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
    L.normalSpatialAt_norm_sq,M.normalSpatialAt_norm_sq,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePoint_boost_norm,
    hLM,M.normalSpatialAt_inner_boost_point a w hwM,hXL] at hg
  have hL := Real.cosh_sq_sub_sinh_sq (L.pointDist a)
  have hM := Real.cosh_sq_sub_sinh_sq (M.pointDist a)
  rw [← L.normalTimeAt_abs] at hL
  rw [← M.normalTimeAt_abs] at hM
  rw [sq_abs] at hL hM
  rw [K.lambert_normal_pairing N L M a b d ha hb hd]
  nlinarith only [hg,hL,hM]

/-- The actual nearest feet provide the corresponding two finite side lengths. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.lambert_sinh_lengths (K N L M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a b d : ℍ)
    (ha : K.OrthogonalAt N a) (hb : K.OrthogonalAt L b) (hd : N.OrthogonalAt M d) :
    Real.sinh (dist a b) * Real.sinh (dist a d) =
      _root_.LowDimensionalTopology.Geometry.Inversive.inversiveProduct L.extendedCircle.realModel M.extendedCircle.realModel := by
  have hb' : L.OrthogonalAt K b := ⟨hb.2.1,hb.1,by rw [real_inner_comm]; exact hb.2.2⟩
  have hd' : M.OrthogonalAt N d := ⟨hd.2.1,hd.1,by rw [real_inner_comm]; exact hd.2.2⟩
  rw [← L.pointDist_eq_dist_of_perpendicular K b a hb' ha.1,
    ← M.pointDist_eq_dist_of_perpendicular N d a hd' ha.2.1]
  exact K.lambert_sinh_product N L M a b d ha hb hd

/-- The second intrinsic Lambert identity, with an actual finite fourth vertex. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.lambert_cosh_acute_angle (K N L M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a b d w : ℍ)
    (ha : K.OrthogonalAt N a) (hb : K.OrthogonalAt L b) (hd : N.OrthogonalAt M d)
    (hwL : w ∈ L.carrier) (hwM : w ∈ M.carrier) :
    Real.cosh (dist a b) = Real.cosh (dist d w) * Real.sin (L.acuteAngle M w) := by
  have hb' : L.OrthogonalAt K b := ⟨hb.2.1,hb.1,by rw [real_inner_comm]; exact hb.2.2⟩
  have hd' : M.OrthogonalAt N d := ⟨hd.2.1,hd.1,by rw [real_inner_comm]; exact hd.2.2⟩
  have hLa := L.pointDist_eq_dist_of_perpendicular K b a hb' ha.1
  have hMa := M.pointDist_eq_dist_of_perpendicular N d a hd' ha.2.1
  have hright := M.orthogonal_cosh_dist N d a w hd' ha.2.1 hwM
  have hdiag := K.lambert_diagonal_cosh_sq N L M a b d w ha hb hd hwL hwM
  rw [hLa,hMa,hright] at hdiag
  have hcos := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlane_inversiveProduct_eq_cos_acuteAngle L M w hwL hwM
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlane_inversiveProduct_eq_normal_product] at hcos
  change |L.normalPairing M| = Real.cos (L.acuteAngle M w) at hcos
  have hcos2 : L.normalPairing M ^ 2 = Real.cos (L.acuteAngle M w) ^ 2 := by
    rw [← hcos,sq_abs]
  rw [hcos2] at hdiag
  have htrig := Real.sin_sq_add_cos_sq (L.acuteAngle M w)
  have hs : 1 - Real.cos (L.acuteAngle M w) ^ 2 = Real.sin (L.acuteAngle M w) ^ 2 := by
    linarith only [htrig]
  rw [hs] at hdiag
  have he : (Real.cosh (dist d w) * Real.sin (L.acuteAngle M w)) ^ 2 = Real.cosh (dist a b) ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (Real.cosh_pos (dist a d)).ne')
    nlinarith only [hdiag]
  have hang := L.acuteAngle_mem_Icc M w
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hang.1 (by linarith [hang.2,Real.pi_pos])
  exact (sq_eq_sq₀ (Real.cosh_pos _).le (mul_nonneg (Real.cosh_pos _).le hsin)).mp he.symm
/-- The genuine finite or ideal corner formula holds throughout its positive Klein cone. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.cosine_alpha_side_normals_of_positive_coordinates
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (q : 𝔻)
    (hq : 0 < (T.discCoordinate q).1 ∧ 0 < (T.discCoordinate q).2) :
    Real.cos T.alpha *
        |_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q)| *
        |_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q)| =
      -((inner ℝ T.sideLineB.incenterNormal T.sideLineC.incenterNormal -
        T.sideLineB.incenterOffset * T.sideLineC.incenterOffset) *
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q) *
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q)) := by
  let FB := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset
  let FC := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset
  have hBa : FB T.a = 0 := (T.sideLineB.closed_incenter_affine_zero_iff _).mpr T.a_mem_sideLineB
  have hBc : FB T.c = 0 := (T.sideLineB.closed_incenter_affine_zero_iff _).mpr T.c_mem_sideLineB
  have hCa : FC T.a = 0 := (T.sideLineC.closed_incenter_affine_zero_iff _).mpr T.a_mem_sideLineC
  have hCb : FC T.b = 0 := (T.sideLineC.closed_incenter_affine_zero_iff _).mpr T.b_mem_sideLineC
  have hBp (p : 𝕔𝔻) : FB p = (T.coordinate p).1 * FB T.b := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine _ _ p = _
    rw [T.kleinAffine_reconstruction]
    change (1 - (T.coordinate p).1 - (T.coordinate p).2) * FB T.a +
      (T.coordinate p).1 * FB T.b + (T.coordinate p).2 * FB T.c = _
    rw [hBa,hBc]
    ring
  have hCp (p : 𝕔𝔻) : FC p = (T.coordinate p).2 * FC T.c := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine _ _ p = _
    rw [T.kleinAffine_reconstruction]
    change (1 - (T.coordinate p).1 - (T.coordinate p).2) * FC T.a +
      (T.coordinate p).1 * FC T.b + (T.coordinate p).2 * FC T.c = _
    rw [hCa,hCb]
    ring
  have hp := T.incenter_interior_coordinates T.incenter_mem_interior
  have he := T.cosine_alpha_side_normals T.incenter T.incenter_mem_interior
  change Real.cos T.alpha * |FB (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    T.incenter)| * |FC (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel T.incenter)| =
    -((inner ℝ T.sideLineB.incenterNormal T.sideLineC.incenterNormal -
      T.sideLineB.incenterOffset * T.sideLineC.incenterOffset) *
      FB (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        T.incenter) * FC (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel T.incenter)) at he
  rw [hBp,hCp,abs_mul,abs_mul] at he
  change Real.cos T.alpha * (|(T.discCoordinate T.incenter).1| * |FB T.b|) *
    (|(T.discCoordinate T.incenter).2| * |FC T.c|) =
      -((inner ℝ T.sideLineB.incenterNormal T.sideLineC.incenterNormal -
        T.sideLineB.incenterOffset * T.sideLineC.incenterOffset) *
        ((T.discCoordinate T.incenter).1 * FB T.b) *
        ((T.discCoordinate T.incenter).2 * FC T.c)) at he
  rw [abs_of_pos hp.1,abs_of_pos hp.2.1] at he
  have hbase : Real.cos T.alpha * |FB T.b| * |FC T.c| =
      -((inner ℝ T.sideLineB.incenterNormal T.sideLineC.incenterNormal -
        T.sideLineB.incenterOffset * T.sideLineC.incenterOffset) * FB T.b * FC T.c) := by
    apply mul_left_cancel₀ (mul_ne_zero hp.1.ne' hp.2.1.ne')
    nlinarith only [he]
  change Real.cos T.alpha * |FB (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    q)| * |FC (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q)| =
    -((inner ℝ T.sideLineB.incenterNormal T.sideLineC.incenterNormal -
      T.sideLineB.incenterOffset * T.sideLineC.incenterOffset) * FB (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q) * FC (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q))
  rw [hBp,hCp,abs_mul,abs_mul]
  change Real.cos T.alpha * (|(T.discCoordinate q).1| * |FB T.b|) *
    (|(T.discCoordinate q).2| * |FC T.c|) =
    -((inner ℝ T.sideLineB.incenterNormal T.sideLineC.incenterNormal -
      T.sideLineB.incenterOffset * T.sideLineC.incenterOffset) *
      ((T.discCoordinate q).1 * FB T.b) * ((T.discCoordinate q).2 * FC T.c))
  rw [abs_of_pos hq.1,abs_of_pos hq.2]
  nlinarith only [congrArg (fun x : ℝ => ((T.discCoordinate q).1 * (T.discCoordinate q).2) * x) hbase]

/-- Neither adjacent side contains a point in the genuine corner cone. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.positive_coordinates_not_adjacent_sides
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (q : 𝔻)
    (hq : 0 < (T.discCoordinate q).1 ∧ 0 < (T.discCoordinate q).2) :
    q ∉ T.sideLineB.carrier ∧ q ∉ T.sideLineC.carrier := by
  constructor
  · intro h
    have he := (T.sideLineB_iff_coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q)).mp
      ((T.sideLineB.closedCarrier_mem_interior_iff q).mpr h)
    change (T.discCoordinate q).1 = 0 at he
    linarith only [he,hq.1]
  · intro h
    have he := (T.sideLineC_iff_coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q)).mp
      ((T.sideLineC.closedCarrier_mem_interior_iff q).mpr h)
    change (T.discCoordinate q).2 = 0 at he
    linarith only [he,hq.2]

/-- A convex Lambert quadrilateral with its actual three finite right-angle vertices.
The fourth vertex may be ideal; the positive Klein cone and opposite chord select the interior. -/
structure LambertQuadrilateral where
  corner : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle
  a : 𝔻
  b : 𝔻
  d : 𝔻
  vertex_d : corner.b = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel d
  vertex_b : corner.c = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel b
  bottom : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine
  left : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine
  angle_a : bottom.OrthogonalAt left a
  angle_b : bottom.OrthogonalAt corner.sideLineB b
  angle_d : left.OrthogonalAt corner.sideLineC d
  convex_corner : 0 < (corner.discCoordinate a).1 ∧ 0 < (corner.discCoordinate a).2
  opposite_chord : 1 < (corner.discCoordinate a).1 + (corner.discCoordinate a).2

def LambertQuadrilateral.angle (Q : LambertQuadrilateral) : ℝ := Q.corner.alpha

def LambertQuadrilateral.sideA₁ (Q :
  LambertQuadrilateral) : ℝ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist Q.a Q.b

def LambertQuadrilateral.sideA₂ (Q :
  LambertQuadrilateral) : ℝ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist Q.a Q.d

/-- The true fourth corner, rather than the smaller unoriented line angle, enters this identity. -/
theorem LambertQuadrilateral.sinh_side_distances (Q : LambertQuadrilateral) :
    Real.sinh (Q.corner.sideLineB.pointDist Q.a) *
      Real.sinh (Q.corner.sideLineC.pointDist Q.a) = Real.cos Q.angle := by
  let L := Q.corner.sideLineB
  let M := Q.corner.sideLineC
  let F := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine L.incenterNormal L.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.a)
  let G := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine M.incenterNormal M.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.a)
  let h := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.a)
  have hF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine L.toHalfPlane.incenterNormal L.toHalfPlane.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.a) = F := by
    simp only [F,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.incenterNormal,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.incenterOffset,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  have hG : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine M.toHalfPlane.incenterNormal M.toHalfPlane.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.a) = G := by
    simp only [G,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.incenterNormal,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.incenterOffset,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  have hpair := Q.bottom.toHalfPlane.lambert_normal_pairing Q.left.toHalfPlane L.toHalfPlane M.toHalfPlane
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      Q.a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      Q.b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.d)
    ((Q.bottom.orthogonalAt_iff_halfPlane Q.left Q.a).mp Q.angle_a)
    ((Q.bottom.orthogonalAt_iff_halfPlane L Q.b).mp Q.angle_b)
    ((Q.left.orthogonalAt_iff_halfPlane M Q.d).mp Q.angle_d)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalTimeAt_eq_affine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalTimeAt_eq_affine,hF,hG] at hpair
  change L.toHalfPlane.normalPairing M.toHalfPlane = -((-h * F) * (-h * G)) at hpair
  have he := Q.corner.cosine_alpha_side_normals_of_positive_coordinates Q.a Q.convex_corner
  change Real.cos Q.angle * |F| * |G| = -(L.toHalfPlane.normalPairing M.toHalfPlane * F * G) at he
  have hn := Q.corner.positive_coordinates_not_adjacent_sides Q.a Q.convex_corner
  have hFn : F ≠ 0 := by
    intro hf
    exact hn.1 ((L.closedCarrier_mem_interior_iff Q.a).mp ((L.closed_incenter_affine_zero_iff _).mp hf))
  have hGn : G ≠ 0 := by
    intro hg
    exact hn.2 ((M.closedCarrier_mem_interior_iff Q.a).mp ((M.closed_incenter_affine_zero_iff _).mp hg))
  have hcos : Real.cos Q.angle = h ^ 2 * |F| * |G| := by
    apply mul_right_cancel₀ (mul_ne_zero (abs_ne_zero.mpr hFn) (abs_ne_zero.mpr hGn))
    calc
      _ = -(L.toHalfPlane.normalPairing M.toHalfPlane * F * G) := by nlinarith only [he]
      _ = (h ^ 2 * |F| * |G|) * (|F| * |G|) := by
        rw [hpair]
        calc
          _ = h ^ 2 * (F ^ 2 * G ^ 2) := by ring
          _ = h ^ 2 * (|F| ^ 2 * |G| ^ 2) := by rw [sq_abs,sq_abs]
          _ = _ := by ring
  rw [L.sinh_pointDist_closed_incenter_affine,M.sinh_pointDist_closed_incenter_affine]
  change |F| * h * (|G| * h) = Real.cos Q.angle
  rw [hcos]
  ring

theorem LambertQuadrilateral.sideA₁_eq_pointDist (Q : LambertQuadrilateral) :
    Q.sideA₁ = Q.corner.sideLineB.pointDist Q.a := by
  have hb : Q.corner.sideLineB.OrthogonalAt Q.bottom Q.b :=
    ⟨Q.angle_b.2.1,Q.angle_b.1,by rw [real_inner_comm]; exact Q.angle_b.2.2⟩
  exact (Q.corner.sideLineB.pointDist_eq_dist_of_perpendicular Q.bottom Q.b Q.a hb Q.angle_a.1).symm

theorem LambertQuadrilateral.sideA₂_eq_pointDist (Q : LambertQuadrilateral) :
    Q.sideA₂ = Q.corner.sideLineC.pointDist Q.a := by
  have hd : Q.corner.sideLineC.OrthogonalAt Q.left Q.d :=
    ⟨Q.angle_d.2.1,Q.angle_d.1,by rw [real_inner_comm]; exact Q.angle_d.2.2⟩
  exact (Q.corner.sideLineC.pointDist_eq_dist_of_perpendicular Q.left Q.d Q.a hd Q.angle_a.2.1).symm

/-- For actual finite or ideal fourth vertices. -/
theorem LambertQuadrilateral.sinh_adjacent_mul_eq_cos_angle (Q : LambertQuadrilateral) :
    Real.sinh Q.sideA₁ * Real.sinh Q.sideA₂ = Real.cos Q.angle := by
  rw [Q.sideA₁_eq_pointDist,Q.sideA₂_eq_pointDist]
  exact Q.sinh_side_distances

theorem LambertQuadrilateral.a_ne_b (Q : LambertQuadrilateral) : Q.a ≠ Q.b := by
  intro he
  have hn := Q.corner.positive_coordinates_not_adjacent_sides Q.a Q.convex_corner
  exact hn.1 (he.symm ▸ Q.angle_b.2.1)

theorem LambertQuadrilateral.a_ne_d (Q : LambertQuadrilateral) : Q.a ≠ Q.d := by
  intro he
  have hn := Q.corner.positive_coordinates_not_adjacent_sides Q.a Q.convex_corner
  exact hn.2 (he.symm ▸ Q.angle_d.2.1)

theorem LambertQuadrilateral.angle_mem_Ico (Q : LambertQuadrilateral) :
    Q.angle ∈ Ico (0 : ℝ) (Real.pi / 2) := by
  have ha := Q.corner.alpha_mem_Ico
  change 0 ≤ Q.angle ∧ Q.angle < Real.pi at ha
  refine ⟨ha.1,?_⟩
  have hA₁ : 0 < Q.sideA₁ := by
    rw [LambertQuadrilateral.sideA₁,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]
    exact dist_pos.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective.ne Q.a_ne_b)
  have hA₂ : 0 < Q.sideA₂ := by
    rw [LambertQuadrilateral.sideA₂,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]
    exact dist_pos.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective.ne Q.a_ne_d)
  have hcos : 0 < Real.cos Q.angle := by
    rw [← Q.sinh_adjacent_mul_eq_cos_angle]
    exact mul_pos (Real.sinh_pos_iff.mpr hA₁) (Real.sinh_pos_iff.mpr hA₂)
  by_contra hn
  have he := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ Real.pi / 2)
    ha.2.le (le_of_not_gt hn)
  rw [Real.cos_pi_div_two] at he
  linarith only [he,hcos]

/-- At a finite fourth vertex the genuine corner agrees with the actual smaller line angle. -/
theorem LambertQuadrilateral.angle_eq_acuteAngle (Q : LambertQuadrilateral) (w : 𝔻)
    (hw : Q.corner.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w) :
    Q.angle = Q.corner.sideLineB.toHalfPlane.acuteAngle Q.corner.sideLineC.toHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) := by
  let L := Q.corner.sideLineB
  let M := Q.corner.sideLineC
  have hwL : w ∈ L.carrier := by
    apply (L.closedCarrier_mem_interior_iff w).mp
    rw [← hw]
    exact Q.corner.a_mem_sideLineB
  have hwM : w ∈ M.carrier := by
    apply (M.closedCarrier_mem_interior_iff w).mp
    rw [← hw]
    exact Q.corner.a_mem_sideLineC
  have hfirst := Q.sinh_side_distances
  rw [L.pointDist_eq_halfPlane,M.pointDist_eq_halfPlane] at hfirst
  have hinv := Q.bottom.toHalfPlane.lambert_sinh_product Q.left.toHalfPlane L.toHalfPlane M.toHalfPlane
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      Q.a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      Q.b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.d)
    ((Q.bottom.orthogonalAt_iff_halfPlane Q.left Q.a).mp Q.angle_a)
    ((Q.bottom.orthogonalAt_iff_halfPlane L Q.b).mp Q.angle_b)
    ((Q.left.orthogonalAt_iff_halfPlane M Q.d).mp Q.angle_d)
  have hcos := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlane_inversiveProduct_eq_cos_acuteAngle L.toHalfPlane M.toHalfPlane
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) ((L.mem_carrier w).mp hwL) ((M.mem_carrier
      w).mp hwM)
  have hangle := Q.angle_mem_Ico
  have hacute := L.toHalfPlane.acuteAngle_mem_Icc M.toHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w)
  exact Real.injOn_cos ⟨hangle.1,by linarith [hangle.2,Real.pi_pos]⟩
    ⟨hacute.1,by linarith [hacute.2,Real.pi_pos]⟩ (hfirst.symm.trans (hinv.trans hcos))

/-- uses a finite fourth vertex, so that its adjacent side is a real length. -/
theorem LambertQuadrilateral.cosh_side_eq_cosh_opposite_mul_sin (Q : LambertQuadrilateral) (w : 𝔻)
    (hw : Q.corner.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w) :
    Real.cosh Q.sideA₁ = Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist Q.d w) * Real.sin Q.angle := by
  let L := Q.corner.sideLineB
  let M := Q.corner.sideLineC
  have hwL : w ∈ L.carrier := by
    apply (L.closedCarrier_mem_interior_iff w).mp
    rw [← hw]
    exact Q.corner.a_mem_sideLineB
  have hwM : w ∈ M.carrier := by
    apply (M.closedCarrier_mem_interior_iff w).mp
    rw [← hw]
    exact Q.corner.a_mem_sideLineC
  have he := Q.bottom.toHalfPlane.lambert_cosh_acute_angle Q.left.toHalfPlane L.toHalfPlane M.toHalfPlane
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      Q.a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      Q.b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      Q.d) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w)
    ((Q.bottom.orthogonalAt_iff_halfPlane Q.left Q.a).mp Q.angle_a)
    ((Q.bottom.orthogonalAt_iff_halfPlane L Q.b).mp Q.angle_b)
    ((Q.left.orthogonalAt_iff_halfPlane M Q.d).mp Q.angle_d)
    ((L.mem_carrier w).mp hwL) ((M.mem_carrier w).mp hwM)
  rw [← Q.angle_eq_acuteAngle w hw] at he
  simpa only [LambertQuadrilateral.sideA₁,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane] using he

end
end LowDimensionalTopology.Geometry.Polygon
