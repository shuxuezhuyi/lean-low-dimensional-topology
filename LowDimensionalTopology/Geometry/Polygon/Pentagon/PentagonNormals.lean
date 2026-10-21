module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.GeodesicNormalCoordinates
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleInradius
@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

theorem complex_eq_projection_of_unit_perpendicular (K N L : ℂ)
    (hK : ‖K‖ ^ 2 = 1) (hN : ‖N‖ ^ 2 = 1) (hKN : inner ℝ K N = 0)
    (hLN : inner ℝ L N = 0) : L = (inner ℝ L K) • K := by
  have hg := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_gram_three K N L
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
    hK,hN,hKN,real_inner_comm L N,hLN] at hg
  have hd : ‖L - (inner ℝ L K) • K‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hK,inner_smul_right]
    nlinarith only [hg]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hd))


/-- The spatial projection of a true two-right-angle chain is its actual invariant side pairing. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalSpatialAt_eq_pairing_smul (K N L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a b : ℍ)
    (ha : K.OrthogonalAt N a) (hb : N.OrthogonalAt L b) :
    L.normalSpatialAt a = L.normalPairing K • K.normalSpatialAt a := by
  have hK := (K.normalTimeAt_eq_zero_iff a).mpr ha.1
  have hN := (N.normalTimeAt_eq_zero_iff a).mpr ha.2.1
  have hk := K.normalSpatialAt_norm_sq a
  have hn := N.normalSpatialAt_norm_sq a
  rw [hK,zero_pow (by omega : 2 ≠ 0),add_zero] at hk
  rw [hN,zero_pow (by omega : 2 ≠ 0),add_zero] at hn
  have hkn := K.normalSpatialAt_inner N a
  rw [K.normalPairing_orthogonal N a ha,hK,zero_mul,add_zero] at hkn
  have hln := L.normalSpatialAt_inner N a
  rw [L.normalPairing_comm N,N.normalPairing_orthogonal L b hb,hN,mul_zero,add_zero] at hln
  have he := complex_eq_projection_of_unit_perpendicular _ _ _ hk hn hkn hln
  rw [L.normalSpatialAt_inner K a,hK,mul_zero,add_zero] at he
  exact he

/-- Exact point/normal Lorentz covariance, without requiring incidence at the second point. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalSpatialAt_inner_boost_point_general (L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (z w : ℍ) :
    inner ℝ (L.normalSpatialAt z)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.sideNormalBoost
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial z)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight z)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial
          w) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight w)) =
      -L.normalTimeAt w + L.normalTimeAt z * Real.cosh (dist z w) := by
  have he := _root_.LowDimensionalTopology.Geometry.Hyperbolic.sideNormalBoost_inner (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial z) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight z)
    L.incenterNormal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial
      w) L.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight w)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_lorentz_unit z) (ne_of_gt (by linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_pos z]))
  rw [real_inner_comm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial z)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial
    w),_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePoint_cosh_distance z w] at he
  change inner ℝ (L.normalSpatialAt z)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.sideNormalBoost
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial z)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight z)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial
        w) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight w)) =
      inner ℝ L.incenterNormal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial
        w) - L.incenterOffset * _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight w +
        L.normalTimeAt z * Real.cosh (dist z w) at he
  change _ = -(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight w * L.incenterOffset - inner ℝ
    L.incenterNormal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial w)) + _
  nlinarith only [he]

/-- Four genuine right angles give the intrinsic signed pentagon pairing identity. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.pentagon_normal_pairing (K N P L M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a b e d : ℍ)
    (ha : K.OrthogonalAt N a) (hb : N.OrthogonalAt L b)
    (he : K.OrthogonalAt P e) (hd : P.OrthogonalAt M d) :
    L.normalPairing M = L.normalPairing K * M.normalPairing K -
      L.normalTimeAt a * M.normalTimeAt e * Real.cosh (dist a e) := by
  have hLa := K.normalSpatialAt_eq_pairing_smul N L a b ha hb
  have hMe := K.normalSpatialAt_eq_pairing_smul P M e d he hd
  have hKe := (K.normalTimeAt_eq_zero_iff e).mpr he.1
  have hKa := (K.normalTimeAt_eq_zero_iff a).mpr ha.1
  have hKX := K.normalSpatialAt_inner_boost_point e a ha.1
  rw [hKe,zero_mul] at hKX
  have hMX := M.normalSpatialAt_inner_boost_point_general e a
  rw [hMe,real_inner_smul_left,hKX,mul_zero] at hMX
  rw [dist_comm e a] at hMX
  have hMtime : M.normalTimeAt a = M.normalTimeAt e * Real.cosh (dist a e) := by linarith only [hMX]
  have hLM := L.normalSpatialAt_inner M a
  rw [hLa,real_inner_smul_left,real_inner_comm (M.normalSpatialAt a) (K.normalSpatialAt a),
    M.normalSpatialAt_inner K a,hKa,mul_zero,add_zero,hMtime] at hLM
  nlinarith only [hLM]

/-- The actual finite side in a two-right-angle chain is the width of its opposite support pair. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalPairing_abs_two_right_angles (K N L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a b : ℍ)
    (ha : K.OrthogonalAt N a) (hb : N.OrthogonalAt L b) :
    |L.normalPairing K| = Real.cosh (dist a b) := by
  have hproj := K.normalSpatialAt_eq_pairing_smul N L a b ha hb
  have hK := K.normalSpatialAt_norm_sq a
  rw [(K.normalTimeAt_eq_zero_iff a).mpr ha.1,zero_pow (by omega : 2 ≠ 0),add_zero] at hK
  have hL := L.normalSpatialAt_norm_sq a
  rw [hproj,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hK,mul_one] at hL
  have hs := Real.cosh_sq_sub_sinh_sq (L.pointDist a)
  rw [← L.normalTimeAt_abs,sq_abs] at hs
  have hb' : L.OrthogonalAt N b := ⟨hb.2.1,hb.1,by rw [real_inner_comm]; exact hb.2.2⟩
  rw [L.pointDist_eq_dist_of_perpendicular N b a hb' ha.2.1] at hs
  apply (sq_eq_sq₀ (abs_nonneg _) (Real.cosh_pos _).le).mp
  rw [sq_abs]
  nlinarith only [hL,hs]




/-- The invariant pairing with inward-facing opposite support normals has the negative distance sign. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.inward_pairing_two_right_angles (K N L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a b : ℍ)
    (ha : K.OrthogonalAt N a) (hb : N.OrthogonalAt L b) (hab : a ≠ b) :
    L.inwardNormalSign a * K.inwardNormalSign b * L.normalPairing K = -Real.cosh (dist a b) := by
  have hb' : L.OrthogonalAt N b := ⟨hb.2.1,hb.1,by rw [real_inner_comm]; exact hb.2.2⟩
  have hsL : |L.normalTimeAt a| = Real.sinh (dist a b) := by
    rw [L.normalTimeAt_abs,L.pointDist_eq_dist_of_perpendicular N b a hb' ha.2.1]
  have hsK : |K.normalTimeAt b| = Real.sinh (dist a b) := by
    rw [K.normalTimeAt_abs,K.pointDist_eq_dist_of_perpendicular N a b ha hb.1,dist_comm b a]
  have hs : 0 < Real.sinh (dist a b) := Real.sinh_pos_iff.mpr (dist_pos.mpr hab)
  have htL : |L.normalTimeAt a| ≠ 0 := ne_of_gt (hsL.symm ▸ hs)
  have htK : |K.normalTimeAt b| ≠ 0 := ne_of_gt (hsK.symm ▸ hs)
  have hproj := K.normalSpatialAt_eq_pairing_smul N L a b ha hb
  have hinner := L.normalSpatialAt_inner_boost_point a b hb.2.1
  rw [hproj,real_inner_smul_left,K.normalSpatialAt_inner_boost_point_general a b,
    (K.normalTimeAt_eq_zero_iff a).mpr ha.1,zero_mul,add_zero] at hinner
  have hrel : L.normalPairing K * K.normalTimeAt b = -L.normalTimeAt a * Real.cosh (dist a b) := by
    nlinarith only [hinner]
  unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.inwardNormalSign
  field_simp
  have he : L.normalTimeAt a ^ 2 = |L.normalTimeAt a| * |K.normalTimeAt b| := by
    have heq : |L.normalTimeAt a| = |K.normalTimeAt b| := hsL.trans hsK.symm
    rw [← heq,← pow_two,sq_abs]
  calc
    _ = L.normalTimeAt a * (L.normalPairing K * K.normalTimeAt b) := by ring
    _ = -(L.normalTimeAt a ^ 2 * Real.cosh (dist a b)) := by rw [hrel]; ring
    _ = _ := by rw [he]

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.inwardNormalSign_eq_of_time_mul_pos (L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a b : ℍ)
    (hab : 0 < L.normalTimeAt a * L.normalTimeAt b) : L.inwardNormalSign a = L.inwardNormalSign b := by
  unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.inwardNormalSign
  rcases mul_pos_iff.mp hab with h | h
  · rw [abs_of_pos h.1,abs_of_pos h.2]
    simp only [neg_div,div_self h.1.ne',div_self h.2.ne']
  · rw [abs_of_neg h.1,abs_of_neg h.2]
    simp only [neg_div_neg_eq,div_self h.1.ne,div_self h.2.ne]

/-- The native inward normalization agrees with the intrinsic half-plane sign. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.inradiusSign_eq_inwardNormalSign (L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (q : 𝔻) :
    L.inradiusSign q = L.toHalfPlane.inwardNormalSign (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane q) := by
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine L.toHalfPlane.incenterNormal L.toHalfPlane.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane q) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine L.incenterNormal L.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q) := by
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.incenterNormal,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.incenterOffset,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.inwardNormalSign,L.toHalfPlane.normalTimeAt_eq_affine,he]
  let F := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine L.incenterNormal L.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q)
  let h := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane q)
  change F / |F| = -(-h * F) / |-h * F|
  have hh : 0 < h := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_pos _
  rw [neg_mul,neg_neg,abs_neg,abs_mul,abs_of_pos hh,mul_div_mul_left F |F| hh.ne']

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.sideB_affine_eq_coordinate (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (p : 𝕔𝔻) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset p =
      (T.coordinate p).1 * _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset T.b := by
  rw [T.kleinAffine_reconstruction,
    (T.sideLineB.closed_incenter_affine_zero_iff _).mpr T.a_mem_sideLineB,
    (T.sideLineB.closed_incenter_affine_zero_iff _).mpr T.c_mem_sideLineB]
  ring

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.sideC_affine_eq_coordinate (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (p : 𝕔𝔻) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset p =
      (T.coordinate p).2 * _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset T.c := by
  rw [T.kleinAffine_reconstruction,
    (T.sideLineC.closed_incenter_affine_zero_iff _).mpr T.a_mem_sideLineC,
    (T.sideLineC.closed_incenter_affine_zero_iff _).mpr T.b_mem_sideLineC]
  ring

theorem real_sign_div_abs_pos_mul (a v : ℝ) (ha : 0 < a) : (a * v) / |a * v| = v / |v| := by
  rw [abs_mul,abs_of_pos ha,mul_div_mul_left v |v| ha.ne']

/-- The actual inward orientations of both adjacent sides are constant throughout the corner cone. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.inradiusSigns_eq_of_positive_coordinates (T
  : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (q r : 𝔻)
    (hq : 0 < (T.discCoordinate q).1 ∧ 0 < (T.discCoordinate q).2)
    (hr : 0 < (T.discCoordinate r).1 ∧ 0 < (T.discCoordinate r).2) :
    T.sideLineB.inradiusSign q = T.sideLineB.inradiusSign r ∧
      T.sideLineC.inradiusSign q = T.sideLineC.inradiusSign r := by
  constructor
  · unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.inradiusSign
    dsimp only
    rw [T.sideB_affine_eq_coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q),
      T.sideB_affine_eq_coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel r)]
    change ((T.discCoordinate q).1 * _) / |(T.discCoordinate q).1 * _| =
      ((T.discCoordinate r).1 * _) / |(T.discCoordinate r).1 * _|
    rw [real_sign_div_abs_pos_mul _ _ hq.1,real_sign_div_abs_pos_mul _ _ hr.1]
  · unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.inradiusSign
    dsimp only
    rw [T.sideC_affine_eq_coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q),
      T.sideC_affine_eq_coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel r)]
    change ((T.discCoordinate q).2 * _) / |(T.discCoordinate q).2 * _| =
      ((T.discCoordinate r).2 * _) / |(T.discCoordinate r).2 * _|
    rw [real_sign_div_abs_pos_mul _ _ hq.2,real_sign_div_abs_pos_mul _ _ hr.2]

/-- Actual finite or ideal corners give the sign-correct intrinsic side pairing. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.inward_normalPairing_cosine_of_positive_coordinates
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (q : 𝔻)
    (hq : 0 < (T.discCoordinate q).1 ∧ 0 < (T.discCoordinate q).2) :
    T.sideLineB.toHalfPlane.inwardNormalSign (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane q) *
      T.sideLineC.toHalfPlane.inwardNormalSign (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane q) *
        T.sideLineB.toHalfPlane.normalPairing T.sideLineC.toHalfPlane = -Real.cos T.alpha := by
  rw [← T.sideLineB.inradiusSign_eq_inwardNormalSign,← T.sideLineC.inradiusSign_eq_inwardNormalSign]
  have he := T.cosine_alpha_side_normals_of_positive_coordinates q hq
  have hn := T.positive_coordinates_not_adjacent_sides q hq
  have hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q) ≠ 0 := by
    intro hf
    exact hn.1 ((T.sideLineB.closedCarrier_mem_interior_iff q).mp
      ((T.sideLineB.closed_incenter_affine_zero_iff _).mp hf))
  have hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q) ≠ 0 := by
    intro hf
    exact hn.2 ((T.sideLineC.closedCarrier_mem_interior_iff q).mp
      ((T.sideLineC.closed_incenter_affine_zero_iff _).mp hf))
  change T.sideLineB.inradiusSign q * T.sideLineC.inradiusSign q *
    (inner ℝ T.sideLineB.incenterNormal T.sideLineC.incenterNormal -
      T.sideLineB.incenterOffset * T.sideLineC.incenterOffset) = _
  dsimp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.inradiusSign]
  field_simp
  nlinarith only [he]

/-- Five actual perpendicular incidences imply the opposite-side sine relation in a right pentagon. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.right_pentagon_sinh_identity (K N P L M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a b c d e : ℍ)
    (ha : K.OrthogonalAt N a) (hb : N.OrthogonalAt L b) (hc : L.OrthogonalAt M c)
    (hd : M.OrthogonalAt P d) (he : K.OrthogonalAt P e) :
    Real.sinh (dist a b) * Real.sinh (dist a e) = Real.cosh (dist d c) := by
  have ha' : N.OrthogonalAt K a := ⟨ha.2.1,ha.1,by rw [real_inner_comm]; exact ha.2.2⟩
  have hprod := N.lambert_sinh_lengths K L P a b e ha' hb he
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlane_inversiveProduct_eq_normal_product] at hprod
  change _ = |L.normalPairing P| at hprod
  rw [L.normalPairing_comm P] at hprod
  rw [L.normalPairing_abs_two_right_angles M P c d hc hd,dist_comm c d] at hprod
  exact hprod

/-- Four actual right angles determine the inward-oriented opposite support pairing. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.four_right_chain_inward_pairing (K N P L M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a b e d : ℍ)
    (ha : K.OrthogonalAt N a) (hb : N.OrthogonalAt L b)
    (he : K.OrthogonalAt P e) (hd : P.OrthogonalAt M d)
    (hab : a ≠ b) (hed : e ≠ d)
    (hsame : 0 < K.normalTimeAt b * K.normalTimeAt d) :
    L.inwardNormalSign a * M.inwardNormalSign e * L.normalPairing M =
      Real.cosh (dist a b) * Real.cosh (dist e d) -
        Real.sinh (dist a b) * Real.cosh (dist a e) * Real.sinh (dist e d) := by
  let l := L.inwardNormalSign a
  let m := M.inwardNormalSign e
  let k := K.inwardNormalSign b
  have hksame : K.inwardNormalSign d = k := (K.inwardNormalSign_eq_of_time_mul_pos b d hsame).symm
  have hkNot : b ∉ K.carrier := by
    intro hmem
    have ht := (K.normalTimeAt_eq_zero_iff b).mpr hmem
    rw [ht,zero_mul] at hsame
    exact lt_irrefl 0 hsame
  have hk2 : k ^ 2 = 1 := K.inwardNormalSign_sq b hkNot
  have hLK := K.inward_pairing_two_right_angles N L a b ha hb hab
  have hMK := K.inward_pairing_two_right_angles P M e d he hd hed
  rw [hksame] at hMK
  change l * k * L.normalPairing K = -Real.cosh (dist a b) at hLK
  change m * k * M.normalPairing K = -Real.cosh (dist e d) at hMK
  have hproduct : l * m * L.normalPairing K * M.normalPairing K =
      Real.cosh (dist a b) * Real.cosh (dist e d) := by
    calc
      _ = (l * k * L.normalPairing K) * (m * k * M.normalPairing K) := by
        have hu := congrArg (fun x : ℝ => l * m * L.normalPairing K * M.normalPairing K * x) hk2
        nlinarith only [hu]
      _ = _ := by rw [hLK,hMK]; ring
  have hb' : L.OrthogonalAt N b := ⟨hb.2.1,hb.1,by rw [real_inner_comm]; exact hb.2.2⟩
  have hd' : M.OrthogonalAt P d := ⟨hd.2.1,hd.1,by rw [real_inner_comm]; exact hd.2.2⟩
  have hlTime := L.inwardNormalSign_mul_time a
  have hmTime := M.inwardNormalSign_mul_time e
  rw [L.pointDist_eq_dist_of_perpendicular N b a hb' ha.2.1] at hlTime
  rw [M.pointDist_eq_dist_of_perpendicular P d e hd' he.2.1] at hmTime
  change l * L.normalTimeAt a = -Real.sinh (dist a b) at hlTime
  change m * M.normalTimeAt e = -Real.sinh (dist e d) at hmTime
  have htimes : l * m * L.normalTimeAt a * M.normalTimeAt e =
      Real.sinh (dist a b) * Real.sinh (dist e d) := by
    calc
      _ = (l * L.normalTimeAt a) * (m * M.normalTimeAt e) := by ring
      _ = _ := by rw [hlTime,hmTime]; ring
  have hraw := K.pentagon_normal_pairing N P L M a b e d ha hb he hd
  have hscaled := congrArg (fun x : ℝ => l * m * x) hraw
  have htimes' := congrArg (fun x : ℝ => x * Real.cosh (dist a e)) htimes
  change l * m * L.normalPairing M = _
  nlinarith only [hscaled,hproduct,htimes']

/-- A genuine convex-position five-vertex configuration with four actual right angles.
The remaining corner is an actual finite/ideal closed triangle corner. -/
structure FourRightPentagon where
  corner : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle
  a : 𝔻
  b : 𝔻
  d : 𝔻
  e : 𝔻
  vertex_d : corner.b = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel d
  vertex_b : corner.c = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel b
  top : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine
  right : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine
  left : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine
  angle_a : top.OrthogonalAt right a
  angle_b : right.OrthogonalAt corner.sideLineB b
  angle_e : top.OrthogonalAt left e
  angle_d : left.OrthogonalAt corner.sideLineC d
  convex_a : 0 < (corner.discCoordinate a).1 ∧ 0 < (corner.discCoordinate a).2
  convex_e : 0 < (corner.discCoordinate e).1 ∧ 0 < (corner.discCoordinate e).2
  top_same_side : 0 < top.toHalfPlane.normalTimeAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
    b) *
    top.toHalfPlane.normalTimeAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane d)

def FourRightPentagon.angle (Q : FourRightPentagon) : ℝ := Q.corner.alpha

def FourRightPentagon.sideA (Q :
  FourRightPentagon) : ℝ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist Q.a Q.b

def FourRightPentagon.sideB (Q :
  FourRightPentagon) : ℝ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist Q.a Q.e

def FourRightPentagon.sideC (Q :
  FourRightPentagon) : ℝ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist Q.e Q.d

theorem FourRightPentagon.a_ne_b (Q : FourRightPentagon) : Q.a ≠ Q.b := by
  intro he
  exact (Q.corner.positive_coordinates_not_adjacent_sides Q.a Q.convex_a).1 (he.symm ▸ Q.angle_b.2.1)

theorem FourRightPentagon.e_ne_d (Q : FourRightPentagon) : Q.e ≠ Q.d := by
  intro he
  exact (Q.corner.positive_coordinates_not_adjacent_sides Q.e Q.convex_e).2 (he.symm ▸ Q.angle_d.2.1)

/-- The four-right-angle pentagon relation uses actual native lengths and the genuine finite/ideal interior angle. -/
theorem FourRightPentagon.cosh_side_cosh_side_add_cos_angle_identity (Q : FourRightPentagon) :
    Real.cosh Q.sideA * Real.cosh Q.sideC + Real.cos Q.angle =
      Real.sinh Q.sideA * Real.cosh Q.sideB * Real.sinh Q.sideC := by
  let K := Q.top.toHalfPlane
  let N := Q.right.toHalfPlane
  let P := Q.left.toHalfPlane
  let L := Q.corner.sideLineB.toHalfPlane
  let M := Q.corner.sideLineC.toHalfPlane
  let a := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.a
  let b := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.b
  let d := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.d
  let e := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.e
  have ha : K.OrthogonalAt N a := (Q.top.orthogonalAt_iff_halfPlane Q.right Q.a).mp Q.angle_a
  have hb : N.OrthogonalAt L b := (Q.right.orthogonalAt_iff_halfPlane Q.corner.sideLineB Q.b).mp Q.angle_b
  have he : K.OrthogonalAt P e := (Q.top.orthogonalAt_iff_halfPlane Q.left Q.e).mp Q.angle_e
  have hd : P.OrthogonalAt M d := (Q.left.orthogonalAt_iff_halfPlane Q.corner.sideLineC Q.d).mp Q.angle_d
  have hab : a ≠ b := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective.ne Q.a_ne_b
  have hed : e ≠ d := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective.ne Q.e_ne_d
  have hchain := K.four_right_chain_inward_pairing N P L M a b e d ha hb he hd hab hed Q.top_same_side
  have hMsign := (Q.corner.inradiusSigns_eq_of_positive_coordinates Q.a Q.e Q.convex_a Q.convex_e).2
  rw [Q.corner.sideLineC.inradiusSign_eq_inwardNormalSign,
    Q.corner.sideLineC.inradiusSign_eq_inwardNormalSign] at hMsign
  have hcorner := Q.corner.inward_normalPairing_cosine_of_positive_coordinates Q.a Q.convex_a
  rw [hMsign] at hcorner
  change L.inwardNormalSign a * M.inwardNormalSign e * L.normalPairing M = -Real.cos Q.angle at hcorner
  simp only [FourRightPentagon.sideA,FourRightPentagon.sideB,FourRightPentagon.sideC,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]
  change Real.cosh (dist a b) * Real.cosh (dist e d) + Real.cos Q.angle =
    Real.sinh (dist a b) * Real.cosh (dist a e) * Real.sinh (dist e d)
  nlinarith only [hchain,hcorner]

/-- Actual common-point orthogonality follows from a zero genuine normalized side pairing. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.orthogonalAt_of_normalPairing_zero (L M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (z : ℍ)
    (hzL : z ∈ L.carrier) (hzM : z ∈ M.carrier) (hLM : L.normalPairing M = 0) :
    L.OrthogonalAt M z := by
  refine ⟨hzL,hzM,?_⟩
  rw [L.tangentAt_eq_incenterNormalAt z hzL,M.tangentAt_eq_incenterNormalAt z hzM,
    real_inner_smul_left,inner_smul_right,_root_.LowDimensionalTopology.Geometry.Hyperbolic.complex_inner_rotate,L.incenterNormalAt_inner M z hzL hzM]
  change ‖L.tangentAt z‖ * (‖M.tangentAt z‖ * L.normalPairing M) = 0
  rw [hLM,mul_zero,mul_zero]

/-- The first all-right-angle specialization uses the true native edge lengths. -/
theorem FourRightPentagon.tanh_side_cosh_side_tanh_side_eq_one_of_right (Q : FourRightPentagon) (hφ : Q.angle = Real.pi
  / 2) :
    Real.tanh Q.sideA * Real.cosh Q.sideB * Real.tanh Q.sideC = 1 := by
  have he := Q.cosh_side_cosh_side_add_cos_angle_identity
  rw [hφ,Real.cos_pi_div_two,add_zero] at he
  rw [Real.tanh_eq_sinh_div_cosh,Real.tanh_eq_sinh_div_cosh]
  have ha := (Real.cosh_pos Q.sideA).ne'
  have hc := (Real.cosh_pos Q.sideC).ne'
  field_simp
  nlinarith only [he]

/-- A right fifth angle forces a finite vertex and the genuine perpendicularity there. -/
theorem FourRightPentagon.exists_finite_right_corner (Q : FourRightPentagon) (hφ : Q.angle = Real.pi / 2) :
    ∃ w : 𝔻, Q.corner.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w ∧
      Q.corner.sideLineB.toHalfPlane.OrthogonalAt Q.corner.sideLineC.toHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) := by
  have hfinite : ‖(Q.corner.a : ℂ)‖ < 1 := by
    by_contra! hn
    have he := Q.corner.alpha_of_ideal (le_antisymm Q.corner.a.norm_le_one hn)
    change Q.angle = 0 at he
    rw [hφ] at he
    linarith only [he,Real.pi_pos]
  let w := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint Q.corner.a hfinite
  have hw : Q.corner.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ _).symm
  have hn := Q.corner.positive_coordinates_not_adjacent_sides Q.a Q.convex_a
  have hLsq := Q.corner.sideLineB.inradiusSign_sq Q.a hn.1
  have hMsq := Q.corner.sideLineC.inradiusSign_sq Q.a hn.2
  rw [Q.corner.sideLineB.inradiusSign_eq_inwardNormalSign] at hLsq
  rw [Q.corner.sideLineC.inradiusSign_eq_inwardNormalSign] at hMsq
  have hLne : Q.corner.sideLineB.toHalfPlane.inwardNormalSign (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.a) ≠ 0 := by
    intro he
    rw [he] at hLsq
    norm_num at hLsq
  have hMne : Q.corner.sideLineC.toHalfPlane.inwardNormalSign (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.a) ≠ 0 := by
    intro he
    rw [he] at hMsq
    norm_num at hMsq
  have he := Q.corner.inward_normalPairing_cosine_of_positive_coordinates Q.a Q.convex_a
  change _ = -Real.cos Q.angle at he
  rw [hφ,Real.cos_pi_div_two,neg_zero] at he
  have hpair : Q.corner.sideLineB.toHalfPlane.normalPairing Q.corner.sideLineC.toHalfPlane = 0 :=
    (mul_eq_zero.mp he).resolve_left (mul_ne_zero hLne hMne)
  refine ⟨w,hw,?_⟩
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.orthogonalAt_of_normalPairing_zero _ _ _ _ _ hpair
  · apply (Q.corner.sideLineB.mem_carrier w).mp
    apply (Q.corner.sideLineB.closedCarrier_mem_interior_iff w).mp
    rw [← hw]
    exact Q.corner.a_mem_sideLineB
  · apply (Q.corner.sideLineC.mem_carrier w).mp
    apply (Q.corner.sideLineC.closedCarrier_mem_interior_iff w).mp
    rw [← hw]
    exact Q.corner.a_mem_sideLineC

/-- The second all-right-angle specialization has an actual opposite finite edge. -/
theorem FourRightPentagon.exists_finite_corner_and_sinh_side_mul_eq_cosh_opposite_of_right (Q : FourRightPentagon) (hφ :
  Q.angle = Real.pi / 2) :
    ∃ w : 𝔻, Q.corner.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w ∧
      Real.sinh Q.sideA * Real.sinh Q.sideB = Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist Q.d w) := by
  obtain ⟨w,hw,hc⟩ := Q.exists_finite_right_corner hφ
  have ha := (Q.top.orthogonalAt_iff_halfPlane Q.right Q.a).mp Q.angle_a
  have hb := (Q.right.orthogonalAt_iff_halfPlane Q.corner.sideLineB Q.b).mp Q.angle_b
  have he := (Q.top.orthogonalAt_iff_halfPlane Q.left Q.e).mp Q.angle_e
  have hd := (Q.left.orthogonalAt_iff_halfPlane Q.corner.sideLineC Q.d).mp Q.angle_d
  have hd' : Q.corner.sideLineC.toHalfPlane.OrthogonalAt Q.left.toHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.d) :=
    ⟨hd.2.1,hd.1,by rw [real_inner_comm]; exact hd.2.2⟩
  have hresult := Q.top.toHalfPlane.right_pentagon_sinh_identity Q.right.toHalfPlane Q.left.toHalfPlane
    Q.corner.sideLineB.toHalfPlane Q.corner.sideLineC.toHalfPlane
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      Q.a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      Q.b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      w) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      Q.d) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.e)
    ha hb hc hd' he
  refine ⟨w,hw,?_⟩
  simpa only [FourRightPentagon.sideA,FourRightPentagon.sideB,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane] using hresult

/-- With both exact source specializations and a genuine finite fifth vertex. -/
theorem FourRightPentagon.tanh_product_and_finite_corner_sinh_identity_of_right (Q : FourRightPentagon) (hφ : Q.angle =
  Real.pi / 2) :
    Real.tanh Q.sideA * Real.cosh Q.sideB * Real.tanh Q.sideC = 1 ∧
      ∃ w : 𝔻, Q.corner.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w ∧
        Real.sinh Q.sideA * Real.sinh Q.sideB = Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist Q.d w) :=
  ⟨Q.tanh_side_cosh_side_tanh_side_eq_one_of_right hφ,Q.exists_finite_corner_and_sinh_side_mul_eq_cosh_opposite_of_right
    hφ⟩

end
end LowDimensionalTopology.Geometry.Polygon
