module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleIncircle
@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section





theorem HalfPlaneLine.incenterNormalAt_norm (L : HalfPlaneLine) (z : ℍ) (hz : z ∈ L.carrier) :
    ‖L.incenterNormalAt z‖ = 1 := by
  cases L with
  | vertical a => rw [HalfPlaneLine.incenterNormalAt_vertical,norm_one]
  | circle c r hr =>
    rw [HalfPlaneLine.incenterNormalAt_circle,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    change r⁻¹ * ‖(z : ℂ) - (c : ℂ)‖ = 1
    rw [show ‖(z : ℂ) - (c : ℂ)‖ = r from hz,inv_mul_cancel₀ hr.ne']

theorem HalfPlaneLine.incenterNormalAt_inner_direction (L : HalfPlaneLine) (z w : ℍ)
    (hz : z ∈ L.carrier) :
    inner ℝ (L.incenterNormalAt z) (hyperbolicDirection z w) =
      z.im * hKleinDenominator w * hKleinAffine L.incenterNormal L.incenterOffset w := by
  have hD := (hKleinDenominator_pos w).ne'
  cases L with
  | vertical a =>
    have hza : z.re = a := hz
    rw [HalfPlaneLine.incenterNormalAt_vertical,verticalLine_incenter_affine]
    simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,Complex.one_re,Complex.one_im,
      hyperbolicDirection,one_mul,zero_mul,add_zero,hKleinDenominator,hza]
    field_simp
  | circle c r hr =>
    have he := norm_sub_real_eq_radius_sq hz
    rw [HalfPlaneLine.incenterNormalAt_circle,circleLine_incenter_affine]
    rw [← Complex.normSq_eq_norm_sq]
    simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,Complex.smul_re,Complex.smul_im,smul_eq_mul,
      Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero,
      UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,hyperbolicDirection,Complex.normSq_apply,
      hKleinDenominator]
    field_simp
    nlinarith only [he]






theorem complex_inner_rotate_right (u v : ℂ) :
    inner ℝ u (Complex.I * v) = -complexCross u v := by
  simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,Complex.mul_re,Complex.mul_im,Complex.I_re,
    Complex.I_im,zero_mul,one_mul,zero_sub,zero_add,complexCross]
  ring

theorem complex_inward_normal_cosine (N M : ℂ) (k l a b : ℝ)
    (hN : ‖N‖ = 1) (hM : ‖M‖ = 1) (hk : k ≠ 0) (hl : l ≠ 0)
    (ha : 0 < a) (hb : 0 < b) :
    let u := k • (Complex.I * N)
    let v := l • (Complex.I * M)
    let w := a • u + b • v
    Real.cos (angle u v) * |inner ℝ N w| * |inner ℝ M w| =
      -(inner ℝ N M * inner ℝ N w * inner ℝ M w) := by
  dsimp only
  have hNu : inner ℝ N (Complex.I * N) = 0 := by
    rw [complex_inner_rotate_right,complexCross_self,neg_zero]
  have hMv : inner ℝ M (Complex.I * M) = 0 := by
    rw [complex_inner_rotate_right,complexCross_self,neg_zero]
  have hNv : inner ℝ N (a • k • (Complex.I * N) + b • l • (Complex.I * M)) =
      -(b * l * complexCross N M) := by
    rw [inner_add_right,inner_smul_right,inner_smul_right,inner_smul_right,
      inner_smul_right,hNu,complex_inner_rotate_right]
    ring
  have hMu : inner ℝ M (a • k • (Complex.I * N) + b • l • (Complex.I * M)) =
      a * k * complexCross N M := by
    rw [inner_add_right,inner_smul_right,inner_smul_right,inner_smul_right,
      inner_smul_right,hMv,complex_inner_rotate_right,complexCross_comm M N]
    ring
  have hcos : Real.cos (angle (k • (Complex.I * N)) (l • (Complex.I * M))) =
      k * l * inner ℝ N M / (|k| * |l|) := by
    rw [cos_angle,real_inner_smul_left,inner_smul_right,complex_inner_rotate,norm_smul,norm_smul,
      norm_mul,norm_mul,Complex.norm_I,hN,hM,one_mul,mul_one,mul_one,Real.norm_eq_abs,
      Real.norm_eq_abs]
    ring
  rw [hNv,hMu,hcos,abs_neg,abs_mul,abs_mul,abs_mul,abs_mul,
    abs_of_pos ha,abs_of_pos hb]
  field_simp
  nlinarith only [congrArg (fun x : ℝ => inner ℝ N M * x) (sq_abs (complexCross N M))]


theorem hAngle_direction_positive_combination {z q : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) (hq : q ∈ properHAngleInterior R S) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ hyperbolicDirection z q =
      a • hyperbolicDirection z R.directionPoint + b • hyperbolicDirection z S.directionPoint := by
  have hRn : R.directionPoint ≠ z := R.directionPoint_mem.2
  have hSn : S.directionPoint ≠ z := S.directionPoint_mem.2
  let T : HTriangle :=
    { a := z, b := R.directionPoint, c := S.directionPoint
      noncollinear := by
        rintro ⟨L,hz,hR,hS⟩
        have hLR : L = R.supportLine := L.eq_of_two_points R.supportLine
          hRn.symm hz hR R.start_mem_support (R.subset_support R.directionPoint_mem.1)
        have hLS : L = S.supportLine := L.eq_of_two_points S.supportLine
          hSn.symm hz hS S.start_mem_support (S.subset_support S.directionPoint_mem.1)
        exact hne (hLR.symm.trans hLS) }
  have hR : T.rayAB = R := hRayThrough_eq hRn.symm R R.directionPoint_mem.1
  have hS : T.rayAC = S := hRayThrough_eq hSn.symm S S.directionPoint_mem.1
  have hqi : q ∈ T.angleInteriorA := by
    change q ∈ properHAngleInterior T.rayAB T.rayAC
    rwa [hR,hS]
  have hzBC := T.angleInteriorA_eq_halfPlanes ▸ hqi
  have hx := mem_image_of_mem T.coordinate hzBC.1
  have hy := mem_image_of_mem T.coordinate hzBC.2
  rw [T.coordinate_image_halfPlaneB] at hx
  rw [T.coordinate_image_halfPlaneC] at hy
  exact T.hyperbolicDirection_positive_combination ⟨hx.2,hy.2⟩

theorem HRayAt.direction_eq_incenterNormalAt {z : ℍ} (R : HRayAt z) :
    ∃ k : ℝ, k ≠ 0 ∧ hyperbolicDirection z R.directionPoint =
      k • (Complex.I * R.supportLine.incenterNormalAt z) := by
  obtain ⟨r,hr,he⟩ := hyperbolicDirection_pos_smul_tangent R R.directionPoint_mem.1
    R.directionPoint_mem.2
  refine ⟨r * R.tangentSign * ‖R.supportLine.tangentAt z‖,
    mul_ne_zero (mul_ne_zero hr.ne' R.tangentSign_ne_zero)
      (norm_ne_zero_iff.mpr (R.supportLine.tangentAt_ne_zero z)),?_⟩
  conv_lhs =>
    rw [he,HRayAt.tangentVector,R.supportLine.tangentAt_eq_incenterNormalAt z R.start_mem_support,
      smul_smul,smul_smul]

/-- The true forward-ray angle determines the signed normalized side-normal product. -/
theorem hAngle_cosine_incenter_normals {z q : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) (hq : q ∈ properHAngleInterior R S) :
    Real.cos (hInteriorAngleMeasure R S) *
        |hKleinAffine R.supportLine.incenterNormal R.supportLine.incenterOffset q| *
        |hKleinAffine S.supportLine.incenterNormal S.supportLine.incenterOffset q| =
      -((inner ℝ R.supportLine.incenterNormal S.supportLine.incenterNormal -
        R.supportLine.incenterOffset * S.supportLine.incenterOffset) *
        hKleinAffine R.supportLine.incenterNormal R.supportLine.incenterOffset q *
        hKleinAffine S.supportLine.incenterNormal S.supportLine.incenterOffset q) := by
  obtain ⟨a,b,ha,hb,hw⟩ := hAngle_direction_positive_combination R S hne hq
  obtain ⟨k,hk,hu⟩ := R.direction_eq_incenterNormalAt
  obtain ⟨l,hl,hv⟩ := S.direction_eq_incenterNormalAt
  have he := complex_inward_normal_cosine (R.supportLine.incenterNormalAt z) (S.supportLine.incenterNormalAt z)
    k l a b (R.supportLine.incenterNormalAt_norm z R.start_mem_support)
    (S.supportLine.incenterNormalAt_norm z S.start_mem_support) hk hl ha hb
  change Real.cos (angle (k • (Complex.I * R.supportLine.incenterNormalAt z))
    (l • (Complex.I * S.supportLine.incenterNormalAt z))) * _ * _ = _ at he
  rw [← hu,← hv,← hw,
    ← hInteriorAngleMeasure_eq_direction R S R.directionPoint_mem.1 R.directionPoint_mem.2
      S.directionPoint_mem.1 S.directionPoint_mem.2,
    R.supportLine.incenterNormalAt_inner_direction z q R.start_mem_support,
    S.supportLine.incenterNormalAt_inner_direction z q S.start_mem_support,
    R.supportLine.incenterNormalAt_inner S.supportLine z R.start_mem_support S.start_mem_support,
    abs_mul,abs_mul,abs_mul,abs_mul,abs_of_pos z.im_pos,
    abs_of_pos (hKleinDenominator_pos q)] at he
  have hp : (z.im * hKleinDenominator q) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero z.im_ne_zero
    (hKleinDenominator_pos q).ne')
  apply mul_left_cancel₀ hp
  calc
    _ = Real.cos (hInteriorAngleMeasure R S) *
        (z.im * hKleinDenominator q * |hKleinAffine R.supportLine.incenterNormal R.supportLine.incenterOffset q|) *
        (z.im * hKleinDenominator q * |hKleinAffine S.supportLine.incenterNormal S.supportLine.incenterOffset q|) := by ring
    _ = _ := he
    _ = _ := by ring


theorem ClosedDiscTriangle.cosine_alpha_side_normals_of_finite (T : ClosedDiscTriangle)
    (a q : 𝔻) (ha : T.a = discToClosedModel a) (hq : q ∈ T.interior) :
    Real.cos T.alpha *
        |closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset (discToClosedModel q)| *
        |closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset (discToClosedModel q)| =
      -((inner ℝ T.sideLineB.incenterNormal T.sideLineC.incenterNormal -
        T.sideLineB.incenterOffset * T.sideLineC.incenterOffset) *
        closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset (discToClosedModel q) *
        closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset (discToClosedModel q)) := by
  let C := T.finiteHalfPlaneCornerAtDiscA a ha
  have hqH : discToHalfPlane q ∈ T.halfPlaneInterior := by
    change halfPlaneToDisc (discToHalfPlane q) ∈ T.interior
    rwa [halfPlaneToDisc_discToHalfPlane]
  have hp := (T.mem_halfPlaneInterior_iff _).mp hqH
  have hqi : discToHalfPlane q ∈ properHAngleInterior C.rayAB C.rayAC :=
    (C.mem_interior_iff _).mpr ⟨hp.1,hp.2.1⟩
  have he := hAngle_cosine_incenter_normals C.rayAB C.rayAC C.proper hqi
  have hangle : T.alpha = hInteriorAngleMeasure C.rayAB C.rayAC := by
    rw [T.alpha_of_finite a ha,discInteriorAngleMeasure_eq_halfPlane,
      T.cornerRayABAtA_toHalfPlane,T.cornerRayACAtA_toHalfPlane]
  rw [C.supportAB,C.supportAC,← hangle] at he
  simp only [hKleinAffine,halfPlaneKleinCoordinate,halfPlaneToDisc_discToHalfPlane] at he
  change Real.cos T.alpha *
    |closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset (discToClosedModel q)| *
    |closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset (discToClosedModel q)| = _ at he
  rw [real_inner_comm T.sideLineB.toHalfPlane.incenterNormal T.sideLineC.toHalfPlane.incenterNormal] at he
  change Real.cos T.alpha * _ * _ =
    -((inner ℝ T.sideLineB.incenterNormal T.sideLineC.incenterNormal -
      T.sideLineC.incenterOffset * T.sideLineB.incenterOffset) *
      closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset (discToClosedModel q) *
      closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset (discToClosedModel q)) at he
  nlinarith only [he]


theorem complex_inner_cross_identity (v n m : ℂ) :
    inner ℝ n v * inner ℝ m v + complexCross v n * complexCross v m =
      ‖v‖ ^ 2 * inner ℝ n m := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,Complex.normSq_apply,complexCross]
  ring

theorem complex_decompose_along_unit (v n : ℂ) (hv : ‖v‖ = 1) :
    n = (inner ℝ n v) • v + (complexCross v n) • (Complex.I * v) := by
  have hv' : v.re ^ 2 + v.im ^ 2 = 1 := by
    have he := Complex.normSq_eq_norm_sq v
    rw [hv] at he
    simpa only [Complex.normSq_apply,one_pow,pow_two,mul_one] using he
  apply Complex.ext
  · simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,Complex.add_re,Complex.smul_re,smul_eq_mul,
      complexCross,Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub]
    nlinarith only [congrArg (fun x : ℝ => n.re * x) hv']
  · simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,Complex.add_im,Complex.smul_im,smul_eq_mul,
      complexCross,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add]
    nlinarith only [congrArg (fun x : ℝ => n.im * x) hv']

/-- At an actual ideal point, two normalized side equations differ by a null normal. -/
theorem boundary_side_normal_relation (v n m : ℂ) (t u : ℝ) (hv : ‖v‖ = 1)
    (hn : ‖n‖ ^ 2 - t ^ 2 = 1) (hm : ‖m‖ ^ 2 - u ^ 2 = 1)
    (ht : inner ℝ n v = t) (hu : inner ℝ m v = u) :
    let B := inner ℝ n m - t * u
    B ^ 2 = 1 ∧ n - B • m = (t - B * u) • v := by
  dsimp only
  let B := inner ℝ n m - t * u
  change B ^ 2 = 1 ∧ n - B • m = (t - B * u) • v
  have hnn := complex_inner_cross_identity v n n
  have hmm := complex_inner_cross_identity v m m
  have hnm := complex_inner_cross_identity v n m
  rw [ht,hu,hv,one_pow,one_mul] at hnm
  rw [ht,hv,one_pow,one_mul,real_inner_self_eq_norm_sq] at hnn
  rw [hu,hv,one_pow,one_mul,real_inner_self_eq_norm_sq] at hmm
  have hk : complexCross v n ^ 2 = 1 := by nlinarith only [hnn,hn]
  have hl : complexCross v m ^ 2 = 1 := by nlinarith only [hmm,hm]
  have hB : B = complexCross v n * complexCross v m := by linarith only [hnm]
  refine ⟨?_,?_⟩
  · rw [hB,mul_pow,hk,hl,one_mul]
  · have hc : complexCross v n - B * complexCross v m = 0 := by
      rw [hB]
      nlinarith only [congrArg (fun x : ℝ => complexCross v n * x) hl]
    calc
      _ = (t - B * u) • v +
          (complexCross v n - B * complexCross v m) • (Complex.I * v) := by
        conv_lhs => rw [complex_decompose_along_unit v n hv,complex_decompose_along_unit v m hv,ht,hu]
        module
      _ = _ := by rw [hc,zero_smul,add_zero]


theorem complex_inner_lt_one_of_closed_ball_ne (v b : ℂ) (hv : ‖v‖ = 1)
    (hb : ‖b‖ ≤ 1) (hne : b ≠ v) : inner ℝ v b < 1 := by
  have hle : inner ℝ v b ≤ 1 := calc
    _ ≤ ‖v‖ * ‖b‖ := real_inner_le_norm _ _
    _ ≤ 1 := by rw [hv,one_mul]; exact hb
  by_contra hnot
  have he : inner ℝ v b = 1 := le_antisymm hle (le_of_not_gt hnot)
  have hd := norm_sub_sq_real b v
  rw [real_inner_comm v b,hv,he] at hd
  have hnorm : ‖b - v‖ = 0 := by nlinarith [norm_nonneg b,norm_nonneg (b - v)]
  exact hne (sub_eq_zero.mp (norm_eq_zero.mp hnorm))

theorem boundary_triangle_side_cosine (v b c n m : ℂ) (t u : ℝ)
    (hv : ‖v‖ = 1) (hb : inner ℝ v b < 1) (hc : inner ℝ v c < 1)
    (hn : ‖n‖ ^ 2 - t ^ 2 = 1) (hm : ‖m‖ ^ 2 - u ^ 2 = 1)
    (ht : inner ℝ n v = t) (hu : inner ℝ m v = u)
    (hbL : inner ℝ n b = t) (hcM : inner ℝ m c = u) :
    |inner ℝ n c - t| * |inner ℝ m b - u| =
      -((inner ℝ n m - t * u) * (inner ℝ n c - t) * (inner ℝ m b - u)) := by
  let B := inner ℝ n m - t * u
  let d := t - B * u
  obtain ⟨hB,he⟩ := boundary_side_normal_relation v n m t u hv hn hm ht hu
  change B ^ 2 = 1 at hB
  change n - B • m = d • v at he
  have heb := congrArg (fun x : ℂ => inner ℝ x b) he
  have hec := congrArg (fun x : ℂ => inner ℝ x c) he
  simp only [inner_sub_left,real_inner_smul_left,hbL] at heb
  simp only [inner_sub_left,real_inner_smul_left,hcM] at hec
  dsimp [d] at heb hec
  have hbg : B * (inner ℝ m b - u) = d * (1 - inner ℝ v b) := by
    dsimp [d]
    nlinarith only [heb]
  have hcf : inner ℝ n c - t = -d * (1 - inner ℝ v c) := by
    dsimp [d]
    nlinarith only [hec]
  have hprod : B * (inner ℝ n c - t) * (inner ℝ m b - u) =
      -d ^ 2 * ((1 - inner ℝ v b) * (1 - inner ℝ v c)) := by
    calc
      _ = (inner ℝ n c - t) * (B * (inner ℝ m b - u)) := by ring
      _ = _ := by rw [hbg,hcf]; ring
  have hnonpos : B * (inner ℝ n c - t) * (inner ℝ m b - u) ≤ 0 := by
    rw [hprod]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
      (mul_nonneg (by linarith) (by linarith))
  have habs : |B| = 1 := by nlinarith [sq_abs B,abs_nonneg B]
  change _ = -(B * _ * _)
  rw [← abs_of_nonpos hnonpos,abs_mul,abs_mul,habs,one_mul]


theorem ClosedDiscTriangle.cosine_alpha_side_normals_of_ideal (T : ClosedDiscTriangle)
    (q : 𝔻) (ha : ‖(T.a : ℂ)‖ = 1) (hq : q ∈ T.interior) :
    Real.cos T.alpha *
        |closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset (discToClosedModel q)| *
        |closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset (discToClosedModel q)| =
      -((inner ℝ T.sideLineB.incenterNormal T.sideLineC.incenterNormal -
        T.sideLineB.incenterOffset * T.sideLineC.incenterOffset) *
        closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset (discToClosedModel q) *
        closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset (discToClosedModel q)) := by
  let FB := closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset
  let FC := closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset
  have hBa : FB T.a = 0 := (T.sideLineB.closed_incenter_affine_zero_iff _).mpr T.a_mem_sideLineB
  have hBc : FB T.c = 0 := (T.sideLineB.closed_incenter_affine_zero_iff _).mpr T.c_mem_sideLineB
  have hCa : FC T.a = 0 := (T.sideLineC.closed_incenter_affine_zero_iff _).mpr T.a_mem_sideLineC
  have hCb : FC T.b = 0 := (T.sideLineC.closed_incenter_affine_zero_iff _).mpr T.b_mem_sideLineC
  have hv : ‖closedKleinCoordinate T.a‖ = 1 := by
    change ‖(closedPoincareToKlein T.a : ℂ)‖ = 1
    rw [closedPoincareToKlein_ideal_fixed T.a ha]
    exact ha
  have hbc : inner ℝ (closedKleinCoordinate T.a) (closedKleinCoordinate T.c) < 1 :=
    complex_inner_lt_one_of_closed_ball_ne _ _ hv (closedPoincareToKlein T.c).norm_le_one
      (closedKleinCoordinate_injective.ne T.c_ne_a)
  have hcb : inner ℝ (closedKleinCoordinate T.a) (closedKleinCoordinate T.b) < 1 :=
    complex_inner_lt_one_of_closed_ball_ne _ _ hv (closedPoincareToKlein T.b).norm_le_one
      (closedKleinCoordinate_injective.ne T.a_ne_b.symm)
  have htB : inner ℝ T.sideLineB.incenterNormal (closedKleinCoordinate T.a) = T.sideLineB.incenterOffset :=
    sub_eq_zero.mp hBa
  have htC : inner ℝ T.sideLineC.incenterNormal (closedKleinCoordinate T.a) = T.sideLineC.incenterOffset :=
    sub_eq_zero.mp hCa
  have hbB : inner ℝ T.sideLineB.incenterNormal (closedKleinCoordinate T.c) = T.sideLineB.incenterOffset :=
    sub_eq_zero.mp hBc
  have hcC : inner ℝ T.sideLineC.incenterNormal (closedKleinCoordinate T.b) = T.sideLineC.incenterOffset :=
    sub_eq_zero.mp hCb
  have he := boundary_triangle_side_cosine (closedKleinCoordinate T.a)
    (closedKleinCoordinate T.c) (closedKleinCoordinate T.b)
    T.sideLineB.incenterNormal T.sideLineC.incenterNormal
    T.sideLineB.incenterOffset T.sideLineC.incenterOffset hv hbc hcb
    T.sideLineB.toHalfPlane.incenterNormal_lorentz_unit
    T.sideLineC.toHalfPlane.incenterNormal_lorentz_unit htB htC hbB hcC
  change |FB T.b| * |FC T.c| =
    -((inner ℝ T.sideLineB.incenterNormal T.sideLineC.incenterNormal -
      T.sideLineB.incenterOffset * T.sideLineC.incenterOffset) * FB T.b * FC T.c) at he
  have hqB : FB (discToClosedModel q) = (T.discCoordinate q).1 * FB T.b := by
    dsimp [FB]
    rw [T.kleinAffine_reconstruction]
    change (1 - (T.discCoordinate q).1 - (T.discCoordinate q).2) * FB T.a +
      (T.discCoordinate q).1 * FB T.b + (T.discCoordinate q).2 * FB T.c = _
    rw [hBa,hBc]
    ring
  have hqC : FC (discToClosedModel q) = (T.discCoordinate q).2 * FC T.c := by
    dsimp [FC]
    rw [T.kleinAffine_reconstruction]
    change (1 - (T.discCoordinate q).1 - (T.discCoordinate q).2) * FC T.a +
      (T.discCoordinate q).1 * FC T.b + (T.discCoordinate q).2 * FC T.c = _
    rw [hCa,hCb]
    ring
  have hp := T.incenter_interior_coordinates hq
  rw [T.alpha_of_ideal ha,Real.cos_zero,one_mul]
  change |FB (discToClosedModel q)| * |FC (discToClosedModel q)| =
    -((inner ℝ T.sideLineB.incenterNormal T.sideLineC.incenterNormal -
      T.sideLineB.incenterOffset * T.sideLineC.incenterOffset) *
      FB (discToClosedModel q) * FC (discToClosedModel q))
  rw [hqB,hqC,abs_mul,abs_mul,abs_of_pos hp.1,abs_of_pos hp.2.1]
  nlinarith only [congrArg (fun x : ℝ => (T.discCoordinate q).1 * (T.discCoordinate q).2 * x) he]

/-- Every source triangle angle, including ideal angles, is the inward side-normal cosine. -/
theorem ClosedDiscTriangle.cosine_alpha_side_normals (T : ClosedDiscTriangle) (q : 𝔻)
    (hq : q ∈ T.interior) :
    Real.cos T.alpha *
        |closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset (discToClosedModel q)| *
        |closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset (discToClosedModel q)| =
      -((inner ℝ T.sideLineB.incenterNormal T.sideLineC.incenterNormal -
        T.sideLineB.incenterOffset * T.sideLineC.incenterOffset) *
        closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset (discToClosedModel q) *
        closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset (discToClosedModel q)) := by
  by_cases ha : ‖(T.a : ℂ)‖ < 1
  · exact T.cosine_alpha_side_normals_of_finite (closedDiscFinitePoint T.a ha) q
      (closedDiscFinitePoint_spec T.a ha).symm hq
  · exact T.cosine_alpha_side_normals_of_ideal q (le_antisymm T.a.norm_le_one (le_of_not_gt ha)) hq

end
end LowDimensionalTopology.Geometry.Hyperbolic
