/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleCongruence
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleCoordinates
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PointLineFormulas
@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section



theorem HTriangle.kleinAffine_reconstruction (T : HTriangle) (n : ℂ) (t : ℝ) (z : ℍ) :
    hKleinAffine n t z = (1 - (T.coordinate z).1 - (T.coordinate z).2) * hKleinAffine n t T.a +
      (T.coordinate z).1 * hKleinAffine n t T.b + (T.coordinate z).2 * hKleinAffine n t T.c := by
  unfold hKleinAffine
  rw [T.inner_klein_reconstruction n z]
  ring

/-- Three independently scaled genuine side equations have an equal-absolute-value point
strictly inside the actual hyperbolic triangle. -/
theorem HTriangle.exists_equal_absolute_side_equations (T : HTriangle)
    (nA nB nC : ℂ) (tA tB tC : ℝ)
    (hA : ∀ z : ℍ, z ∈ T.sideLineA.carrier ↔ hKleinAffine nA tA z = 0)
    (hB : ∀ z : ℍ, z ∈ T.sideLineB.carrier ↔ hKleinAffine nB tB z = 0)
    (hC : ∀ z : ℍ, z ∈ T.sideLineC.carrier ↔ hKleinAffine nC tC z = 0) :
    ∃ z ∈ T.interior, |hKleinAffine nA tA z| = |hKleinAffine nB tB z| ∧
      |hKleinAffine nB tB z| = |hKleinAffine nC tC z| := by
  let u := |hKleinAffine nA tA T.a|
  let v := |hKleinAffine nB tB T.b|
  let w := |hKleinAffine nC tC T.c|
  have hu : 0 < u := abs_pos.mpr (fun h => T.a_not_mem_sideLineA ((hA _).mpr h))
  have hv : 0 < v := abs_pos.mpr (fun h => T.b_not_mem_sideLineB ((hB _).mpr h))
  have hw : 0 < w := abs_pos.mpr (fun h => T.c_not_mem_sideLineC ((hC _).mpr h))
  let D := u * v + u * w + v * w
  have hD : 0 < D := by dsimp [D]; positivity
  let x := u * w / D
  let y := u * v / D
  have hxy : (x,y) ∈ standardOpenTriangle := by
    refine ⟨div_pos (mul_pos hu hw) hD, div_pos (mul_pos hu hv) hD, ?_⟩
    change u * w / D + u * v / D < 1
    rw [← add_div, div_lt_one hD]
    dsimp [D]
    nlinarith [mul_pos hv hw]
  obtain ⟨z, hz, hcoord⟩ : (x,y) ∈ T.coordinate '' T.interior := by
    rw [T.coordinate_image_interior]
    exact hxy
  have hAzB : hKleinAffine nA tA T.b = 0 := (hA _).mp T.rayBC.start_mem_support
  have hAzC : hKleinAffine nA tA T.c = 0 :=
    (hA _).mp (T.rayBC.subset_support T.c_mem_rayBC)
  have hBzA : hKleinAffine nB tB T.a = 0 :=
    (hB _).mp (T.rayCA.subset_support T.a_mem_rayCA)
  have hBzC : hKleinAffine nB tB T.c = 0 := (hB _).mp T.rayCA.start_mem_support
  have hCzA : hKleinAffine nC tC T.a = 0 := (hC _).mp T.rayAB.start_mem_support
  have hCzB : hKleinAffine nC tC T.b = 0 :=
    (hC _).mp (T.rayAB.subset_support T.b_mem_rayAB)
  have heA : hKleinAffine nA tA z = (v * w / D) * hKleinAffine nA tA T.a := by
    rw [T.kleinAffine_reconstruction, hcoord, hAzB, hAzC]
    dsimp only [x,y]
    have he : 1 - u * w / D - u * v / D = v * w / D := by
      field_simp
      dsimp [D]
      ring
    rw [he]
    ring
  have heB : hKleinAffine nB tB z = x * hKleinAffine nB tB T.b := by
    rw [T.kleinAffine_reconstruction, hcoord, hBzA, hBzC]
    ring
  have heC : hKleinAffine nC tC z = y * hKleinAffine nC tC T.c := by
    rw [T.kleinAffine_reconstruction, hcoord, hCzA, hCzB]
    ring
  have heAx : |hKleinAffine nA tA z| = u * v * w / D := by
    rw [heA, abs_mul, abs_of_pos (div_pos (mul_pos hv hw) hD)]
    change v * w / D * u = _
    ring
  have heBx : |hKleinAffine nB tB z| = u * v * w / D := by
    rw [heB, abs_mul, abs_of_pos (div_pos (mul_pos hu hw) hD)]
    change u * w / D * v = _
    ring
  have heCx : |hKleinAffine nC tC z| = u * v * w / D := by
    rw [heC, abs_mul, abs_of_pos (div_pos (mul_pos hu hv) hD)]
    change u * v / D * w = _
    ring
  exact ⟨z,hz,heAx.trans heBx.symm,heBx.trans heCx.symm⟩









/-- A genuine internal point is equidistant from all three actual complete side geodesics. -/
theorem HTriangle.exists_equidistant_side_point (T : HTriangle) :
    ∃ z ∈ T.interior, T.sideLineA.pointDist z = T.sideLineB.pointDist z ∧
      T.sideLineB.pointDist z = T.sideLineC.pointDist z := by
  obtain ⟨z,hz,hab,hbc⟩ := T.exists_equal_absolute_side_equations
    T.sideLineA.incenterNormal T.sideLineB.incenterNormal T.sideLineC.incenterNormal
    T.sideLineA.incenterOffset T.sideLineB.incenterOffset T.sideLineC.incenterOffset
    (fun z => (T.sideLineA.incenter_affine_eq_zero_iff z).symm)
    (fun z => (T.sideLineB.incenter_affine_eq_zero_iff z).symm)
    (fun z => (T.sideLineC.incenter_affine_eq_zero_iff z).symm)
  refine ⟨z,hz,?_,?_⟩
  · apply Real.sinh_injective
    rw [HalfPlaneLine.sinh_pointDist_incenter_affine,HalfPlaneLine.sinh_pointDist_incenter_affine,hab]
  · apply Real.sinh_injective
    rw [HalfPlaneLine.sinh_pointDist_incenter_affine,HalfPlaneLine.sinh_pointDist_incenter_affine,hbc]

/-- The internal equidistant point, whose angle-bisector and tangency properties are proved separately. -/
def HTriangle.incenter (T : HTriangle) : ℍ := T.exists_equidistant_side_point.choose

theorem HTriangle.incenter_mem_interior (T : HTriangle) : T.incenter ∈ T.interior :=
  T.exists_equidistant_side_point.choose_spec.1

theorem HTriangle.incenter_equidistant (T : HTriangle) :
    T.sideLineA.pointDist T.incenter = T.sideLineB.pointDist T.incenter ∧
      T.sideLineB.pointDist T.incenter = T.sideLineC.pointDist T.incenter :=
  T.exists_equidistant_side_point.choose_spec.2



def hNormalizedDirection (z w : ℍ) : ℂ := (hKleinDenominator w)⁻¹ • hyperbolicDirection z w

theorem hNormalizedDirection_re (z w : ℍ) :
    (hNormalizedDirection z w).re = z.im * hKleinAffine ⟨z.re,-1⟩ z.re w := by
  simp only [hNormalizedDirection,Complex.smul_re,hyperbolicDirection,smul_eq_mul]
  have he := verticalLine_incenter_affine z.re w
  change hKleinAffine ⟨z.re,-1⟩ z.re w = _ at he
  rw [he]
  unfold hKleinDenominator
  ring

theorem hNormalizedDirection_im (z w : ℍ) :
    (hNormalizedDirection z w).im =
      hKleinAffine ⟨(-z.re ^ 2 + z.im ^ 2 + 1) / 2,z.re⟩
        (-(z.re ^ 2 - z.im ^ 2 + 1) / 2) w := by
  simp only [hNormalizedDirection,Complex.smul_im,hyperbolicDirection,smul_eq_mul]
  rw [hKleinAffine,halfPlaneKleinCoordinate_explicit,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
  unfold hKleinDenominator
  field_simp
  ring

theorem hNormalizedDirection_self (z : ℍ) : hNormalizedDirection z z = 0 := by
  have he : hyperbolicDirection z z = 0 := by
    apply Complex.ext <;> simp [hyperbolicDirection]
  rw [hNormalizedDirection,he,smul_zero]

/-- Klein-positive barycentric coordinates give a positive tangent-cone combination. -/
theorem HTriangle.normalizedDirection_reconstruction (T : HTriangle) (z : ℍ) :
    hNormalizedDirection T.a z = (T.coordinate z).1 • hNormalizedDirection T.a T.b +
      (T.coordinate z).2 • hNormalizedDirection T.a T.c := by
  have hre : hKleinAffine ⟨T.a.re,-1⟩ T.a.re T.a = 0 := by
    have he := verticalLine_incenter_affine T.a.re T.a
    change hKleinAffine ⟨T.a.re,-1⟩ T.a.re T.a = _ at he
    simpa only [sub_self,mul_zero,zero_div] using he
  have him : hKleinAffine ⟨(-T.a.re ^ 2 + T.a.im ^ 2 + 1) / 2,T.a.re⟩
      (-(T.a.re ^ 2 - T.a.im ^ 2 + 1) / 2) T.a = 0 := by
    rw [← hNormalizedDirection_im,hNormalizedDirection_self,Complex.zero_im]
  apply Complex.ext
  · simp only [Complex.add_re,Complex.smul_re,smul_eq_mul,hNormalizedDirection_re]
    rw [T.kleinAffine_reconstruction,hre]
    ring
  · simp only [Complex.add_im,Complex.smul_im,smul_eq_mul,hNormalizedDirection_im]
    rw [T.kleinAffine_reconstruction,him]
    ring

theorem HTriangle.hyperbolicDirection_interior_combination (T : HTriangle) {z : ℍ}
    (hz : z ∈ T.interior) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ hyperbolicDirection T.a z =
      a • hyperbolicDirection T.a T.b + b • hyperbolicDirection T.a T.c := by
  have hp := T.interior_coordinate hz
  have hDq := hKleinDenominator_pos z
  have hDb := hKleinDenominator_pos T.b
  have hDc := hKleinDenominator_pos T.c
  refine ⟨(T.coordinate z).1 * hKleinDenominator z / hKleinDenominator T.b,
    (T.coordinate z).2 * hKleinDenominator z / hKleinDenominator T.c,
    div_pos (mul_pos hp.1 hDq) hDb,div_pos (mul_pos hp.2.1 hDq) hDc,?_⟩
  have he := congrArg (fun v : ℂ => hKleinDenominator z • v) (T.normalizedDirection_reconstruction z)
  simp only [hNormalizedDirection,smul_add,smul_smul,mul_inv_cancel₀ hDq.ne',one_smul] at he
  simpa only [div_eq_mul_inv,mul_comm,mul_left_comm] using he

def complexCross (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

theorem complex_sin_angle_cross {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    Real.sin (angle u v) = |complexCross u v| / (‖u‖ * ‖v‖) := by
  rw [sin_angle hu hv]
  congr 1
  have h : inner ℝ u u * inner ℝ v v - inner ℝ u v * inner ℝ u v = complexCross u v ^ 2 := by
    simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,complexCross]
    ring
  rw [h,Real.sqrt_sq_eq_abs]

theorem complexCross_smul_left (a : ℝ) (u v : ℂ) : complexCross (a • u) v = a * complexCross u v := by
  simp only [complexCross,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

theorem complexCross_smul_right (a : ℝ) (u v : ℂ) : complexCross u (a • v) = a * complexCross u v := by
  simp only [complexCross,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

theorem complexCross_add_right (u v w : ℂ) : complexCross u (v + w) = complexCross u v + complexCross u w := by
  simp only [complexCross,Complex.add_re,Complex.add_im]
  ring

theorem complexCross_self (u : ℂ) : complexCross u u = 0 := by unfold complexCross; ring

theorem complexCross_comm (u v : ℂ) : complexCross u v = -complexCross v u := by unfold complexCross; ring

/-- Equal perpendicular sine ratios select the internal Euclidean bisector in a positive cone. -/
theorem complex_angle_bisector_of_positive_combination {u v w : ℂ} {a b : ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) (hab : 0 < a ∧ 0 < b)
    (hc : complexCross u v ≠ 0) (he : w = a • u + b • v)
    (hs : Real.sin (angle u w) = Real.sin (angle v w)) : angle u w = angle w v := by
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hcr : 0 < |complexCross u v| := abs_pos.mpr hc
  have hcu : complexCross u w = b * complexCross u v := by
    rw [he,complexCross_add_right,complexCross_smul_right,complexCross_smul_right,complexCross_self]
    ring
  have hcv : complexCross v w = -(a * complexCross u v) := by
    rw [he,complexCross_add_right,complexCross_smul_right,complexCross_smul_right,
      complexCross_self,complexCross_comm v u]
    ring
  rw [complex_sin_angle_cross hu hw,complex_sin_angle_cross hv hw,hcu,hcv,
    abs_neg,abs_mul,abs_mul,abs_of_pos hab.1,abs_of_pos hab.2] at hs
  have hm : a * ‖u‖ = b * ‖v‖ := by
    have hh := (div_eq_div_iff (mul_pos hnu hnw).ne' (mul_pos hnv hnw).ne').mp hs
    have hcancel : a * ‖u‖ * (|complexCross u v| * ‖w‖) =
        b * ‖v‖ * (|complexCross u v| * ‖w‖) := by nlinarith only [hh]
    exact (mul_right_cancel₀ (mul_pos hcr hnw).ne') hcancel
  apply Real.strictAntiOn_cos.injOn ⟨angle_nonneg _ _,angle_le_pi _ _⟩
    ⟨angle_nonneg _ _,angle_le_pi _ _⟩
  rw [cos_angle,cos_angle,real_inner_comm v w]
  apply (div_eq_div_iff (mul_pos hnu hnw).ne' (mul_pos hnw hnv).ne').mpr
  have hiu : inner ℝ u w = a * ‖u‖ ^ 2 + b * inner ℝ u v := by
    rw [he,inner_add_right,inner_smul_right,inner_smul_right,real_inner_self_eq_norm_sq]
  have hiv : inner ℝ v w = a * inner ℝ u v + b * ‖v‖ ^ 2 := by
    rw [he,inner_add_right,inner_smul_right,inner_smul_right,real_inner_comm u v,real_inner_self_eq_norm_sq]
  rw [hiu,hiv]
  nlinarith [congrArg (fun x : ℝ => x * (‖u‖ * ‖v‖ - inner ℝ u v) * ‖w‖) hm]

theorem complexCross_circle_direction (c : ℝ) (z w : ℍ) :
    complexCross (Complex.I * ((z : ℂ) - (c : ℂ))) (hyperbolicDirection z w) =
      -z.im * (‖(w : ℂ) - (c : ℂ)‖ ^ 2 - ‖(z : ℂ) - (c : ℂ)‖ ^ 2) := by
  rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
  simp only [complexCross,hyperbolicDirection,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    sub_zero,zero_mul,one_mul,zero_sub,zero_add,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  ring

/-- Exact perpendicular sine ratio at any vertex on the genuine h-line. -/
theorem HalfPlaneLine.sinh_pointDist_cross_ratio (L : HalfPlaneLine) (z w : ℍ) (hz : z ∈ L.carrier) :
    Real.sinh (L.pointDist w) = |complexCross (L.tangentAt z) (hyperbolicDirection z w)| /
      (‖L.tangentAt z‖ * (2 * z.im * w.im)) := by
  cases L with
  | vertical a =>
    have hza : z.re = a := hz
    rw [verticalLine_pointDist_sinh]
    have he : complexCross ((HalfPlaneLine.vertical a).tangentAt z) (hyperbolicDirection z w) =
        -(2 * z.im * (w.re - a)) := by
      simp only [HalfPlaneLine.tangentAt,complexCross,hyperbolicDirection,Complex.I_re,Complex.I_im,
        zero_mul,one_mul,zero_sub,hza]
    rw [he,abs_neg,abs_mul,abs_mul,abs_of_pos (by positivity : (0 : ℝ) < 2),abs_of_pos z.im_pos]
    simp only [HalfPlaneLine.tangentAt,Complex.norm_I,one_mul]
    field_simp
  | circle c r hr =>
    have hnorm : ‖(HalfPlaneLine.circle c r hr).tangentAt z‖ = r := by
      change ‖Complex.I * ((z : ℂ) - (c : ℂ))‖ = r
      rw [norm_mul,Complex.norm_I,one_mul]
      exact hz
    have hcr : complexCross ((HalfPlaneLine.circle c r hr).tangentAt z) (hyperbolicDirection z w) =
        -z.im * (‖(w : ℂ) - (c : ℂ)‖ ^ 2 - r ^ 2) := by
      rw [HalfPlaneLine.tangentAt,complexCross_circle_direction,hz]
    rw [circleLine_pointDist_sinh,hnorm,hcr,abs_mul,abs_neg,abs_of_pos z.im_pos]
    field_simp

/-- A nonzero real rescaling does not alter the sine of an angle. -/
theorem complex_sin_angle_smul_left (a : ℝ) (u v : ℂ) (ha : a ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    Real.sin (angle (a • u) v) = Real.sin (angle u v) := by
  rw [complex_sin_angle_cross (smul_ne_zero ha hu) hv,complex_sin_angle_cross hu hv,
    complexCross_smul_left,abs_mul,norm_smul,Real.norm_eq_abs]
  field_simp

theorem HRayAt.sinh_pointDist_angle {z : ℍ} (R : HRayAt z) (w : ℍ) (hw : w ≠ z) :
    Real.sinh (R.supportLine.pointDist w) =
      Real.sin (angle R.tangentVector (hyperbolicDirection z w)) * Real.sinh (dist z w) := by
  have hnorm : hyperbolicDirection z w ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hyperbolicDirection_norm]
    exact ne_of_gt (by positivity [dist_pos.mpr hw.symm])
  rw [HRayAt.tangentVector,
    complex_sin_angle_smul_left R.tangentSign _ _ R.tangentSign_ne_zero
      (R.supportLine.tangentAt_ne_zero z) hnorm,
    complex_sin_angle_cross (R.supportLine.tangentAt_ne_zero z) hnorm,
    R.supportLine.sinh_pointDist_cross_ratio z w R.start_mem_support,hyperbolicDirection_norm]
  have hp : 0 < Real.sinh (dist z w) := Real.sinh_pos_iff.mpr (dist_pos.mpr hw.symm)
  field_simp


theorem hyperbolicDirection_ne_zero {z w : ℍ} (hzw : z ≠ w) : hyperbolicDirection z w ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [hyperbolicDirection_norm]
  have hs : 0 < Real.sinh (dist z w) := Real.sinh_pos_iff.mpr (dist_pos.mpr hzw)
  exact ne_of_gt (by positivity)

theorem HRayAt.sinh_pointDist_direction {z : ℍ} (R : HRayAt z) {v : ℍ}
    (hv : v ∈ R.val) (hvz : v ≠ z) (w : ℍ) (hw : w ≠ z) :
    Real.sinh (R.supportLine.pointDist w) =
      Real.sin (angle (hyperbolicDirection z v) (hyperbolicDirection z w)) * Real.sinh (dist z w) := by
  obtain ⟨a,ha,he⟩ := hyperbolicDirection_pos_smul_tangent R hv hvz
  rw [he,angle_smul_left_of_pos _ _ ha]
  exact R.sinh_pointDist_angle w hw

/-- Equal genuine side distances select the internal measured angle bisector at the first vertex. -/
theorem HTriangle.equidistant_bisects_angleA (T : HTriangle) {z : ℍ} (hz : z ∈ T.interior)
    (heq : T.sideLineB.pointDist z = T.sideLineC.pointDist z) :
    angle (hyperbolicDirection T.a T.b) (hyperbolicDirection T.a z) =
      angle (hyperbolicDirection T.a z) (hyperbolicDirection T.a T.c) := by
  have hza : T.a ≠ z := T.a_ne_of_mem_interior hz
  have hsC := T.rayAB.sinh_pointDist_direction T.b_mem_rayAB T.a_ne_b.symm z hza.symm
  have hsB := T.rayAC.sinh_pointDist_direction T.c_mem_rayAC T.c_ne_a z hza.symm
  rw [T.support_AC_eq] at hsB
  change Real.sinh (T.sideLineC.pointDist z) = _ at hsC
  have hs : Real.sin (angle (hyperbolicDirection T.a T.b) (hyperbolicDirection T.a z)) =
      Real.sin (angle (hyperbolicDirection T.a T.c) (hyperbolicDirection T.a z)) := by
    apply mul_right_cancel₀ (ne_of_gt (Real.sinh_pos_iff.mpr (dist_pos.mpr hza)))
    exact hsC.symm.trans ((congrArg Real.sinh heq.symm).trans hsB)
  obtain ⟨a,b,ha,hb,he⟩ := T.hyperbolicDirection_interior_combination hz
  have hc : complexCross (hyperbolicDirection T.a T.b) (hyperbolicDirection T.a T.c) ≠ 0 := by
    have hspos := Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.1.1 T.angles_mem_Ioo.1.2
    have hangle := hInteriorAngleMeasure_eq_direction T.rayAB T.rayAC
      T.b_mem_rayAB T.a_ne_b.symm T.c_mem_rayAC T.c_ne_a
    change T.alpha = _ at hangle
    rw [hangle,complex_sin_angle_cross (hyperbolicDirection_ne_zero T.a_ne_b)
      (hyperbolicDirection_ne_zero T.c_ne_a.symm)] at hspos
    intro hzero
    rw [hzero,abs_zero,zero_div] at hspos
    exact lt_irrefl 0 hspos
  exact complex_angle_bisector_of_positive_combination
    (hyperbolicDirection_ne_zero T.a_ne_b) (hyperbolicDirection_ne_zero T.c_ne_a.symm)
    (hyperbolicDirection_ne_zero hza) ⟨ha,hb⟩ hc he hs

/-- Cyclic relabelling of the actual ordered vertices. -/
def HTriangle.cyclic (T : HTriangle) : HTriangle where
  a := T.b
  b := T.c
  c := T.a
  noncollinear := by
    rintro ⟨L,hb,hc,ha⟩
    exact T.noncollinear ⟨L,ha,hb,hc⟩

theorem HTriangle.cyclic_interior (T : HTriangle) : T.cyclic.interior = T.interior := by
  rw [HTriangle.interior_eq_halfPlanes,HTriangle.interior_eq_halfPlanes]
  change T.halfPlaneB ∩ T.halfPlaneC ∩ T.halfPlaneA = T.halfPlaneA ∩ T.halfPlaneB ∩ T.halfPlaneC
  ext z
  simp only [mem_inter_iff]
  tauto

/-- Concurrency expressed with the actual three forward tangent-angle bisections. -/
theorem HTriangle.incenter_bisects_angles (T : HTriangle) :
    angle (hyperbolicDirection T.a T.b) (hyperbolicDirection T.a T.incenter) =
      angle (hyperbolicDirection T.a T.incenter) (hyperbolicDirection T.a T.c) ∧
    angle (hyperbolicDirection T.b T.c) (hyperbolicDirection T.b T.incenter) =
      angle (hyperbolicDirection T.b T.incenter) (hyperbolicDirection T.b T.a) ∧
    angle (hyperbolicDirection T.c T.a) (hyperbolicDirection T.c T.incenter) =
      angle (hyperbolicDirection T.c T.incenter) (hyperbolicDirection T.c T.b) := by
  refine ⟨T.equidistant_bisects_angleA T.incenter_mem_interior T.incenter_equidistant.2,?_,?_⟩
  · apply T.cyclic.equidistant_bisects_angleA
    · rw [T.cyclic_interior]
      exact T.incenter_mem_interior
    · change T.sideLineC.pointDist T.incenter = T.sideLineA.pointDist T.incenter
      exact (T.incenter_equidistant.1.trans T.incenter_equidistant.2).symm
  · apply T.cyclic.cyclic.equidistant_bisects_angleA
    · rw [T.cyclic.cyclic_interior,T.cyclic_interior]
      exact T.incenter_mem_interior
    · change T.sideLineA.pointDist T.incenter = T.sideLineB.pointDist T.incenter
      exact T.incenter_equidistant.1

end
end LowDimensionalTopology.Geometry.Hyperbolic
