/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PointLineDistance
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HorocyclicRegions

/-!
# Actual point-line distance formulas
-/

@[expose] public section
open Set
open scoped UpperHalfPlane Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

def verticalLineFoot (a : ℝ) (z : ℍ) : ℍ :=
  UpperHalfPlane.mk ⟨a,‖(z : ℂ) - (a : ℂ)‖⟩ (norm_sub_real_pos a z)

theorem verticalLineFoot_orthogonal (a : ℝ) (z : ℍ) :
    (HalfPlaneLine.vertical a).OrthogonalAt
      (.circle a ‖(z : ℂ) - (a : ℂ)‖ (norm_sub_real_pos a z)) (verticalLineFoot a z) := by
  have hpL : verticalLineFoot a z ∈ (HalfPlaneLine.vertical a).carrier := rfl
  have hpM : verticalLineFoot a z ∈
      (HalfPlaneLine.circle a ‖(z : ℂ) - (a : ℂ)‖ (norm_sub_real_pos a z)).carrier := by
    apply norm_sub_real_eq_of_sq (norm_sub_real_pos a z)
    change (a-a) ^ 2 + ‖(z : ℂ) - (a : ℂ)‖ ^ 2 = ‖(z : ℂ) - (a : ℂ)‖ ^ 2
    ring
  exact ((HalfPlaneLine.vertical a).orthogonalAt_iff_coefficients
    (.circle a ‖(z : ℂ) - (a : ℂ)‖ (norm_sub_real_pos a z)) (verticalLineFoot a z) hpL hpM).mpr rfl

theorem verticalLine_pointDist (a : ℝ) (z : ℍ) :
    (HalfPlaneLine.vertical a).pointDist z = dist z (verticalLineFoot a z) :=
  (HalfPlaneLine.vertical a).pointDist_eq_dist_of_perpendicular
    (.circle a ‖(z : ℂ) - (a : ℂ)‖ (norm_sub_real_pos a z)) _ _
    (verticalLineFoot_orthogonal a z) rfl

theorem verticalLine_pointDist_cosh (a : ℝ) (z : ℍ) :
    Real.cosh ((HalfPlaneLine.vertical a).pointDist z) = ‖(z : ℂ) - (a : ℂ)‖ / z.im := by
  have hr := norm_sub_real_pos a z
  have hz := norm_sub_real_eq_radius_sq (show
    z ∈ (HalfPlaneLine.circle a ‖(z : ℂ) - (a : ℂ)‖ hr).carrier from rfl)
  rw [verticalLine_pointDist,UpperHalfPlane.cosh_dist']
  change ((z.re-a) ^ 2 + z.im ^ 2 + ‖(z : ℂ) - (a : ℂ)‖ ^ 2) /
    (2 * z.im * ‖(z : ℂ) - (a : ℂ)‖) = ‖(z : ℂ) - (a : ℂ)‖ / z.im
  field_simp [hr.ne',z.im_ne_zero]
  nlinarith

theorem verticalLine_pointDist_sinh (a : ℝ) (z : ℍ) :
    Real.sinh ((HalfPlaneLine.vertical a).pointDist z) = |z.re-a| / z.im := by
  have hc := Real.cosh_sq_sub_sinh_sq ((HalfPlaneLine.vertical a).pointDist z)
  rw [verticalLine_pointDist_cosh] at hc
  field_simp [z.im_ne_zero] at hc
  have hz := norm_sub_real_eq_radius_sq (show
    z ∈ (HalfPlaneLine.circle a ‖(z : ℂ) - (a : ℂ)‖ (norm_sub_real_pos a z)).carrier from rfl)
  apply (sq_eq_sq₀ (Real.sinh_nonneg_iff.mpr ((HalfPlaneLine.vertical a).pointDist_nonneg z))
    (by positivity)).mp
  rw [div_pow,sq_abs]
  apply (eq_div_iff (pow_ne_zero 2 z.im_ne_zero)).mpr
  nlinarith


theorem norm_sub_real_sq (c : ℝ) (z : ℍ) :
    ‖(z : ℂ) - (c : ℂ)‖ ^ 2 = (z.re-c) ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero]
  change (z.re-c) * (z.re-c) + z.im * z.im = _
  ring

/-- Direct real-coordinate elimination for genuine orthogonal circle configurations. -/
theorem orthogonal_circle_numerator_identity (c d r s zx zy px py : ℝ)
    (ho : (c-d) ^ 2 = r ^ 2 + s ^ 2)
    (hpL : (px-c) ^ 2 + py ^ 2 = r ^ 2)
    (hpM : (px-d) ^ 2 + py ^ 2 = s ^ 2)
    (hzM : (zx-d) ^ 2 + zy ^ 2 = s ^ 2) :
    r ^ 2 * ((zx-px) ^ 2 + zy ^ 2 + py ^ 2) ^ 2 - 4 * r ^ 2 * zy ^ 2 * py ^ 2 =
      py ^ 2 * ((zx-c) ^ 2 + zy ^ 2 - r ^ 2) ^ 2 := by
  have hpR : r ^ 2 = (d-c) * (px-c) := by nlinarith
  have hpy : py ^ 2 = (px-c) * ((d-c)-(px-c)) := by nlinarith [hpL,hpR]
  have hz : (zx-c) ^ 2 + zy ^ 2 + (d-c) * (px-c) = 2 * (d-c) * (zx-c) := by nlinarith
  have hA : (zx-px) ^ 2 + zy ^ 2 + py ^ 2 = 2 * (zx-c) * ((d-c)-(px-c)) := by nlinarith
  have hB : (zx-c) ^ 2 + zy ^ 2 - r ^ 2 = 2 * (d-c) * ((zx-c)-(px-c)) := by nlinarith
  rw [hA,hB,hpR,hpy]
  linear_combination -4 * (d-c) * (px-c) ^ 2 * ((d-c)-(px-c)) * hz

theorem circle_foot_numerator_identity (c r : ℝ) (hr : 0 < r) (M : HalfPlaneLine)
    (p z : ℍ) (hp : (HalfPlaneLine.circle c r hr).OrthogonalAt M p) (hz : z ∈ M.carrier) :
    r ^ 2 * ((z.re-p.re) ^ 2 + z.im ^ 2 + p.im ^ 2) ^ 2 - 4 * r ^ 2 * z.im ^ 2 * p.im ^ 2 =
      p.im ^ 2 * ((z.re-c) ^ 2 + z.im ^ 2 - r ^ 2) ^ 2 := by
  have hc := ((HalfPlaneLine.circle c r hr).orthogonalAt_iff_coefficients M p hp.1 hp.2.1).mp hp
  cases M with
  | vertical d =>
    change c = d at hc
    rw [← hc] at hp hz
    have hp0 : p.re = c := hp.2.1
    have hz0 : z.re = c := hz
    have hpr := norm_sub_real_eq_radius_sq hp.1
    rw [hp0,sub_self,zero_pow (by norm_num : 2 ≠ 0),zero_add] at hpr
    rw [hp0,hz0,sub_self,zero_pow (by norm_num : 2 ≠ 0),zero_add,← hpr]
    ring
  | circle d s hs =>
    exact orthogonal_circle_numerator_identity c d r s z.re z.im p.re p.im hc
      (norm_sub_real_eq_radius_sq hp.1) (norm_sub_real_eq_radius_sq hp.2.1)
      (norm_sub_real_eq_radius_sq hz)

theorem circleLine_pointDist_cosh_sq_sub_one (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    Real.cosh ((HalfPlaneLine.circle c r hr).pointDist z) ^ 2 - 1 =
      ((‖(z : ℂ) - (c : ℂ)‖ ^ 2 - r ^ 2) / (2 * z.im * r)) ^ 2 := by
  obtain ⟨M,⟨hz,⟨p,hp⟩⟩,_⟩ := (HalfPlaneLine.circle c r hr).existsUnique_perpendicular z
  have hn := circle_foot_numerator_identity c r hr M p z hp hz
  rw [(HalfPlaneLine.circle c r hr).pointDist_eq_dist_of_perpendicular M p z hp hz,
    UpperHalfPlane.cosh_dist',norm_sub_real_sq]
  field_simp [hr.ne',z.im_ne_zero,p.im_ne_zero]
  linear_combination hn

theorem circleLine_pointDist_sinh (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    Real.sinh ((HalfPlaneLine.circle c r hr).pointDist z) =
      |‖(z : ℂ) - (c : ℂ)‖ ^ 2 - r ^ 2| / (2 * z.im * r) := by
  have hcore := Real.cosh_sq_sub_sinh_sq ((HalfPlaneLine.circle c r hr).pointDist z)
  have hs := circleLine_pointDist_cosh_sq_sub_one c r hr z
  rw [div_pow] at hs
  apply (sq_eq_sq₀ (Real.sinh_nonneg_iff.mpr ((HalfPlaneLine.circle c r hr).pointDist_nonneg z))
    (by positivity)).mp
  rw [div_pow,sq_abs]
  nlinarith


theorem HalfPlaneLine.toDiscLine_toHalfPlane (L : HalfPlaneLine) : L.toDiscLine.toHalfPlane = L := by
  apply HalfPlaneLine.toDiscLine_injective
  exact L.toDiscLine.toHalfPlane_spec

theorem inverseCayley_re (z : 𝔻) :
    (inverseCayleyFormula z).re = -2 * (z : ℂ).im / ‖1 - (z : ℂ)‖ ^ 2 := by
  rw [inverseCayleyFormula,Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub,
    Complex.div_im,Complex.normSq_eq_norm_sq]
  simp only [Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
    zero_add,zero_sub]
  ring

/-- The actual native disc h-line whose carrier is the real diameter. -/
def realDiameterDiscLine : DiscLine := (HalfPlaneLine.vertical 0).toDiscLine

theorem realDiameterDiscLine_carrier : realDiameterDiscLine.carrier = {z : 𝔻 | (z : ℂ).im = 0} := by
  ext z
  rw [realDiameterDiscLine.mem_carrier]
  change discToHalfPlane z ∈ (HalfPlaneLine.vertical 0).toDiscLine.toHalfPlane.carrier ↔ _
  rw [HalfPlaneLine.toDiscLine_toHalfPlane]
  change (inverseCayleyFormula z).re = 0 ↔ _
  rw [inverseCayley_re]
  have hd : ‖1 - (z : ℂ)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (inverseCayley_denom_ne_zero z))
  rw [div_eq_zero_iff]
  simp only [hd,or_false,mul_eq_zero,neg_eq_zero,OfNat.ofNat_ne_zero,false_or]
  rfl

theorem realDiameterDiscLine_pointDist_sinh (z : 𝔻) :
    Real.sinh (realDiameterDiscLine.pointDist z) = 2 * |(z : ℂ).im| / (1 - ‖(z : ℂ)‖ ^ 2) := by
  rw [realDiameterDiscLine,DiscLine.pointDist_eq_halfPlane,HalfPlaneLine.toDiscLine_toHalfPlane,
    verticalLine_pointDist_sinh]
  change |(inverseCayleyFormula z).re - 0| / (inverseCayleyFormula z).im = _
  rw [sub_zero,inverseCayley_re,inverseCayley_im]
  have hd : 0 < ‖1 - (z : ℂ)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (inverseCayley_denom_ne_zero z))
  have hgap : 0 < 1 - ‖(z : ℂ)‖ ^ 2 := sub_pos.mpr z.sq_norm_lt_one
  rw [abs_div,abs_mul,abs_neg,abs_of_pos (by norm_num : 0 < (2 : ℝ)),abs_of_pos hd]
  field_simp [hd.ne',hgap.ne',norm_ne_zero_iff.mpr (inverseCayley_denom_ne_zero z)]


/-- The actual Euclidean inclination to the positive imaginary direction. -/
def verticalInclination (a : ℝ) (z : ℍ) : ℝ :=
  InnerProductGeometry.angle ((z : ℂ) - (a : ℂ)) Complex.I

theorem verticalInclination_cos (a : ℝ) (z : ℍ) :
    Real.cos (verticalInclination a z) = z.im / ‖(z : ℂ) - (a : ℂ)‖ := by
  rw [verticalInclination,InnerProductGeometry.cos_angle,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,Complex.norm_I,mul_one]
  simp only [Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,Complex.sub_im,Complex.ofReal_im,
    sub_zero,UpperHalfPlane.coe_im]

theorem verticalInclination_sin (a : ℝ) (z : ℍ) :
    Real.sin (verticalInclination a z) = |z.re-a| / ‖(z : ℂ) - (a : ℂ)‖ := by
  have hr := norm_sub_real_pos a z
  have hs := Real.sin_sq_add_cos_sq (verticalInclination a z)
  rw [verticalInclination_cos] at hs
  field_simp [hr.ne'] at hs
  have hn := norm_sub_real_sq a z
  apply (sq_eq_sq₀ (InnerProductGeometry.sin_angle_nonneg _ _) (by positivity)).mp
  change Real.sin (verticalInclination a z) ^ 2 = (|z.re-a| / ‖(z : ℂ) - (a : ℂ)‖) ^ 2
  rw [div_pow,sq_abs]
  apply (eq_div_iff (pow_ne_zero 2 hr.ne')).mpr
  nlinarith

theorem verticalInclination_mem_Ico (a : ℝ) (z : ℍ) :
    verticalInclination a z ∈ Ico (0 : ℝ) (Real.pi / 2) := by
  have ht : verticalInclination a z ∈ Icc (0 : ℝ) Real.pi :=
    ⟨InnerProductGeometry.angle_nonneg _ _,InnerProductGeometry.angle_le_pi _ _⟩
  have hp : Real.pi / 2 ∈ Icc (0 : ℝ) Real.pi := by constructor <;> linarith [Real.pi_pos]
  have hc : 0 < Real.cos (verticalInclination a z) := by
    rw [verticalInclination_cos]
    exact div_pos z.im_pos (norm_sub_real_pos a z)
  refine ⟨ht.1,?_⟩
  apply (Real.strictAntiOn_cos.lt_iff_gt hp ht).mp
  rwa [Real.cos_pi_div_two]

theorem verticalLine_pointDist_cosh_inclination (a : ℝ) (z : ℍ) :
    Real.cosh ((HalfPlaneLine.vertical a).pointDist z) = 1 / Real.cos (verticalInclination a z) := by
  rw [verticalLine_pointDist_cosh,verticalInclination_cos,one_div_div]

theorem verticalLine_pointDist_sinh_inclination (a : ℝ) (z : ℍ) :
    Real.sinh ((HalfPlaneLine.vertical a).pointDist z) = Real.tan (verticalInclination a z) := by
  rw [verticalLine_pointDist_sinh,Real.tan_eq_sin_div_cos,verticalInclination_sin,verticalInclination_cos]
  field_simp [(norm_sub_real_pos a z).ne',z.im_ne_zero]

theorem verticalLine_pointDist_tanh_inclination (a : ℝ) (z : ℍ) :
    Real.tanh ((HalfPlaneLine.vertical a).pointDist z) = Real.sin (verticalInclination a z) := by
  rw [Real.tanh_eq_sinh_div_cosh,verticalLine_pointDist_sinh,verticalLine_pointDist_cosh,verticalInclination_sin]
  field_simp [(norm_sub_real_pos a z).ne',z.im_ne_zero]

theorem verticalInclination_zero_eq_arg (z : ℍ) :
    verticalInclination 0 z = |Complex.arg (z : ℂ) - Real.pi / 2| := by
  have ha : Complex.arg (z : ℂ) ∈ Icc (0 : ℝ) Real.pi :=
    ⟨Complex.arg_nonneg_iff.mpr z.im_pos.le,Complex.arg_le_pi _⟩
  have hb : |Complex.arg (z : ℂ) - Real.pi / 2| ∈ Icc (0 : ℝ) Real.pi := by
    refine ⟨abs_nonneg _,?_⟩
    rw [abs_le]
    constructor <;> linarith [ha.1,ha.2,Real.pi_pos]
  apply Real.strictAntiOn_cos.injOn
    ⟨(verticalInclination_mem_Ico 0 z).1,by linarith [(verticalInclination_mem_Ico 0 z).2,Real.pi_pos]⟩ hb
  rw [Real.cos_abs,Real.cos_sub,Real.cos_pi_div_two,Real.sin_pi_div_two,mul_zero,mul_one,zero_add,
    Complex.sin_arg (z : ℂ),verticalInclination_cos]
  simp only [Complex.ofReal_zero,sub_zero,UpperHalfPlane.coe_im]

end
end LowDimensionalTopology.Geometry.Hyperbolic
