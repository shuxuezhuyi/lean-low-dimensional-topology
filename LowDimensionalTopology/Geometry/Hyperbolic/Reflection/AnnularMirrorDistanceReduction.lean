module

public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.DiscreteTriangleArea
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HalfPlaneLorentzReflections

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

private theorem circle_normalTimeAt_norm (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    (HalfPlaneLine.circle c r hr).normalTimeAt z =
      (r ^ 2 - ‖(z : ℂ) - (c : ℂ)‖ ^ 2) / (2 * r * z.im) := by
  rw [HalfPlaneLine.normalTimeAt_circle, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, UpperHalfPlane.coe_re, Complex.ofReal_re,
    Complex.sub_im, UpperHalfPlane.coe_im, Complex.ofReal_im, sub_zero]
  congr 1; ring

private theorem reflection_I_dist_lt_of_normal_mul_neg (L : HalfPlaneLine) (z : ℍ)
    (hneg : L.normalTimeAt z * L.normalTimeAt UpperHalfPlane.I < 0) :
    dist z (L.reflection UpperHalfPlane.I) < dist z UpperHalfPlane.I := by
  have hc : Real.cosh (dist z (L.reflection UpperHalfPlane.I)) <
      Real.cosh (dist z UpperHalfPlane.I) := by
    have he := LowDimensionalTopology.Geometry.Fuchsian.triangleArea_reflection_cosh
      L z UpperHalfPlane.I
    nlinarith only [he, hneg]
  simpa only [Real.cosh_lt_cosh, abs_of_nonneg dist_nonneg] using hc

/-- Outside the outer mirror, reflecting I strictly decreases the genuine distance. -/
theorem outerCircle_reflection_I_dist_lt (E : ℝ) (hE : 1 < E) {z : ℍ}
    (hz : E < ‖(z : ℂ)‖) :
    dist z ((HalfPlaneLine.circle 0 E (lt_trans zero_lt_one hE)).reflection
      UpperHalfPlane.I) < dist z UpperHalfPlane.I := by
  have hE0 : 0 < E := lt_trans zero_lt_one hE
  have hzsq : E ^ 2 < ‖(z : ℂ)‖ ^ 2 :=
    (sq_lt_sq₀ hE0.le (norm_nonneg _)).mpr hz
  have hzn : (HalfPlaneLine.circle 0 E hE0).normalTimeAt z < 0 := by
    rw [circle_normalTimeAt_norm]
    simp only [Complex.ofReal_zero, sub_zero]
    exact div_neg_of_neg_of_pos (sub_neg.mpr hzsq) (by positivity)
  have hIn : 0 < (HalfPlaneLine.circle 0 E hE0).normalTimeAt UpperHalfPlane.I := by
    rw [circle_normalTimeAt_norm]
    simp only [UpperHalfPlane.coe_I, Complex.ofReal_zero, sub_zero,
      Complex.norm_I, one_pow, UpperHalfPlane.I_im, mul_one]
    exact div_pos (by nlinarith only [hE, sq_nonneg (E - 1)]) (by positivity)
  exact reflection_I_dist_lt_of_normal_mul_neg _ z (mul_neg_of_neg_of_pos hzn hIn)

/-- Inside the small mirror, reflecting I strictly decreases the genuine distance. -/
theorem smallCircle_reflection_I_dist_lt (r x : ℝ) (hr : 0 < r)
    (hsep : 1 + r < x) {z : ℍ} (hz : ‖(z : ℂ) - (x : ℂ)‖ < r) :
    dist z ((HalfPlaneLine.circle x r hr).reflection UpperHalfPlane.I) <
      dist z UpperHalfPlane.I := by
  have hrx : r < x := by linarith only [hsep]
  have hx : 0 < x := lt_trans hr hrx
  have hrx2 : r ^ 2 < x ^ 2 := (sq_lt_sq₀ hr.le hx.le).mpr hrx
  have hzsq : ‖(z : ℂ) - (x : ℂ)‖ ^ 2 < r ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr hz
  have hzn : 0 < (HalfPlaneLine.circle x r hr).normalTimeAt z := by
    rw [circle_normalTimeAt_norm]
    exact div_pos (sub_pos.mpr hzsq) (by positivity)
  have hIn : (HalfPlaneLine.circle x r hr).normalTimeAt UpperHalfPlane.I < 0 := by
    rw [HalfPlaneLine.normalTimeAt_circle]
    simp only [UpperHalfPlane.I_re, UpperHalfPlane.I_im, zero_sub, neg_sq,
      one_pow, mul_one]
    exact div_neg_of_neg_of_pos (by linarith only [hrx2]) (by positivity)
  exact reflection_I_dist_lt_of_normal_mul_neg _ z (mul_neg_of_pos_of_neg hzn hIn)

end LowDimensionalTopology.Geometry.Hyperbolic
