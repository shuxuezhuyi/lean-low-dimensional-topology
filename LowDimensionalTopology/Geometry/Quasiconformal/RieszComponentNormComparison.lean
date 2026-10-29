module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The two real components of a complex Lp function

This is the finite two-component comparison needed for complexification
when p≥2. The components are the actual real and imaginary parts; no
orthogonality is asserted for two arbitrary complex-valued functions.
All norm comparisons remain in the extended nonnegative reals.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem complex_enorm_sq_re_im (z : ℂ) :
    ‖z.re‖ₑ ^ 2 + ‖z.im‖ₑ ^ 2 = ‖z‖ₑ ^ 2 := by
  calc ‖z.re‖ₑ ^ 2 + ‖z.im‖ₑ ^ 2
      = ENNReal.ofReal (‖z.re‖ ^ 2 + ‖z.im‖ ^ 2) := by
        rw [ENNReal.ofReal_add (sq_nonneg ‖z.re‖) (sq_nonneg ‖z.im‖),
          ENNReal.ofReal_pow (norm_nonneg z.re) 2,
          ENNReal.ofReal_pow (norm_nonneg z.im) 2, ofReal_norm, ofReal_norm]
    _ = ENNReal.ofReal (‖z‖ ^ 2) := by
        congr 1
        simp only [Real.norm_eq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply]
        ring
    _ = ‖z‖ₑ ^ 2 := by rw [ENNReal.ofReal_pow (norm_nonneg z) 2, ofReal_norm]

private theorem complex_enorm_rpow_re_im_le {p : ℝ} (hp : 2 ≤ p) (z : ℂ) :
    ‖z.re‖ₑ ^ p + ‖z.im‖ₑ ^ p ≤ ‖z‖ₑ ^ p := by
  have h := ENNReal.add_rpow_le_rpow_add (‖z.re‖ₑ ^ 2) (‖z.im‖ₑ ^ 2)
    (by linarith : (1 : ℝ) ≤ p / 2)
  rw [complex_enorm_sq_re_im z] at h
  simpa only [← ENNReal.rpow_two, ← ENNReal.rpow_mul,
    show (2 : ℝ) * (p / 2) = p by ring] using h

private theorem two_component_rpow_two_le {p : ℝ} (hp : 2 ≤ p) (a b : ℝ≥0∞) :
    a ^ (2 : ℝ) + b ^ (2 : ℝ) ≤
      (2 : ℝ≥0∞) ^ (1 - 2 / p) * (a ^ p + b ^ p) ^ (2 / p) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 ≤ 2 / p := div_nonneg (by norm_num) hp0.le
  have hmean := ENNReal.rpow_add_le_mul_rpow_add_rpow
    (a ^ (2 : ℝ)) (b ^ (2 : ℝ)) (by linarith : (1 : ℝ) ≤ p / 2)
  have h := ENNReal.rpow_le_rpow hmean hq0
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq0] at h
  simpa only [← ENNReal.rpow_mul,
    show (p / 2) * (2 / p) = (1 : ℝ) by field_simp [hp0.ne'],
    show (2 : ℝ) * (p / 2) = p by ring,
    show (p / 2 - 1) * (2 / p) = (1 : ℝ) - 2 / p by field_simp [hp0.ne'],
    ENNReal.rpow_one] using h

/-- The sum of the p-th powers of the two real component norms is at
most the p-th power of the norm of the same complex function. -/
theorem eLpNorm_re_im_rpow_le_complex {φ : ℝ → ℂ} (hφ : Continuous φ)
    {p : ℝ} (hp : 2 ≤ p) :
    eLpNorm (fun x => (φ x).re) (ENNReal.ofReal p) volume ^ p +
        eLpNorm (fun x => (φ x).im) (ENNReal.ofReal p) volume ^ p ≤
      eLpNorm φ (ENNReal.ofReal p) volume ^ p := by
  have hp0 : 0 < p := by linarith
  have hRe : Continuous (fun x => (φ x).re) := Complex.continuous_re.comp hφ
  have hIm : Continuous (fun x => (φ x).im) := Complex.continuous_im.comp hφ
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
      hRe.aestronglyMeasurable,
    eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
      hIm.aestronglyMeasurable,
    eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
      hφ.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp0.le]
  rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp0,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp0,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp0,
    ← lintegral_add_left (hRe.stronglyMeasurable.enorm.pow_const p)]
  exact lintegral_mono fun x => complex_enorm_rpow_re_im_le hp (φ x)

/-- The squared component-norm sum is controlled by the norm of the
same original complex input with the exact two-component factor. -/
theorem eLpNorm_re_im_sq_le_complex {φ : ℝ → ℂ} (hφ : Continuous φ)
    {p : ℝ} (hp : 2 ≤ p) :
    eLpNorm (fun x => (φ x).re) (ENNReal.ofReal p) volume ^ 2 +
        eLpNorm (fun x => (φ x).im) (ENNReal.ofReal p) volume ^ 2 ≤
      (2 : ℝ≥0∞) ^ (1 - 2 / p) * eLpNorm φ (ENNReal.ofReal p) volume ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 ≤ 2 / p := div_nonneg (by norm_num) hp0.le
  have hpow := eLpNorm_re_im_rpow_le_complex hφ hp
  calc eLpNorm (fun x => (φ x).re) (ENNReal.ofReal p) volume ^ 2 +
        eLpNorm (fun x => (φ x).im) (ENNReal.ofReal p) volume ^ 2
      ≤ (2 : ℝ≥0∞) ^ (1 - 2 / p) *
          (eLpNorm (fun x => (φ x).re) (ENNReal.ofReal p) volume ^ p +
            eLpNorm (fun x => (φ x).im) (ENNReal.ofReal p) volume ^ p) ^ (2 / p) := by
        simpa only [ENNReal.rpow_two] using two_component_rpow_two_le hp
          (eLpNorm (fun x => (φ x).re) (ENNReal.ofReal p) volume)
          (eLpNorm (fun x => (φ x).im) (ENNReal.ofReal p) volume)
    _ ≤ (2 : ℝ≥0∞) ^ (1 - 2 / p) *
        (eLpNorm φ (ENNReal.ofReal p) volume ^ p) ^ (2 / p) := by
        gcongr
    _ = (2 : ℝ≥0∞) ^ (1 - 2 / p) * eLpNorm φ (ENNReal.ofReal p) volume ^ 2 := by
        rw [← ENNReal.rpow_mul,
          show p * (2 / p) = (2 : ℝ) by field_simp [hp0.ne'],
          ENNReal.rpow_two]

end LowDimensionalTopology.Geometry.Quasiconformal
