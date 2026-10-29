module

public import LowDimensionalTopology.Geometry.Quasiconformal.RealDirectionalHilbert
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Pairing opposite directions in a full angular integral

Translation of the second half-circle changes both the direction and its
complex weight by a minus sign, producing the opposite-ray difference.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem exp_angle_add_pi (θ : ℝ) :
    Complex.exp (((θ + Real.pi : ℝ) : ℂ) * I) =
      -Complex.exp ((θ : ℂ) * I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

private theorem exp_neg_angle_add_pi (θ : ℝ) :
    Complex.exp (-(((θ + Real.pi : ℝ) : ℂ) * I)) =
      -Complex.exp (-((θ : ℂ) * I)) := by
  rw [Complex.exp_neg, exp_angle_add_pi, inv_neg, ← Complex.exp_neg]

/-- The full angular integral is the exact positive-minus-negative ray integral. -/
theorem circular_angular_integral_eq_paired {φ : ℂ → ℂ}
    (hφ : Continuous φ) (ζ : ℂ) (r : ℝ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      φ ((r : ℂ) * Complex.exp ((θ : ℂ) * I) + ζ) *
        Complex.exp (-((θ : ℂ) * I))) =
      ∫ θ in (0 : ℝ)..Real.pi,
        (φ ((r : ℂ) * Complex.exp ((θ : ℂ) * I) + ζ) -
          φ (((-r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I) + ζ)) *
            Complex.exp (-((θ : ℂ) * I)) := by
  let g : ℝ → ℂ := fun θ =>
    φ ((r : ℂ) * Complex.exp ((θ : ℂ) * I) + ζ) * Complex.exp (-((θ : ℂ) * I))
  let gm : ℝ → ℂ := fun θ =>
    φ (((-r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I) + ζ) * Complex.exp (-((θ : ℂ) * I))
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hgm : Continuous gm := by dsimp [gm]; fun_prop
  have hshift : (∫ θ in Real.pi..2 * Real.pi, g θ) =
      -(∫ θ in (0 : ℝ)..Real.pi, gm θ) := by
    have htr := intervalIntegral.integral_comp_add_right
      (a := (0 : ℝ)) (b := Real.pi) g Real.pi
    rw [zero_add, show Real.pi + Real.pi = 2 * Real.pi by ring] at htr
    rw [← htr]
    calc
      (∫ θ in (0 : ℝ)..Real.pi, g (θ + Real.pi)) =
          ∫ θ in (0 : ℝ)..Real.pi, -gm θ := by
        apply intervalIntegral.integral_congr
        intro θ _
        dsimp only [g, gm]
        rw [exp_angle_add_pi, exp_neg_angle_add_pi]
        simp only [Complex.ofReal_neg, mul_neg, neg_mul]
      _ = -(∫ θ in (0 : ℝ)..Real.pi, gm θ) := intervalIntegral.integral_neg
  calc
    (∫ θ in (0 : ℝ)..2 * Real.pi, g θ) =
        (∫ θ in (0 : ℝ)..Real.pi, g θ) + (∫ θ in Real.pi..2 * Real.pi, g θ) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hg.intervalIntegrable (μ := volume) 0 Real.pi)
        (hg.intervalIntegrable (μ := volume) Real.pi (2 * Real.pi))).symm
    _ = (∫ θ in (0 : ℝ)..Real.pi, g θ) - (∫ θ in (0 : ℝ)..Real.pi, gm θ) := by
      rw [hshift, sub_eq_add_neg]
    _ = ∫ θ in (0 : ℝ)..Real.pi, g θ - gm θ :=
      (intervalIntegral.integral_sub (hg.intervalIntegrable (μ := volume) 0 Real.pi)
        (hgm.intervalIntegrable (μ := volume) 0 Real.pi)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp [g, gm]
      ring


/-- A positive radial truncation is genuinely absolutely integrable for every
compact continuous planar test. -/
theorem integrableOn_circularHilbertRadialKernel {φ : ℂ → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (ζ : ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun z : ℂ => φ (z + ζ) / (z * (‖z‖ : ℂ)))
      {z : ℂ | ε < ‖z‖} (volume : Measure ℂ) := by
  have hi : Integrable (fun z : ℂ => φ (z + ζ)) (volume : Measure ℂ) := by
    simpa only [add_comm] using
      (hφ.integrable_of_hasCompactSupport hc).comp_add_left ζ
  refine ((hi.norm.const_mul (1 / ε ^ 2)).integrableOn).mono' ?_ ?_
  · exact (((hφ.measurable.comp (measurable_id.add_const ζ)).div
      (measurable_id.mul (Complex.continuous_ofReal.measurable.comp
        measurable_norm))).aestronglyMeasurable).restrict
  · filter_upwards [self_mem_ae_restrict
      ((isOpen_lt continuous_const continuous_norm).measurableSet)] with z hz
    change ‖φ (z + ζ) / (z * (‖z‖ : ℂ))‖ ≤ (1 / ε ^ 2) * ‖φ (z + ζ)‖
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg z)]
    have hs : ε ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    calc
      ‖φ (z + ζ)‖ / (‖z‖ * ‖z‖) = ‖φ (z + ζ)‖ / ‖z‖ ^ 2 := by rw [pow_two]
      _ ≤ ‖φ (z + ζ)‖ / ε ^ 2 :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hs
      _ = (1 / ε ^ 2) * ‖φ (z + ζ)‖ := by ring

end LowDimensionalTopology.Geometry.Quasiconformal
