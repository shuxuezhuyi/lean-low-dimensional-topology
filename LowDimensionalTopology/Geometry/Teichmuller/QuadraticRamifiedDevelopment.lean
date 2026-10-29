module

public import LowDimensionalTopology.External.LiZhongQC.Ch07.S25_QuadraticDifferentials
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Flat development at a finite-order quadratic zero

The variable `u` is a coordinate in the logarithm plane, with ordinary
coordinate `z = exp u`. The angular coordinate is retained before projection
to the complex plane. The projected flat development is not asserted to be
globally injective. Rescaling the existing analytic normal coordinate gives
the coefficient-one normal form and the precise primitive factor.

The analytic normal-form producer is reused from Wu Xiaobin's LiZhongQC
development, under Apache-2.0; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Filter Topology

namespace LowDimensionalTopology.Geometry.Teichmuller

/-- Half the positive integer `m + 2`, regarded as a complex scalar. -/
def quadraticZeroExponent (m : ℕ) : ℂ := ((m + 2 : ℕ) : ℂ) / 2

private theorem quadraticZeroExponent_ne_zero (m : ℕ) : quadraticZeroExponent m ≠ 0 := by
  exact div_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (m + 1))) two_ne_zero

/-- The primitive of `z^m dz²` on the logarithm plane `z = exp u`. -/
def quadraticZeroDevelopment (m : ℕ) (u : ℂ) : ℂ :=
  (quadraticZeroExponent m)⁻¹ * Complex.exp (quadraticZeroExponent m * u)

/-- The target logarithm keeps the angle before the exponential projection. -/
def quadraticZeroLogDevelopment (m : ℕ) (u : ℂ) : ℂ :=
  (Real.log (2 / ((m + 2 : ℕ) : ℝ)) : ℂ) + quadraticZeroExponent m * u

/-- The explicit primitive factor is exactly `2 / (m + 2)`. -/
theorem quadraticZeroDevelopment_eq_formula (m : ℕ) (u : ℂ) :
    quadraticZeroDevelopment m u = (2 / ((m + 2 : ℕ) : ℂ)) *
      Complex.exp (quadraticZeroExponent m * u) := by
  simp only [quadraticZeroDevelopment, quadraticZeroExponent, inv_div]

/-- Exponentiating the retained target logarithm gives the actual flat development. -/
theorem exp_quadraticZeroLogDevelopment (m : ℕ) (u : ℂ) :
    Complex.exp (quadraticZeroLogDevelopment m u) = quadraticZeroDevelopment m u := by
  let a : ℝ := 2 / ((m + 2 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have he : Complex.exp (Real.log a : ℂ) = (a : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log ha]
  change Complex.exp ((Real.log a : ℂ) + quadraticZeroExponent m * u) = _
  rw [Complex.exp_add, he]
  have hcast : (a : ℂ) = 2 / ((m + 2 : ℕ) : ℂ) := by
    simp only [a, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_natCast]
  rw [hcast]
  exact (quadraticZeroDevelopment_eq_formula m u).symm

/-- The primitive derivative is taken with respect to the actual log variable. -/
theorem hasDerivAt_quadraticZeroDevelopment (m : ℕ) (u : ℂ) :
    HasDerivAt (quadraticZeroDevelopment m)
      (Complex.exp (quadraticZeroExponent m * u)) u := by
  let c := quadraticZeroExponent m
  have hc : c ≠ 0 := quadraticZeroExponent_ne_zero m
  have h := (((hasDerivAt_id u).const_mul c).cexp).const_mul c⁻¹
  have hcoeff : c⁻¹ * (Complex.exp (c * u) * (c * 1)) = Complex.exp (c * u) := by
    calc
      c⁻¹ * (Complex.exp (c * u) * (c * 1)) = (c⁻¹ * c) * Complex.exp (c * u) := by ring
      _ = Complex.exp (c * u) := by rw [inv_mul_cancel₀ hc, one_mul]
  dsimp only [id] at h
  rw [hcoeff] at h
  exact h

/-- Pulling the quadratic differential back by `z = exp u` gives this derivative square. -/
theorem quadraticZeroDevelopment_deriv_sq (m : ℕ) (u : ℂ) :
    deriv (quadraticZeroDevelopment m) u ^ 2 = Complex.exp u ^ m * Complex.exp u ^ 2 := by
  rw [(hasDerivAt_quadraticZeroDevelopment m u).deriv]
  calc
    Complex.exp (quadraticZeroExponent m * u) ^ 2 =
        Complex.exp (2 * (quadraticZeroExponent m * u)) := (Complex.exp_nat_mul _ 2).symm
    _ = Complex.exp (((m + 2 : ℕ) : ℂ) * u) := by
      congr 1
      dsimp [quadraticZeroExponent]
      ring
    _ = Complex.exp u ^ (m + 2) := Complex.exp_nat_mul u (m + 2)
    _ = Complex.exp u ^ m * Complex.exp u ^ 2 := pow_add _ _ _

/-- A full turn of the ordinary coordinate changes the development by `(-1)^m`. -/
theorem quadraticZeroDevelopment_monodromy (m : ℕ) (u : ℂ) :
    quadraticZeroDevelopment m (u + 2 * (Real.pi : ℂ) * Complex.I) =
      (-1 : ℂ) ^ m * quadraticZeroDevelopment m u := by
  have hphase : Complex.exp (quadraticZeroExponent m * (2 * (Real.pi : ℂ) * Complex.I)) =
      (-1 : ℂ) ^ m := by
    calc
      Complex.exp (quadraticZeroExponent m * (2 * (Real.pi : ℂ) * Complex.I)) =
          Complex.exp (((m + 2 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
        congr 1
        dsimp [quadraticZeroExponent]
        ring
      _ = Complex.exp ((Real.pi : ℂ) * Complex.I) ^ (m + 2) := Complex.exp_nat_mul _ _
      _ = (-1 : ℂ) ^ (m + 2) := by rw [Complex.exp_pi_mul_I]
      _ = (-1 : ℂ) ^ m := by rw [pow_add]; norm_num
  simp only [quadraticZeroDevelopment, mul_add, Complex.exp_add, hphase]
  ring

/-- The logarithmic target map is injective; this does not assert injectivity of its projection. -/
theorem quadraticZeroLogDevelopment_injective (m : ℕ) :
    Function.Injective (quadraticZeroLogDevelopment m) := by
  intro u v huv
  apply mul_left_cancel₀ (quadraticZeroExponent_ne_zero m)
  change (Real.log (2 / ((m + 2 : ℕ) : ℝ)) : ℂ) + quadraticZeroExponent m * u =
    (Real.log (2 / ((m + 2 : ℕ) : ℝ)) : ℂ) + quadraticZeroExponent m * v at huv
  exact add_left_cancel huv

/-- The range describes an unwrapped angle, rather than the principal argument of the projection. -/
theorem quadraticZeroLogDevelopment_angle (m : ℕ) (u : ℂ)
    (hu : 0 < u.im ∧ u.im < 2 * Real.pi) :
    0 < (quadraticZeroLogDevelopment m u).im ∧
      (quadraticZeroLogDevelopment m u).im < ((m + 2 : ℕ) : ℝ) * Real.pi := by
  have him : (quadraticZeroLogDevelopment m u).im = ((m + 2 : ℕ) : ℝ) / 2 * u.im := by
    simp [quadraticZeroLogDevelopment, quadraticZeroExponent, Complex.mul_im]
  rw [him]
  have hc : 0 < ((m + 2 : ℕ) : ℝ) / 2 := by positivity
  refine ⟨mul_pos hc hu.1, ?_⟩
  calc
    ((m + 2 : ℕ) : ℝ) / 2 * u.im < ((m + 2 : ℕ) : ℝ) / 2 * (2 * Real.pi) :=
      mul_lt_mul_of_pos_left hu.2 hc
    _ = ((m + 2 : ℕ) : ℝ) * Real.pi := by ring

/-- The nonzero constant rescales the existing analytic normal coordinate. -/
def quadraticZeroScaling (m : ℕ) : ℂ :=
  Complex.exp (Complex.log (quadraticZeroExponent m) / quadraticZeroExponent m)

theorem quadraticZeroScaling_ne_zero (m : ℕ) : quadraticZeroScaling m ≠ 0 :=
  Complex.exp_ne_zero _

theorem quadraticZeroScaling_pow (m : ℕ) :
    quadraticZeroScaling m ^ (m + 2) = quadraticZeroExponent m ^ 2 := by
  let c := quadraticZeroExponent m
  have hc : c ≠ 0 := quadraticZeroExponent_ne_zero m
  have hN : ((m + 2 : ℕ) : ℂ) = 2 * c := by dsimp [c, quadraticZeroExponent]; ring
  have hcancel : c * (Complex.log c / c) = Complex.log c :=
    (mul_comm _ _).trans (div_mul_cancel₀ _ hc)
  change Complex.exp (Complex.log c / c) ^ (m + 2) = c ^ 2
  calc
    Complex.exp (Complex.log c / c) ^ (m + 2) =
        Complex.exp (((m + 2 : ℕ) : ℂ) * (Complex.log c / c)) :=
      (Complex.exp_nat_mul _ _).symm
    _ = Complex.exp (2 * Complex.log c) := by rw [hN, mul_assoc, hcancel]
    _ = Complex.exp (Complex.log c) ^ 2 := Complex.exp_nat_mul _ 2
    _ = c ^ 2 := by rw [Complex.exp_log hc]

/-- The actual logarithmic coordinate change matches the primitive of the existing normal form. -/
theorem quadraticZeroDevelopment_rescaled (m : ℕ) (u : ℂ) :
    quadraticZeroDevelopment m
        (u + Complex.log (quadraticZeroExponent m) / quadraticZeroExponent m) =
      Complex.exp (quadraticZeroExponent m * u) := by
  let c := quadraticZeroExponent m
  have hc : c ≠ 0 := quadraticZeroExponent_ne_zero m
  have hcancel : c * (Complex.log c / c) = Complex.log c :=
    (mul_comm _ _).trans (div_mul_cancel₀ _ hc)
  change c⁻¹ * Complex.exp (c * (u + Complex.log c / c)) = Complex.exp (c * u)
  rw [mul_add, hcancel, Complex.exp_add, Complex.exp_log hc]
  calc
    c⁻¹ * (Complex.exp (c * u) * c) = (c⁻¹ * c) * Complex.exp (c * u) := by ring
    _ = Complex.exp (c * u) := by rw [inv_mul_cancel₀ hc, one_mul]

/-- Rescale the existing normal-form coordinate without changing the given coefficient. -/
theorem rescale_quadratic_normal_coordinate {φ w : ℂ → ℂ} {z₀ : ℂ} (m : ℕ)
    (hw : AnalyticAt ℂ w z₀) (hw0 : w z₀ = 0) (hwd : deriv w z₀ ≠ 0)
    (hφ : ∀ᶠ z in 𝓝 z₀,
      φ z = quadraticZeroExponent m ^ 2 * w z ^ m * deriv w z ^ 2) :
    ∃ z : ℂ → ℂ, AnalyticAt ℂ z z₀ ∧ z z₀ = 0 ∧ deriv z z₀ ≠ 0 ∧
      ∀ᶠ t in 𝓝 z₀, φ t = z t ^ m * deriv z t ^ 2 := by
  let a := quadraticZeroScaling m
  let z : ℂ → ℂ := fun t => a * w t
  have ha : a ≠ 0 := quadraticZeroScaling_ne_zero m
  have hz : AnalyticAt ℂ z z₀ := analyticAt_const.mul hw
  have hzd : deriv z z₀ = a * deriv w z₀ := (hw.differentiableAt.hasDerivAt.const_mul a).deriv
  refine ⟨z, hz, ?_, ?_, ?_⟩
  · simp only [z, hw0, mul_zero]
  · rw [hzd]
    exact mul_ne_zero ha hwd
  · filter_upwards [hφ, hw.eventually_analyticAt] with t ht hwt
    have hzdt : deriv z t = a * deriv w t := (hwt.differentiableAt.hasDerivAt.const_mul a).deriv
    have hpower : a ^ (m + 2) = quadraticZeroExponent m ^ 2 := quadraticZeroScaling_pow m
    rw [ht, hzdt, ← hpower]
    change a ^ (m + 2) * w t ^ m * deriv w t ^ 2 = (a * w t) ^ m * (a * deriv w t) ^ 2
    rw [pow_add, mul_pow, mul_pow]
    ring

/-- The actual finite-order-zero existence theorem supplies the normal coordinate used here. -/
theorem exists_quadratic_zero_normal_coordinate {φ : ℂ → ℂ} {z₀ : ℂ} {m : ℕ}
    (hm : 0 < m) {ψ : ℂ → ℂ} (hψ : AnalyticAt ℂ ψ z₀) (hψ0 : ψ z₀ ≠ 0)
    (hφ : ∀ᶠ z in 𝓝 z₀, φ z = (z - z₀) ^ m * ψ z) :
    ∃ z : ℂ → ℂ, AnalyticAt ℂ z z₀ ∧ z z₀ = 0 ∧ deriv z z₀ ≠ 0 ∧
      ∀ᶠ t in 𝓝 z₀, φ t = z t ^ m * deriv z t ^ 2 := by
  obtain ⟨w, hw, hw0, hwd, hφw⟩ := LiZhongQC.eq25_5_natural_parameter_zero hm hψ hψ0 hφ
  apply rescale_quadratic_normal_coordinate m hw hw0 hwd
  simpa only [quadraticZeroExponent, Nat.cast_add, Nat.cast_ofNat] using hφw

end LowDimensionalTopology.Geometry.Teichmuller
