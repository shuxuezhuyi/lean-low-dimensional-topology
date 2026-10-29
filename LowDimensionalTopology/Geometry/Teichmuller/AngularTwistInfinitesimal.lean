module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Tactic.NormNum

/-! The elementary angular-strip infinitesimal coefficient and its real parameter curve.
The curve is an explicit coefficient formula; no quasiconformal-map claim is made. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- The closed angular interval determining the coefficient representative. -/
def interval (θ : Width) : Set ℝ :=
  Set.Icc (Real.pi / 2 - (θ : ℝ)) (Real.pi / 2 + (θ : ℝ))

/-- Constant factor of the elementary infinitesimal coefficient. -/
def infinitesimalScale (θ : Width) : ℂ :=
  -Complex.I / ((4 * (θ : ℝ) : ℝ) : ℂ)

open scoped Classical in
/-- The elementary infinitesimal coefficient, on the full upper half-plane. -/
def infinitesimal (θ : Width) (z : ℍ) : ℂ :=
  if Complex.arg (z : ℂ) ∈ interval θ then
    infinitesimalScale θ * ((z : ℂ) / conj (z : ℂ)) else 0

open scoped Classical in
/-- An explicit rational real-parameter coefficient curve with the same angular support. -/
def coefficientCurve (θ : Width) (t : ℝ) (z : ℍ) : ℂ :=
  if Complex.arg (z : ℂ) ∈ interval θ then
    ((t : ℂ) * infinitesimalScale θ) / (1 - (t : ℂ) * infinitesimalScale θ) *
      ((z : ℂ) / conj (z : ℂ)) else 0

/-- The elementary coefficient is the actual pointwise real parameter derivative at zero. -/
theorem hasDerivAt_coefficientCurve_zero (θ : Width) (z : ℍ) :
    HasDerivAt (fun t : ℝ => coefficientCurve θ t z) (infinitesimal θ z) 0 := by
  classical
  by_cases hz : Complex.arg (z : ℂ) ∈ interval θ
  · have hu : HasDerivAt (fun t : ℝ => (t : ℂ) * infinitesimalScale θ)
        (infinitesimalScale θ) 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const
        (infinitesimalScale θ)
    have hden : HasDerivAt (fun t : ℝ => (1 : ℂ) - (t : ℂ) * infinitesimalScale θ)
        (-infinitesimalScale θ) 0 := HasDerivAt.const_sub (1 : ℂ) hu
    have hq := hu.fun_div hden (by simp)
    simpa [coefficientCurve, infinitesimal, hz] using
      hq.mul_const ((z : ℂ) / conj (z : ℂ))
  · simpa [coefficientCurve, infinitesimal, hz] using
      (hasDerivAt_const (0 : ℝ) (0 : ℂ))

open scoped Classical in
/-- The exact magnitude is constant on the angular strip and zero outside it. -/
theorem norm_infinitesimal (θ : Width) (z : ℍ) :
    ‖infinitesimal θ z‖ =
      if Complex.arg (z : ℂ) ∈ interval θ then 1 / (4 * (θ : ℝ)) else 0 := by
  have hθ : 0 < 4 * (θ : ℝ) := mul_pos (by norm_num) θ.property.1
  have hphase : ‖(z : ℂ) / conj (z : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr z.ne_zero)]
  by_cases hz : Complex.arg (z : ℂ) ∈ interval θ
  · simp only [infinitesimal, ite_eq_left hz, norm_mul, hphase, mul_one]
    simp only [infinitesimalScale, norm_div, norm_neg, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ]
  · simp [infinitesimal, hz]

/-- A uniform bound suitable for the later infinitesimal Beltrami construction. -/
theorem norm_infinitesimal_le (θ : Width) (z : ℍ) :
    ‖infinitesimal θ z‖ ≤ 1 / (4 * (θ : ℝ)) := by
  classical
  rw [norm_infinitesimal]
  by_cases hz : Complex.arg (z : ℂ) ∈ interval θ
  · simp only [ite_eq_left hz, le_refl]
  · rw [ite_eq_right hz]
    exact le_of_lt (one_div_pos.mpr (mul_pos (by norm_num) θ.property.1))

/-- Positive real dilation preserves this coefficient on the full upper half-plane. -/
theorem infinitesimal_pos_real_smul (θ : Width) (r : {r : ℝ // 0 < r}) (z : ℍ) :
    infinitesimal θ (r • z) = infinitesimal θ z := by
  classical
  have harg : Complex.arg ((r • z : ℍ) : ℂ) = Complex.arg (z : ℂ) := by
    rw [UpperHalfPlane.coe_pos_real_smul, Complex.real_smul]
    exact Complex.arg_real_mul _ r.property
  have hr : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr r.property.ne'
  have hphase : ((r • z : ℍ) : ℂ) / conj ((r • z : ℍ) : ℂ) =
      (z : ℂ) / conj (z : ℂ) := by
    simp only [UpperHalfPlane.coe_pos_real_smul, Complex.real_smul,
      map_mul, Complex.conj_ofReal]
    exact mul_div_mul_left _ _ hr
  simp only [infinitesimal, harg, hphase]

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
