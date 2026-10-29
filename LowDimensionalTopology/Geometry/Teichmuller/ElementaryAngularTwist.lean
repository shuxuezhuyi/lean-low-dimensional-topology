module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistInfinitesimal
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Ring

/-!
# Literal elementary half-plane twist formulas

The elementary map has three angular pieces. Its coefficient formula has
positive dilation invariance, a negative sign in epsilon and a closed middle
angular interval.

This module defines the literal map on the actual upper half-plane and
matches the existing coefficient curve to the rational expression.
It makes no quasiconformality, derivative-of-the-spatial-map, collar descent,
automorphic-sum or global FN deformation assertion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- The source's signed angular shear parameter. -/
def shear (θ : Width) (t : ℝ) : ℝ := -t / (2 * (θ : ℝ))

open scoped Classical in
/-- The literal three-piece map, with both boundary rays in the middle piece. -/
def elementaryMap (θ : Width) (t : ℝ) (z : ℍ) : ℍ :=
  if Complex.arg (z : ℂ) < Real.pi / 2 - (θ : ℝ) then z
  else if Complex.arg (z : ℂ) ≤ Real.pi / 2 + (θ : ℝ) then
    (⟨Real.exp (shear θ t * (Complex.arg (z : ℂ) - Real.pi / 2 + (θ : ℝ))),
      Real.exp_pos _⟩ : {r : ℝ // 0 < r}) • z
  else (⟨Real.exp (-t), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) • z

open scoped Classical in
/-- Its plane values are precisely the displayed source formula. -/
theorem coe_elementaryMap (θ : Width) (t : ℝ) (z : ℍ) :
    (elementaryMap θ t z : ℂ) =
      if Complex.arg (z : ℂ) < Real.pi / 2 - (θ : ℝ) then (z : ℂ)
      else if Complex.arg (z : ℂ) ≤ Real.pi / 2 + (θ : ℝ) then
        (z : ℂ) * (Real.exp
          (shear θ t * (Complex.arg (z : ℂ) - Real.pi / 2 + (θ : ℝ))) : ℂ)
      else (z : ℂ) * (Real.exp (-t) : ℂ) := by
  classical
  by_cases hlo : Complex.arg (z : ℂ) < Real.pi / 2 - (θ : ℝ)
  · simp only [elementaryMap, ite_eq_left hlo]
  · by_cases hup : Complex.arg (z : ℂ) ≤ Real.pi / 2 + (θ : ℝ)
    · simp only [elementaryMap, ite_eq_right hlo, ite_eq_left hup,
        UpperHalfPlane.coe_pos_real_smul, Complex.real_smul, mul_comm]
    · simp only [elementaryMap, ite_eq_right hlo, ite_eq_right hup,
        UpperHalfPlane.coe_pos_real_smul, Complex.real_smul, mul_comm]

open scoped Classical in
/-- The existing rational curve has exactly the source's epsilon-factor and
closed-interval coefficient representative. No spatial derivative is asserted. -/
theorem coefficientCurve_eq_source (θ : Width) (t : ℝ) (z : ℍ) :
    coefficientCurve θ t z =
      if Complex.arg (z : ℂ) ∈ interval θ then
        (Complex.I * (shear θ t : ℂ)) / (2 - Complex.I * (shear θ t : ℂ)) *
          ((z : ℂ) / conj (z : ℂ)) else 0 := by
  classical
  have hscale : Complex.I * (shear θ t : ℂ) =
      2 * ((t : ℂ) * infinitesimalScale θ) := by
    simp only [shear, infinitesimalScale, Complex.ofReal_neg,
      Complex.ofReal_mul, Complex.ofReal_ofNat, div_eq_mul_inv, mul_inv_rev,
      Complex.ofReal_inv]
    ring
  by_cases hz : Complex.arg (z : ℂ) ∈ interval θ
  · simp only [coefficientCurve, ite_eq_left hz]
    rw [hscale]
    have hden : (2 : ℂ) - 2 * ((t : ℂ) * infinitesimalScale θ) =
        2 * (1 - (t : ℂ) * infinitesimalScale θ) := by ring
    rw [hden, mul_div_mul_left _ _ (by norm_num : (2 : ℂ) ≠ 0)]
  · simp only [coefficientCurve, ite_eq_right hz]

/-- Positive real dilation preserves the same explicit coefficient on all of H. -/
theorem coefficientCurve_pos_real_smul (θ : Width) (t : ℝ)
    (r : {r : ℝ // 0 < r}) (z : ℍ) :
    coefficientCurve θ t (r • z) = coefficientCurve θ t z := by
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
  simp only [coefficientCurve, harg, hphase]

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
