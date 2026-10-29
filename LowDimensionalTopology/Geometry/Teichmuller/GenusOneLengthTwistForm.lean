module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneWeilPeterssonParameter
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The length–twist calculation for the genus-one parameter metric

Differentiating the length and twist functions with the normalization
`gWP = 2 Re hWP` gives `omegaWP = dt ∧ dl`.

The statement below is on the actual complex parameter directions of the
upper half-plane. It identifies the full determinant of the two actual
Fréchet derivatives with `gWP(i u, v)` for the existing parameter tensor.
The geometric interpretation of these functions and their identification
with quotient tangent vectors are not used here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne

/-- The source's genus-one length coordinate, extended to the ambient plane. -/
def parameterLength (z : ℂ) : ℝ := 1 / Real.sqrt z.im

/-- The source's signed genus-one twist coordinate on the same parameter plane. -/
def parameterTwist (z : ℂ) : ℝ := -z.re * parameterLength z

/-- The source's angular parameter, defined from the same length and signed twist. -/
def parameterTwistAngle (z : ℂ) : ℝ := 2 * Real.pi * parameterTwist z / parameterLength z

/-- The actual differentials of the source's length and twist functions have
determinant equal to the fundamental form of the existing parameter metric. -/
theorem parameterTensor_eq_twist_wedge_length (τ : ℍ) (u v : ℂ) :
    parameterTensor τ (Complex.I * u) v =
      fderiv ℝ parameterTwist (τ : ℂ) u * fderiv ℝ parameterLength (τ : ℂ) v -
        fderiv ℝ parameterTwist (τ : ℂ) v * fderiv ℝ parameterLength (τ : ℂ) u := by
  let s := Real.sqrt τ.im
  let k := -(s ^ 2)⁻¹ * (1 / (2 * s))
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr τ.im_pos).ne'
  have hsq : s ^ 2 = τ.im := Real.sq_sqrt τ.im_pos.le
  have hl : HasFDerivAt parameterLength (k • Complex.imCLM) (τ : ℂ) := by
    unfold parameterLength
    simp only [one_div]
    simpa only [Function.comp_def, Complex.imCLM_apply, UpperHalfPlane.coe_im,
      one_div, smul_smul, s, k] using
      (hasDerivAt_inv hs).comp_hasFDerivAt (τ : ℂ)
        (Complex.imCLM.hasFDerivAt.sqrt τ.im_ne_zero)
  have ht : HasFDerivAt parameterTwist
      ((-τ.re) • (k • Complex.imCLM) +
        parameterLength (τ : ℂ) • (-Complex.reCLM)) (τ : ℂ) := by
    exact Complex.reCLM.hasFDerivAt.neg.mul hl
  have hk : (1 / s) * k = -(1 / (2 * τ.im ^ 2)) := by
    calc
      _ = -(1 / (2 * (s ^ 2) ^ 2)) := by
        dsimp only [k]
        field_simp [hs]
      _ = _ := by rw [hsq]
  have hm : parameterTensor τ (Complex.I * u) v =
      (u.re * v.im - u.im * v.re) / (2 * τ.im ^ 2) := by
    rw [parameterTensor_apply, pairing_eq]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    field_simp [τ.im_ne_zero]
    ring
  rw [hm, hl.fderiv, ht.fderiv]
  simp only [add_apply, smul_apply,
    neg_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    smul_eq_mul, parameterLength, UpperHalfPlane.coe_im]
  change (u.re * v.im - u.im * v.re) / (2 * τ.im ^ 2) =
    ((-τ.re) * (k * u.im) + (1 / s) * -u.re) * (k * v.im) -
      ((-τ.re) * (k * v.im) + (1 / s) * -v.re) * (k * u.im)
  calc
    _ = -((1 / s) * k) * (u.re * v.im - u.im * v.re) := by rw [hk]; ring
    _ = _ := by ring

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
