module

public import LowDimensionalTopology.Geometry.Teichmuller.SmoothBeltrami
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The literal metric Beltrami coefficient of a pulled-back complex inner product

The coefficient is computed from the actual real Gram entries E, F, G. The
positive-Jacobian branch recovers the ratio of the two Wirtinger coefficients;
neither a conformal metric nor a prescribed coefficient is assumed as data.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller

/-- The original coefficient of E dx² + 2 F dx dy + G dy², with the positive
square root of its Gram determinant. -/
def metricBeltramiFromGram (E F G : ℝ) : ℂ :=
  (((E - G : ℝ) : ℂ) + 2 * Complex.I * (F : ℂ)) /
    ((E + G + 2 * Real.sqrt (E * G - F ^ 2) : ℝ) : ℂ)

/-- A positive multiple of the actual inner-product pullback by
z ↦ a z + b conjugate(z) has exactly the coefficient b/a. Orientation is the
strict inequality between the two actual Wirtinger factors. -/
theorem metricBeltramiFromGram_of_wirtinger
    (scale : ℝ) (a b : ℂ) (hscale : 0 < scale) (hba : ‖b‖ < ‖a‖) :
    metricBeltramiFromGram
      (scale * ‖a + b‖ ^ 2)
      (scale * ⟪a + b, a * Complex.I - b * Complex.I⟫_ℝ)
      (scale * ‖a * Complex.I - b * Complex.I‖ ^ 2) = b / a := by
  let E : ℝ := scale * ‖a + b‖ ^ 2
  let F : ℝ := scale * ⟪a + b, a * Complex.I - b * Complex.I⟫_ℝ
  let G : ℝ := scale * ‖a * Complex.I - b * Complex.I‖ ^ 2
  let D : ℝ := ‖a‖ ^ 2 - ‖b‖ ^ 2
  have hD : 0 < D := by
    dsimp only [D]
    nlinarith [norm_nonneg a, norm_nonneg b]
  have hGram : E * G - F ^ 2 = (scale * D) ^ 2 := by
    dsimp only [E, F, G, D]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.inner,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.I_re, Complex.I_im]
    ring
  have hsqrt : Real.sqrt (E * G - F ^ 2) = scale * D := by
    rw [hGram, Real.sqrt_sq (mul_nonneg hscale.le hD.le)]
  have hnum : (((E - G : ℝ) : ℂ) + 2 * Complex.I * (F : ℂ)) =
      4 * (scale : ℂ) * conj a * b := by
    apply Complex.ext <;>
      simp [E, F, G, Complex.sq_norm, Complex.normSq_apply, Complex.inner,
        Complex.mul_re, Complex.mul_im] <;> ring
  have hden : ((E + G + 2 * Real.sqrt (E * G - F ^ 2) : ℝ) : ℂ) =
      4 * (scale : ℂ) * conj a * a := by
    rw [hsqrt]
    apply Complex.ext <;>
      simp [E, G, D, Complex.sq_norm, Complex.normSq_apply,
        Complex.mul_re, Complex.mul_im] <;> ring
  have ha : a ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg b) hba)
  have hscalec : (scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hscale.ne'
  have hca : conj a ≠ 0 := by simpa using ha
  change metricBeltramiFromGram E F G = b / a
  rw [metricBeltramiFromGram, hnum, hden]
  exact mul_div_mul_left b a
    (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hscalec) hca)

end LowDimensionalTopology.Geometry.Teichmuller
