module
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Real inner products and Gram relations in the complex plane.

Complex coordinates express the real inner product explicitly. The Gram determinant of
three vectors vanishes because the underlying real vector space has dimension two.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Euclidean

theorem complex_real_inner_coordinates (z w : ℂ) :
    inner ℝ z w = z.re * w.re + z.im * w.im := by
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
  change (conj z * w).re = _
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Three vectors in the real plane have singular Gram matrix. -/
theorem complex_gram_three (a b c : ℂ) :
    inner ℝ a a * inner ℝ b b * inner ℝ c c +
      2 * inner ℝ a b * inner ℝ b c * inner ℝ c a -
      inner ℝ a a * (inner ℝ b c) ^ 2 -
      inner ℝ b b * (inner ℝ c a) ^ 2 -
      inner ℝ c c * (inner ℝ a b) ^ 2 = 0 := by
  simp only [complex_real_inner_coordinates]
  ring

end LowDimensionalTopology.Geometry.Euclidean
