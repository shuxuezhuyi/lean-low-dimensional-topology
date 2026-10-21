/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Auxiliary real Möbius normalization

These lemmas support the separate construction of the weighted path metric.
The normalization is proved using an explicit real circle center and endpoint.
The final identity concerns a tangent vector; integration and the piecewise curve construction
are handled in the curve-length module.
-/

@[expose] public section

open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- A determinant-one representative of the reciprocal map with a real pole. -/
def verticalNormalizer (a : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![0, -1; 1, -a], by simp [Matrix.det_fin_two]⟩

/-- The real coordinate of the explicit reciprocal transformation. -/
theorem verticalNormalizer_re (a : ℝ) (z : ℍ) :
    (verticalNormalizer a • z).re =
      (a - z.re) / ((z.re - a) ^ 2 + z.im ^ 2) := by
  change ((verticalNormalizer a • z : ℍ) : ℂ).re = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [verticalNormalizer, Complex.div_re, Complex.normSq_apply, pow_two]
  ring

/-- Auxiliary normalization for the proof: two points can be put on one vertical line. -/
theorem exists_sl2_same_real_part (z w : ℍ) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, (g • z).re = (g • w).re := by
  by_cases h : z.re = w.re
  · exact ⟨1, by simpa using h⟩
  · let c := (z.re ^ 2 + z.im ^ 2 - w.re ^ 2 - w.im ^ 2) / (2 * (z.re - w.re))
    have hc : 2 * c * (z.re - w.re) =
        z.re ^ 2 + z.im ^ 2 - w.re ^ 2 - w.im ^ 2 := by
      dsimp [c]
      field_simp
    have hcircle : (w.re - c) ^ 2 + w.im ^ 2 = (z.re - c) ^ 2 + z.im ^ 2 := by
      nlinarith [hc]
    let r := Real.sqrt ((z.re - c) ^ 2 + z.im ^ 2)
    have hrpos : 0 < r := by
      apply Real.sqrt_pos.mpr
      nlinarith [z.im_pos, sq_nonneg (z.re - c)]
    have hrsq : r ^ 2 = (z.re - c) ^ 2 + z.im ^ 2 :=
      Real.sq_sqrt (by positivity)
    let a := c + r
    have hza : a - z.re ≠ 0 := by
      intro hz
      dsimp [a] at hz
      nlinarith [z.im_pos, hrsq]
    have hwa : a - w.re ≠ 0 := by
      intro hw
      dsimp [a] at hw
      nlinarith [w.im_pos, hrsq, hcircle]
    have hzden : (z.re - a) ^ 2 + z.im ^ 2 = 2 * r * (a - z.re) := by
      dsimp [a]
      nlinarith [hrsq]
    have hwden : (w.re - a) ^ 2 + w.im ^ 2 = 2 * r * (a - w.re) := by
      dsimp [a]
      nlinarith [hrsq, hcircle]
    refine ⟨verticalNormalizer a, ?_⟩
    rw [verticalNormalizer_re, verticalNormalizer_re, hzden, hwden]
    field_simp

/-- The imaginary-part formula specialized to real determinant-one matrices. -/
theorem sl2_im_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    (g • z).im = z.im / Complex.normSq
      (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z) := by
  change ((Matrix.SpecialLinearGroup.mapGL ℝ g) • z).im = _
  simpa using UpperHalfPlane.im_smul_eq_div_normSq (Matrix.SpecialLinearGroup.mapGL ℝ g) z

/-- Auxiliary pointwise speed identity for the weighted curve length. -/
theorem sl2_weighted_tangent_norm (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (z : ℍ) (v : ℂ) :
    ‖((1 : ℂ) / (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z) ^ 2) * v‖ /
      (g • z).im = ‖v‖ / z.im := by
  have hd := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) z
  rw [norm_mul, norm_div, norm_one, norm_pow, sl2_im_smul, Complex.normSq_eq_norm_sq]
  field_simp

end LowDimensionalTopology.Geometry.Hyperbolic
