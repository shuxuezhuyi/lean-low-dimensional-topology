module

public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.TranslationPowers
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfPlaneDisk

/-!
# Actual traversed axis intervals for every matrix power

The endpoint relation retains the original matrix power. The weighted C1
integral therefore counts repeated traversal, including the zero power, without
replacing the covering element by a primitive axis-stabilizer generator.
-/

public section
noncomputable section

open Set
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Mobius

/-- Every actual matrix power has a genuine C1 axis interval joining `z` to
`A^n • z`, whose weighted integral is exactly `n` times the original translation
length. The case `n = 0` is the constant interval. -/
theorem exists_axis_power_c1_piece
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    (n : ℕ) :
    ∃ c : C1CurvePiece, c.a = 0 ∧ c.b = 1 ∧
      (∀ t : ℝ, c.curve t ∈ (hHyperbolicAxis A hA ht).carrier) ∧
      c.curve 1 = A ^ n • c.curve 0 ∧
      c.length = (n : ℝ) * hTranslationLength (hSLIsometry A) := by
  obtain ⟨s, k, hk, _hk1, haxis, hlen, hact⟩ := hHyperbolicAxis_normalizer A hA ht
  let v := verticalPiece 0 1 (k ^ n) zero_lt_one (pow_pos hk n)
  let c := v.mapSL2 s⁻¹
  have hactn (z : ℍ) :
      (s * A ^ n * s⁻¹) • z = verticalDilationSL (k ^ n) (pow_pos hk n) • z := by
    apply UpperHalfPlane.ext
    calc
      (((s * A ^ n * s⁻¹) • z : ℍ) : ℂ) =
          ((((s * A * s⁻¹) ^ n) • z : ℍ) : ℂ) := by rw [conj_pow]
      _ = (k ^ n : ℝ) * (z : ℂ) :=
        hSL_dilation_pow_coe (s * A * s⁻¹) k hk hact n z
      _ = ((verticalDilationSL (k ^ n) (pow_pos hk n) • z : ℍ) : ℂ) :=
        (verticalDilationSL_coe (k ^ n) (pow_pos hk n) z).symm
  have hvfin : v.curve 1 = verticalDilationSL (k ^ n) (pow_pos hk n) • v.curve 0 := by
    dsimp only [v]
    rw [verticalPiece_finish, verticalPiece_start]
    apply UpperHalfPlane.ext
    rw [verticalDilationSL_coe]
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
  refine ⟨c, rfl, rfl, ?_, ?_, ?_⟩
  · intro t
    rw [haxis]
    change (s • (s⁻¹ • v.curve t)).re = 0
    rw [smul_inv_smul]
    simp only [v, verticalPiece, UpperHalfPlane.mk_re, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  · apply (hSLIsometry s).injective
    change s • (s⁻¹ • v.curve 1) = s • (A ^ n • (s⁻¹ • v.curve 0))
    simp only [smul_inv_smul]
    calc
      v.curve 1 = verticalDilationSL (k ^ n) (pow_pos hk n) • v.curve 0 := hvfin
      _ = (s * A ^ n * s⁻¹) • v.curve 0 := (hactn _).symm
      _ = s • (A ^ n • (s⁻¹ • v.curve 0)) := by simp only [mul_smul]
  · change (v.mapSL2 s⁻¹).length = _
    rw [C1CurvePiece.mapSL2_length]
    change (verticalPiece 0 1 (k ^ n) zero_lt_one (pow_pos hk n)).length = _
    rw [verticalPiece_length, Real.log_one, sub_zero, Real.log_pow, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg n), hlen]

end LowDimensionalTopology.Geometry.Hyperbolic
