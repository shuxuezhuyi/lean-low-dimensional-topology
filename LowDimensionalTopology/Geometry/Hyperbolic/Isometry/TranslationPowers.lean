module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicRayReturns
public import Mathlib.Algebra.Group.Conj

@[expose] public section
noncomputable section
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Mobius

/-- Every natural power of an actual hyperbolic matrix retains its full
translation length, including the zero power. No primitivity is required. -/
theorem hSL_translationLength_pow
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    (n : ℕ) :
    hTranslationLength (hSLIsometry (A ^ n)) =
      (n : ℝ) * hTranslationLength (hSLIsometry A) := by
  obtain ⟨s, k, hk, _hk1, hact, hlen⟩ :=
    realSLMobius_hyperbolic_translationLength A hA ht
  have hiso : hSLIsometry (s * A ^ n * s⁻¹) =
      hSLIsometry (verticalDilationSL (k ^ n) (pow_pos hk n)) := by
    apply IsometryEquiv.ext
    intro z
    change (s * A ^ n * s⁻¹) • z =
      verticalDilationSL (k ^ n) (pow_pos hk n) • z
    apply UpperHalfPlane.ext
    calc
      (((s * A ^ n * s⁻¹) • z : ℍ) : ℂ) =
          ((((s * A * s⁻¹) ^ n) • z : ℍ) : ℂ) := by rw [conj_pow]
      _ = (k ^ n : ℝ) * (z : ℂ) :=
        hSL_dilation_pow_coe (s * A * s⁻¹) k hk hact n z
      _ = ((verticalDilationSL (k ^ n) (pow_pos hk n) • z : ℍ) : ℂ) :=
        (verticalDilationSL_coe (k ^ n) (pow_pos hk n) z).symm
  calc
    hTranslationLength (hSLIsometry (A ^ n)) =
        hTranslationLength (hSLIsometry (s * A ^ n * s⁻¹)) := by
      rw [hSLIsometry_conjugation, hTranslationLength_conjugation]
    _ = |Real.log (k ^ n)| := by rw [hiso, dilation_translationLength]
    _ = (n : ℝ) * |Real.log k| := by
      rw [Real.log_pow, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    _ = (n : ℝ) * hTranslationLength (hSLIsometry A) := by rw [hlen]

end LowDimensionalTopology.Geometry.Hyperbolic
