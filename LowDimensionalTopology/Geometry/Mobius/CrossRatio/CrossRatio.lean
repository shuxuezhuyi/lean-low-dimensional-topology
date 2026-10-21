/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Mobius.Metric.ChordalIsometries
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The cross-ratio on the actual extended complex plane

Homogeneous determinants give one formula that also handles infinity. The total
complex-valued definition is total, with division by zero equal to zero;
the nondegenerate geometric applications use distinct points.
-/

@[expose] public section

namespace LowDimensionalTopology.Geometry.Mobius

open scoped OnePoint LinearAlgebra.Projectivization

noncomputable section

/-- Alternating determinant of two homogeneous columns. -/
def complexWedge (v w : Fin 2 → ℂ) : ℂ := v 0 * w 1 - v 1 * w 0

/-- The cross-ratio expression in arbitrary homogeneous coordinates. -/
def homogeneousCrossRatio (v₁ v₂ v₃ v₄ : Fin 2 → ℂ) : ℂ :=
  (complexWedge v₁ v₃ * complexWedge v₂ v₄) /
    (complexWedge v₁ v₂ * complexWedge v₃ v₄)

/-- The cross-ratio, including configurations with an infinite point. -/
def extendedCrossRatio (z₁ z₂ z₃ z₄ : ExtendedComplex) : ℂ :=
  homogeneousCrossRatio (complexProjectiveVector z₁) (complexProjectiveVector z₂)
    (complexProjectiveVector z₃) (complexProjectiveVector z₄)

theorem complexWedge_units_smul (a b : ℂˣ) (v w : Fin 2 → ℂ) :
    complexWedge (a • v) (b • w) = (a : ℂ) * (b : ℂ) * complexWedge v w := by
  simp only [complexWedge, Pi.smul_apply, Units.smul_def, smul_eq_mul]
  ring

/-- The ratio is independent of the four independently rescaled homogeneous representatives. -/
theorem homogeneousCrossRatio_units_smul (a b c d : ℂˣ) (v₁ v₂ v₃ v₄ : Fin 2 → ℂ) :
    homogeneousCrossRatio (a • v₁) (b • v₂) (c • v₃) (d • v₄) =
      homogeneousCrossRatio v₁ v₂ v₃ v₄ := by
  simp only [homogeneousCrossRatio, complexWedge_units_smul]
  have hn : (a : ℂ) * b * c * d ≠ 0 := by exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (Units.ne_zero a) (Units.ne_zero b)) (Units.ne_zero c)) (Units.ne_zero d)
  rw [show (a : ℂ) * c * complexWedge v₁ v₃ * ((b : ℂ) * d * complexWedge v₂ v₄) =
      ((a : ℂ) * b * c * d) * (complexWedge v₁ v₃ * complexWedge v₂ v₄) by ring,
    show (a : ℂ) * b * complexWedge v₁ v₂ * ((c : ℂ) * d * complexWedge v₃ v₄) =
      ((a : ℂ) * b * c * d) * (complexWedge v₁ v₂ * complexWedge v₃ v₄) by ring,
    mul_div_mul_left _ _ hn]

/-- Invertible matrices preserve the homogeneous cross-ratio. -/
theorem homogeneousCrossRatio_matrix_smul (g : FractionalLinearMatrix)
    (v₁ v₂ v₃ v₄ : Fin 2 → ℂ) :
    homogeneousCrossRatio (g • v₁) (g • v₂) (g • v₃) (g • v₄) =
      homogeneousCrossRatio v₁ v₂ v₃ v₄ := by
  simp only [homogeneousCrossRatio, complexWedge, homogeneous_wedge_smul]
  rw [show (g : Auxiliary.Algebra.ComplexMatrix2).det * (v₁ 0 * v₃ 1 - v₁ 1 * v₃ 0) *
      ((g : Auxiliary.Algebra.ComplexMatrix2).det * (v₂ 0 * v₄ 1 - v₂ 1 * v₄ 0)) =
        (g : Auxiliary.Algebra.ComplexMatrix2).det ^ 2 *
          ((v₁ 0 * v₃ 1 - v₁ 1 * v₃ 0) * (v₂ 0 * v₄ 1 - v₂ 1 * v₄ 0)) by ring,
    show (g : Auxiliary.Algebra.ComplexMatrix2).det * (v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0) *
      ((g : Auxiliary.Algebra.ComplexMatrix2).det * (v₃ 0 * v₄ 1 - v₃ 1 * v₄ 0)) =
        (g : Auxiliary.Algebra.ComplexMatrix2).det ^ 2 *
          ((v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0) * (v₃ 0 * v₄ 1 - v₃ 1 * v₄ 0)) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 g.det_ne_zero)]

/-- Any nonzero representative of a point differs from its fixed representative by a unit. -/
theorem exists_unit_smul_projectiveVector (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    ∃ a : ℂˣ, a • v = complexProjectiveVector (complexProjectivePoint v) := by
  have h :
      (OnePoint.equivProjectivization ℂ).symm
          (Projectivization.mk ℂ (complexProjectiveVector (complexProjectivePoint v))
            (complexProjectiveVector_ne_zero _)) =
        (OnePoint.equivProjectivization ℂ).symm (Projectivization.mk ℂ v hv) := by
    calc
      _ = complexProjectivePoint (complexProjectiveVector (complexProjectivePoint v)) :=
        (complexProjectivePoint_eq_projectivization _ _).symm
      _ = complexProjectivePoint v := complexProjectivePoint_vector _
      _ = _ := complexProjectivePoint_eq_projectivization v hv
  exact (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp
    ((OnePoint.equivProjectivization ℂ).symm.injective h)

/-- The actual extended-plane ratio may be evaluated in any four nonzero homogeneous representatives. -/
theorem extendedCrossRatio_projective (v₁ v₂ v₃ v₄ : Fin 2 → ℂ)
    (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0) (h₃ : v₃ ≠ 0) (h₄ : v₄ ≠ 0) :
    extendedCrossRatio (complexProjectivePoint v₁) (complexProjectivePoint v₂)
      (complexProjectivePoint v₃) (complexProjectivePoint v₄) =
        homogeneousCrossRatio v₁ v₂ v₃ v₄ := by
  obtain ⟨a, ha⟩ := exists_unit_smul_projectiveVector v₁ h₁
  obtain ⟨b, hb⟩ := exists_unit_smul_projectiveVector v₂ h₂
  obtain ⟨c, hc⟩ := exists_unit_smul_projectiveVector v₃ h₃
  obtain ⟨d, hd⟩ := exists_unit_smul_projectiveVector v₄ h₄
  rw [extendedCrossRatio, ← ha, ← hb, ← hc, ← hd, homogeneousCrossRatio_units_smul]

/-- Möbius invariance on the actual extended complex plane, including poles and infinity. -/
theorem extendedCrossRatio_fractionalLinear (g : FractionalLinearMatrix)
    (z₁ z₂ z₃ z₄ : ExtendedComplex) :
    extendedCrossRatio (fractionalLinear g z₁) (fractionalLinear g z₂)
      (fractionalLinear g z₃) (fractionalLinear g z₄) = extendedCrossRatio z₁ z₂ z₃ z₄ := by
  have hp (z : ExtendedComplex) :
      fractionalLinear g z = complexProjectivePoint (g • complexProjectiveVector z) := by
    rw [complexProjectivePoint_smul g _ (complexProjectiveVector_ne_zero z),
      complexProjectivePoint_vector]
  rw [hp z₁, hp z₂, hp z₃, hp z₄, extendedCrossRatio_projective _ _ _ _
    ((smul_ne_zero_iff_ne g).mpr (complexProjectiveVector_ne_zero z₁))
    ((smul_ne_zero_iff_ne g).mpr (complexProjectiveVector_ne_zero z₂))
    ((smul_ne_zero_iff_ne g).mpr (complexProjectiveVector_ne_zero z₃))
    ((smul_ne_zero_iff_ne g).mpr (complexProjectiveVector_ne_zero z₄)),
    homogeneousCrossRatio_matrix_smul]
  rfl

/-- The exact finite formula, with the ordering convention used throughout this formulation. -/
theorem extendedCrossRatio_coe (z₁ z₂ z₃ z₄ : ℂ) :
    extendedCrossRatio z₁ z₂ z₃ z₄ = ((z₁ - z₃) * (z₂ - z₄)) /
      ((z₁ - z₂) * (z₃ - z₄)) := by
  simp [extendedCrossRatio, homogeneousCrossRatio, complexWedge, complexProjectiveVector]

theorem extendedCrossRatio_infty_fourth (z₁ z₂ z₃ : ℂ) :
    extendedCrossRatio z₁ z₂ z₃ ∞ = (z₁ - z₃) / (z₁ - z₂) := by
  simp only [extendedCrossRatio, homogeneousCrossRatio, complexWedge, complexProjectiveVector,
    OnePoint.elim_some, OnePoint.elim_infty, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_one, one_mul, mul_zero, zero_sub, mul_neg, neg_div_neg_eq]

theorem extendedCrossRatio_infty_first (z₂ z₃ z₄ : ℂ) :
    extendedCrossRatio ∞ z₂ z₃ z₄ = (z₂ - z₄) / (z₃ - z₄) := by
  simp [extendedCrossRatio, homogeneousCrossRatio, complexWedge, complexProjectiveVector]

theorem extendedCrossRatio_infty_second (z₁ z₃ z₄ : ℂ) :
    extendedCrossRatio z₁ ∞ z₃ z₄ = (z₃ - z₁) / (z₃ - z₄) := by
  simp only [extendedCrossRatio, homogeneousCrossRatio, complexWedge, complexProjectiveVector,
    OnePoint.elim_some, OnePoint.elim_infty, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_one, one_mul, mul_zero, zero_mul, zero_sub, sub_zero, neg_one_mul]
  rw [div_neg_eq_neg_div, ← neg_div, neg_sub]

theorem extendedCrossRatio_infty_third (z₁ z₂ z₄ : ℂ) :
    extendedCrossRatio z₁ z₂ ∞ z₄ = (z₂ - z₄) / (z₂ - z₁) := by
  simp only [extendedCrossRatio, homogeneousCrossRatio, complexWedge, complexProjectiveVector,
    OnePoint.elim_some, OnePoint.elim_infty, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_one, one_mul, mul_zero, zero_mul, zero_sub, sub_zero, neg_one_mul]
  rw [neg_div, ← div_neg_eq_neg_div, neg_sub]

theorem extendedCrossRatio_zero_one_infty (z : ℂ) :
    extendedCrossRatio (0 : ℂ) (1 : ℂ) z ∞ = z := by
  rw [extendedCrossRatio_infty_fourth]
  simp

/-- The finite fractional-linear difference formula used. -/
theorem fractionalLinear_difference_formula (a b c d z w : ℂ)
    (hz : c * z + d ≠ 0) (hw : c * w + d ≠ 0) :
    (a * z + b) / (c * z + d) - (a * w + b) / (c * w + d) =
      (a * d - b * c) * (z - w) / ((c * z + d) * (c * w + d)) := by
  have hz' : z * c + d ≠ 0 := by simpa only [mul_comm] using hz
  have hw' : w * c + d ≠ 0 := by simpa only [mul_comm] using hw
  field_simp [hz, hw, hz', hw']
  ring

/-- The homogeneous denominator is nonzero exactly when its pair of actual points differ. -/
theorem complexWedge_projectiveVector_eq_zero_iff (z w : ExtendedComplex) :
    complexWedge (complexProjectiveVector z) (complexProjectiveVector w) = 0 ↔ z = w := by
  cases z using OnePoint.rec <;> cases w using OnePoint.rec <;>
    simp [complexWedge, complexProjectiveVector, sub_eq_zero]

end

end LowDimensionalTopology.Geometry.Mobius
