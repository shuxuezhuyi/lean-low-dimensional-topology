module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenInequality
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
open scoped Matrix.Norms.Frobenius
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius

/-- The trace functional has Frobenius operator bound given by the norm of identity. -/
theorem jorgensen_trace_norm_le (X : Auxiliary.Algebra.ComplexMatrix2) :
    ‖Matrix.trace X‖ ≤ Auxiliary.Algebra.matrixNorm X * Auxiliary.Algebra.matrixNorm 1 := by
  have h := Auxiliary.Algebra.matrixScalarProduct_norm_le X 1
  simpa only [Auxiliary.Algebra.matrixScalarProduct, Matrix.conjTranspose_one, Matrix.mul_one] using h

/-- A convenient exact rational upper bound for the Frobenius norm of identity. -/
theorem jorgensen_matrixNorm_one_le : Auxiliary.Algebra.matrixNorm (1 : Auxiliary.Algebra.ComplexMatrix2) ≤ 10 / 7 := by
  have hs : Auxiliary.Algebra.matrixNorm (1 : Auxiliary.Algebra.ComplexMatrix2) ^ 2 = 2 :=
    by norm_num [Auxiliary.Algebra.matrixNorm_sq]
  nlinarith [Auxiliary.Algebra.matrixNorm_nonneg (1 : Auxiliary.Algebra.ComplexMatrix2)]

/-- Determinant-one inversion preserves this Frobenius norm exactly. -/
theorem jorgensen_matrixNorm_inv (A : Auxiliary.Algebra.SpecialLinear2) :
    Auxiliary.Algebra.matrixNorm ((A⁻¹ : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) =
      Auxiliary.Algebra.matrixNorm (A : Auxiliary.Algebra.ComplexMatrix2) := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Auxiliary.Algebra.matrixNorm_adjugate]

/-- The commutator difference has two quadratic factors before the actual inverse matrices. -/
theorem jorgensen_commutator_difference (A B : Auxiliary.Algebra.SpecialLinear2) :
    (Mobius.Classification.specialCommutator A B : Auxiliary.Algebra.ComplexMatrix2) - 1 =
      ((((A : Auxiliary.Algebra.ComplexMatrix2) - 1) * ((B : Auxiliary.Algebra.ComplexMatrix2) - 1) -
        ((B : Auxiliary.Algebra.ComplexMatrix2) - 1) * ((A : Auxiliary.Algebra.ComplexMatrix2) - 1)) *
        ((A⁻¹ : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2)) * ((B⁻¹ :
          Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) := by
  have hp : ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) * ((B : Auxiliary.Algebra.ComplexMatrix2) - 1) -
      ((B : Auxiliary.Algebra.ComplexMatrix2) - 1) * ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) =
      (A : Auxiliary.Algebra.ComplexMatrix2) * (B : Auxiliary.Algebra.ComplexMatrix2) - (B :
        Auxiliary.Algebra.ComplexMatrix2) * (A : Auxiliary.Algebra.ComplexMatrix2) := by noncomm_ring
  rw [hp, Matrix.sub_mul, Matrix.sub_mul]
  have hc : (B : Auxiliary.Algebra.ComplexMatrix2) * (A : Auxiliary.Algebra.ComplexMatrix2) *
      ((A⁻¹ : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) * ((B⁻¹ :
        Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) = 1 := by
    change ((B * A * A⁻¹ * B⁻¹ : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) = 1
    simp
  rw [hc]
  rfl

/-- Exact small-difference bounds imply uniform rational bounds on both inverse norms. -/
theorem jorgensen_small_matrixNorm (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) ≤ 7 / 50) :
      Auxiliary.Algebra.matrixNorm (A : Auxiliary.Algebra.ComplexMatrix2) ≤ 8 / 5 := by
  have ha := Auxiliary.Algebra.matrixNorm_add_le ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) 1
  rw [sub_add_cancel] at ha
  linarith [jorgensen_matrixNorm_one_le]

/-- A small difference from identity forces its trace difference into a fifth of the unit disc. -/
theorem jorgensen_small_trace (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) ≤ 7 / 50) :
    ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) - 2‖ ≤ 1 / 5 := by
  have ht := jorgensen_trace_norm_le ((A : Auxiliary.Algebra.ComplexMatrix2) - 1)
  have htr : Matrix.trace ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) = Matrix.trace (A :
    Auxiliary.Algebra.ComplexMatrix2) - 2 := by
    rw [Matrix.trace_sub]
    norm_num [Matrix.trace_fin_two]
  rw [htr] at ht
  have hb := mul_le_mul hA jorgensen_matrixNorm_one_le
    (Auxiliary.Algebra.matrixNorm_nonneg _) (by norm_num : (0 : ℝ) ≤ 7 / 50)
  norm_num at hb
  exact ht.trans hb

/-- The trace-square term is uniformly at most twenty-one twenty-fifths in the small ball. -/
theorem jorgensen_small_squaredTrace (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) ≤ 7 / 50) :
    ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4‖ ≤ 21 / 25 := by
  have hs := jorgensen_small_trace A hA
  have he : Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4 =
      (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) - 2) * (4 + (Matrix.trace (A :
        Auxiliary.Algebra.ComplexMatrix2) - 2)) := by ring
  rw [he, norm_mul]
  have hb : ‖(4 : ℂ) + (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) - 2)‖ ≤ 4 + ‖Matrix.trace (A :
    Auxiliary.Algebra.ComplexMatrix2) - 2‖ := by
    simpa only [Complex.norm_ofNat] using norm_add_le (4 : ℂ) (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) - 2)
  calc
    _ ≤ (1 / 5 : ℝ) * (4 + 1 / 5) :=
      mul_le_mul hs (hb.trans (by linarith)) (norm_nonneg _) (by norm_num)
    _ = 21 / 25 := by norm_num

/-- The commutator trace term is strictly small when both differences are at most 0.14. -/
theorem jorgensen_small_commutatorTrace (A B : Auxiliary.Algebra.SpecialLinear2)
    (hA : Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) ≤ 7 / 50)
    (hB : Auxiliary.Algebra.matrixNorm ((B : Auxiliary.Algebra.ComplexMatrix2) - 1) ≤ 7 / 50) :
    ‖Matrix.trace (Mobius.Classification.specialCommutator A B : Auxiliary.Algebra.ComplexMatrix2) - 2‖ ≤ 448 /
      3125 := by
  let X := (A : Auxiliary.Algebra.ComplexMatrix2) - 1
  let Y := (B : Auxiliary.Algebra.ComplexMatrix2) - 1
  have hXY : Auxiliary.Algebra.matrixNorm (X * Y - Y * X) ≤ 2 * (7 / 50 : ℝ) ^ 2 := by
    have hnorm := norm_sub_le (X * Y) (Y * X)
    have hm1 := Auxiliary.Algebra.matrixNorm_mul_le X Y
    have hm2 := Auxiliary.Algebra.matrixNorm_mul_le Y X
    have hb := mul_le_mul hA hB (Auxiliary.Algebra.matrixNorm_nonneg _) (by norm_num : (0 : ℝ) ≤ 7 / 50)
    change Auxiliary.Algebra.matrixNorm (X * Y - Y * X) ≤ Auxiliary.Algebra.matrixNorm (X * Y) +
      Auxiliary.Algebra.matrixNorm (Y * X) at hnorm
    change Auxiliary.Algebra.matrixNorm X * Auxiliary.Algebra.matrixNorm Y ≤ (7 / 50 : ℝ) * (7 / 50) at hb
    nlinarith
  have hC : Auxiliary.Algebra.matrixNorm ((Mobius.Classification.specialCommutator A B :
    Auxiliary.Algebra.ComplexMatrix2) - 1) ≤
      2 * (7 / 50 : ℝ) ^ 2 * (8 / 5) * (8 / 5) := by
    rw [jorgensen_commutator_difference]
    have ha : Auxiliary.Algebra.matrixNorm (((A⁻¹ : Auxiliary.Algebra.SpecialLinear2) :
      Auxiliary.Algebra.ComplexMatrix2)) ≤ 8 / 5 := by
      rw [jorgensen_matrixNorm_inv]
      exact jorgensen_small_matrixNorm A hA
    have hb : Auxiliary.Algebra.matrixNorm (((B⁻¹ : Auxiliary.Algebra.SpecialLinear2) :
      Auxiliary.Algebra.ComplexMatrix2)) ≤ 8 / 5 := by
      rw [jorgensen_matrixNorm_inv]
      exact jorgensen_small_matrixNorm B hB
    calc
      _ ≤ Auxiliary.Algebra.matrixNorm ((X * Y - Y * X) * ((A⁻¹ : Auxiliary.Algebra.SpecialLinear2) :
        Auxiliary.Algebra.ComplexMatrix2)) *
          Auxiliary.Algebra.matrixNorm ((B⁻¹ : Auxiliary.Algebra.SpecialLinear2) :
            Auxiliary.Algebra.ComplexMatrix2) := Auxiliary.Algebra.matrixNorm_mul_le _ _
      _ ≤ (Auxiliary.Algebra.matrixNorm (X * Y - Y * X) * Auxiliary.Algebra.matrixNorm ((A⁻¹ :
        Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2)) *
          Auxiliary.Algebra.matrixNorm ((B⁻¹ : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) :=
        mul_le_mul_of_nonneg_right (Auxiliary.Algebra.matrixNorm_mul_le _ _) (Auxiliary.Algebra.matrixNorm_nonneg _)
      _ ≤ _ := mul_le_mul (mul_le_mul hXY ha (Auxiliary.Algebra.matrixNorm_nonneg _) (by norm_num)) hb
        (Auxiliary.Algebra.matrixNorm_nonneg _) (by norm_num)
  have ht := jorgensen_trace_norm_le ((Mobius.Classification.specialCommutator A B :
    Auxiliary.Algebra.ComplexMatrix2) - 1)
  have htr : Matrix.trace ((Mobius.Classification.specialCommutator A B : Auxiliary.Algebra.ComplexMatrix2) - 1) =
      Matrix.trace (Mobius.Classification.specialCommutator A B : Auxiliary.Algebra.ComplexMatrix2) - 2 := by
    rw [Matrix.trace_sub]
    norm_num [Matrix.trace_fin_two]
  rw [htr] at ht
  have hb := mul_le_mul hC jorgensen_matrixNorm_one_le (Auxiliary.Algebra.matrixNorm_nonneg _) (by norm_num :
    (0 : ℝ) ≤ 2 * (7 / 50) ^ 2 * (8 / 5) * (8 / 5))
  norm_num at hb
  exact ht.trans hb

/-- A discrete non-elementary determinant-one pair has an identity norm gap greater than 7/50. -/
theorem specialLinear_jorgensen_identity_separation (A B : Auxiliary.Algebra.SpecialLinear2)
    (hD : DiscreteTopology (Subgroup.closure ({A, B} : Set Auxiliary.Algebra.SpecialLinear2)))
    (hH : IsNonElementary (Subgroup.closure
      ({Mobius.mobiusSpecialLinearProjection A, Mobius.mobiusSpecialLinearProjection B} : Set
        Mobius.complexMobiusGroup))) :
    (7 / 50 : ℝ) < max (Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - 1))
      (Auxiliary.Algebra.matrixNorm ((B : Auxiliary.Algebra.ComplexMatrix2) - 1)) := by
  by_contra! h
  have hA := (max_le_iff.mp h).1
  have hB := (max_le_iff.mp h).2
  have ht := jorgensen_small_squaredTrace A hA
  have hc := jorgensen_small_commutatorTrace A B hA hB
  have hj := specialLinear_jorgensen_inequality A B hD hH
  unfold jorgensenMatrixDefect at hj
  linarith

end LowDimensionalTopology.Geometry.DiscreteGroups
