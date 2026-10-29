/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Mobius.SpecialUnitarySignatureOneOne
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The normalized coefficient shape of SU(1,1)

For the fixed form diag(1,-1), special-unitary preservation and determinant
one give the conjugate-entry disc form. Both coefficient conventions are
recorded on the original complex special-linear carrier.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped Matrix MatrixGroups ComplexConjugate

namespace LowDimensionalTopology.Geometry.Mobius

open LowDimensionalTopology.Geometry.Auxiliary.Algebra

/-- Right multiplication by the actual SL inverse linearizes J preservation. -/
theorem specialUnitarySignatureOneOne_conjTranspose_mul_form (A : SL(2, ℂ))
    (hA : A ∈ specialUnitarySignatureOneOne) :
    (A : ComplexMatrix2)ᴴ * signatureOneOneForm =
      signatureOneOneForm * ((A⁻¹ : SL(2, ℂ)) : ComplexMatrix2) := by
  have hinv : (A : ComplexMatrix2) * ((A⁻¹ : SL(2, ℂ)) : ComplexMatrix2) = 1 := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
      using congrArg (fun B : SL(2, ℂ) => (B : ComplexMatrix2)) (mul_inv_cancel A)
  have hpres : (A : ComplexMatrix2)ᴴ * signatureOneOneForm * A =
      signatureOneOneForm := hA
  simpa only [Matrix.mul_assoc, hinv, Matrix.mul_one] using
    congrArg (fun M : ComplexMatrix2 =>
      M * ((A⁻¹ : SL(2, ℂ)) : ComplexMatrix2)) hpres

/-- The original lower-left coefficient convention for a J-preserving SL matrix. -/
theorem specialUnitarySignatureOneOne_normalized_shape (A : SL(2, ℂ))
    (hA : A ∈ specialUnitarySignatureOneOne) :
    A 0 1 = conj (A 1 0) ∧ A 1 1 = conj (A 0 0) ∧
      Complex.normSq (A 0 0) - Complex.normSq (A 1 0) = 1 := by
  have hlinear := specialUnitarySignatureOneOne_conjTranspose_mul_form A hA
  have hd : A 1 1 = conj (A 0 0) := by
    have h := congrArg (fun M : ComplexMatrix2 => M 0 0) hlinear
    simpa only [signatureOneOneForm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Complex.star_def, mul_one, mul_zero,
      one_mul, zero_mul, add_zero] using h.symm
  have hc : A 1 0 = conj (A 0 1) := by
    have h := congrArg (fun M : ComplexMatrix2 => M 1 0) hlinear
    simpa only [signatureOneOneForm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Complex.star_def, mul_one, mul_zero,
      one_mul, zero_mul, add_zero, zero_add, neg_mul, neg_neg] using h.symm
  have hb : A 0 1 = conj (A 1 0) := by
    simpa only [Complex.conj_conj] using (congrArg conj hc).symm
  have hdet : A 0 0 * conj (A 0 0) - A 1 0 * conj (A 1 0) = 1 := by
    simpa only [Matrix.det_fin_two, hb, hd, mul_comm] using A.det_coe
  have hnorm : Complex.normSq (A 0 0) - Complex.normSq (A 1 0) = 1 := by
    simpa only [Complex.sub_re, Complex.mul_conj, Complex.ofReal_re, Complex.one_re]
      using congrArg Complex.re hdet
  exact ⟨hb, hd, hnorm⟩

/-- The book's upper-right coefficient convention has the same exact normalization. -/
theorem specialUnitarySignatureOneOne_source_shape (A : SL(2, ℂ))
    (hA : A ∈ specialUnitarySignatureOneOne) :
    A 1 0 = conj (A 0 1) ∧ A 1 1 = conj (A 0 0) ∧
      Complex.normSq (A 0 0) - Complex.normSq (A 0 1) = 1 := by
  obtain ⟨hb, hd, hn⟩ := specialUnitarySignatureOneOne_normalized_shape A hA
  refine ⟨?_, hd, ?_⟩
  · simpa only [Complex.conj_conj] using (congrArg conj hb).symm
  · simpa only [hb, Complex.normSq_conj] using hn

/-- On the determinant-one carrier, the lower-left normal form is equivalent to SU(1,1). -/
theorem mem_specialUnitarySignatureOneOne_iff_normalized_shape (A : SL(2, ℂ)) :
    A ∈ specialUnitarySignatureOneOne ↔
      A 0 1 = conj (A 1 0) ∧ A 1 1 = conj (A 0 0) ∧
        Complex.normSq (A 0 0) - Complex.normSq (A 1 0) = 1 := by
  constructor
  · exact specialUnitarySignatureOneOne_normalized_shape A
  · rintro ⟨hb, hd, _⟩
    exact mem_specialUnitarySignatureOneOne_of_normalized A hb hd

/-- On the same determinant-one carrier, the source matrix form is equivalent to SU(1,1). -/
theorem mem_specialUnitarySignatureOneOne_iff_source_shape (A : SL(2, ℂ)) :
    A ∈ specialUnitarySignatureOneOne ↔
      A 1 0 = conj (A 0 1) ∧ A 1 1 = conj (A 0 0) ∧
        Complex.normSq (A 0 0) - Complex.normSq (A 0 1) = 1 := by
  constructor
  · exact specialUnitarySignatureOneOne_source_shape A
  · rintro ⟨hc, hd, _⟩
    have hb : A 0 1 = conj (A 1 0) := by
      simpa only [Complex.conj_conj] using (congrArg conj hc).symm
    exact mem_specialUnitarySignatureOneOne_of_normalized A hb hd

end LowDimensionalTopology.Geometry.Mobius
