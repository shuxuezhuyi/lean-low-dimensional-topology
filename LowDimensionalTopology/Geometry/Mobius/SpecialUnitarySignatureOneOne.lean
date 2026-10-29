/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.StandardAutomorphisms
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The signature-(1,1) special-unitary group and its sign quotient

The form is literally diag(1,-1), and the ambient matrices have determinant one.
The quotient acts faithfully through its actual global sphere image. Every
analytic automorphism of the inherited disc has a lift to this group. The full
identification of this quotient with the disc automorphism group is not asserted.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open scoped Matrix MatrixGroups ComplexConjugate

namespace LowDimensionalTopology.Geometry.Mobius

open LowDimensionalTopology.Geometry.Auxiliary.Algebra

/-- The fixed Hermitian form of signature (1,1), rather than the positive form. -/
def signatureOneOneForm : ComplexMatrix2 := !![1, 0; 0, -1]

/-- The genuine J-preserving subgroup of the original complex SL(2) carrier. -/
def specialUnitarySignatureOneOne : Subgroup SL(2, ℂ) where
  carrier := {A | (A : ComplexMatrix2)ᴴ * signatureOneOneForm * A = signatureOneOneForm}
  one_mem' := by simp
  mul_mem' := by
    intro A B hA hB
    calc
      ((A * B : SL(2, ℂ)) : ComplexMatrix2)ᴴ * signatureOneOneForm * (A * B) =
          (B : ComplexMatrix2)ᴴ *
            ((A : ComplexMatrix2)ᴴ * signatureOneOneForm * A) * B := by
              simp only [Matrix.SpecialLinearGroup.coe_mul,
                Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = signatureOneOneForm := by rw [hA]; exact hB
  inv_mem' := by
    intro A hA
    have hinv : (A : ComplexMatrix2) * ((A⁻¹ : SL(2, ℂ)) : ComplexMatrix2) = 1 := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
        using congrArg (fun B : SL(2, ℂ) => (B : ComplexMatrix2)) (mul_inv_cancel A)
    calc
      ((A⁻¹ : SL(2, ℂ)) : ComplexMatrix2)ᴴ * signatureOneOneForm *
          ((A⁻¹ : SL(2, ℂ)) : ComplexMatrix2) =
          ((A⁻¹ : SL(2, ℂ)) : ComplexMatrix2)ᴴ *
            ((A : ComplexMatrix2)ᴴ * signatureOneOneForm * (A : ComplexMatrix2)) *
              ((A⁻¹ : SL(2, ℂ)) : ComplexMatrix2) := by rw [hA]
      _ = ((A : ComplexMatrix2) * ((A⁻¹ : SL(2, ℂ)) : ComplexMatrix2))ᴴ * signatureOneOneForm *
          ((A : ComplexMatrix2) * ((A⁻¹ : SL(2, ℂ)) : ComplexMatrix2)) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = signatureOneOneForm := by
        simp only [hinv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/-- The scalar sign subgroup, pulled back from the original SL center. -/
def specialUnitarySignatureOneOneSigns : Subgroup specialUnitarySignatureOneOne :=
  (Subgroup.center SL(2, ℂ)).comap specialUnitarySignatureOneOne.subtype

instance specialUnitarySignatureOneOneSigns_normal :
    specialUnitarySignatureOneOneSigns.Normal := by
  unfold specialUnitarySignatureOneOneSigns
  infer_instance

/-- The literal SU(1,1)/{I,-I} quotient; its precise sign criterion is proved below. -/
abbrev ProjectiveSpecialUnitarySignatureOneOne : Type :=
  specialUnitarySignatureOneOne ⧸ specialUnitarySignatureOneOneSigns

/-- The original determinant-one sphere projection restricted to genuine SU(1,1). -/
def specialUnitarySignatureOneOneProjection :
    specialUnitarySignatureOneOne →* complexMobiusGroup :=
  mobiusSpecialLinearProjection.comp specialUnitarySignatureOneOne.subtype

/-- The restricted action kernel is exactly the scalar sign subgroup. -/
theorem specialUnitarySignatureOneOneProjection_kernel :
    specialUnitarySignatureOneOneProjection.ker = specialUnitarySignatureOneOneSigns := by
  ext A
  change mobiusSpecialLinearProjection A.val = 1 ↔ A.val ∈ Subgroup.center SL(2, ℂ)
  rw [← MonoidHom.mem_ker, mobiusSpecialLinearProjection_kernel]

/-- No further matrices are identified in the quotient. -/
theorem specialUnitarySignatureOneOneSigns_mem_iff (A : specialUnitarySignatureOneOne) :
    A ∈ specialUnitarySignatureOneOneSigns ↔
      (A.val : ComplexMatrix2) = 1 ∨ (A.val : ComplexMatrix2) = -1 := by
  rw [← specialUnitarySignatureOneOneProjection_kernel, MonoidHom.mem_ker]
  exact mobiusSpecialLinearProjection_eq_one_iff A.val

/-- The negative scalar identity really belongs to the J-preserving group. -/
theorem neg_one_mem_specialUnitarySignatureOneOne :
    (-1 : SL(2, ℂ)) ∈ specialUnitarySignatureOneOne := by
  change ((-1 : SL(2, ℂ)) : ComplexMatrix2)ᴴ * signatureOneOneForm *
    (-1 : SL(2, ℂ)) = signatureOneOneForm
  simp

/-- The sign quotient identifies with its faithful actual global sphere image.
This statement does not identify that image with the full disc automorphism group. -/
def projectiveSpecialUnitarySignatureOneOneMobiusEquiv :
    ProjectiveSpecialUnitarySignatureOneOne ≃*
      specialUnitarySignatureOneOneProjection.range :=
  QuotientGroup.liftEquiv specialUnitarySignatureOneOneSigns
    (MonoidHom.rangeRestrict_surjective specialUnitarySignatureOneOneProjection)
    (by rw [MonoidHom.ker_rangeRestrict, specialUnitarySignatureOneOneProjection_kernel])

/-- The quotient's global sphere map is precisely the original SL projection. -/
theorem projectiveSpecialUnitarySignatureOneOneMobiusEquiv_mk
    (A : specialUnitarySignatureOneOne) :
    projectiveSpecialUnitarySignatureOneOneMobiusEquiv (QuotientGroup.mk A) =
      specialUnitarySignatureOneOneProjection.rangeRestrict A :=
  QuotientGroup.liftEquiv_mk _ _ _ A

/-- The determinant-one conjugate-entry normal form preserves the actual J form. -/
theorem mem_specialUnitarySignatureOneOne_of_normalized (A : SL(2, ℂ))
    (hb : A 0 1 = conj (A 1 0)) (hd : A 1 1 = conj (A 0 0)) :
    A ∈ specialUnitarySignatureOneOne := by
  have he : (A : ComplexMatrix2) = !![A 0 0, conj (A 1 0); A 1 0, conj (A 0 0)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hd]
  have hdet : A 0 0 * conj (A 0 0) - conj (A 1 0) * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two, hb, hd] using A.det_coe
  have hneg : A 1 0 * conj (A 1 0) - A 0 0 * conj (A 0 0) = -1 := by
    linear_combination -hdet
  change (A : ComplexMatrix2)ᴴ * signatureOneOneForm * A = signatureOneOneForm
  rw [he]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [signatureOneOneForm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Complex.star_def, Complex.conj_conj,
      mul_zero, mul_one, mul_neg, neg_mul, add_zero, zero_add]
  · linear_combination hdet
  · ring
  · ring
  · linear_combination hneg

/-- Any determinant-one representative of an actual disc preserver lies in SU(1,1). -/
theorem mem_specialUnitarySignatureOneOne_of_disc_preserving (A : SL(2, ℂ))
    (hA : (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) ''
      Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc) :
    A ∈ specialUnitarySignatureOneOne := by
  have haction : (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) =
      fractionalLinear (Matrix.SpecialLinearGroup.toGL A) := mobiusMatrixProjection_coe _
  rw [haction] at hA
  obtain ⟨hb, hd, _⟩ := Hyperbolic.specialLinear_disc_coefficients A hA
  exact mem_specialUnitarySignatureOneOne_of_normalized A hb hd

/-- Every automorphism of the original inherited disc surface has an actual
SU(1,1) representative. No assumption about its matrix form is supplied. -/
theorem disc_analytic_automorphism_exists_specialUnitarySignatureOneOne
    (H : Hyperbolic.extendedUnitDisc ≃ₜ Hyperbolic.extendedUnitDisc)
    (hH : Surfaces.RiemannAnalyticMap Surfaces.discRiemannSurface.toRiemannAtlas
      Surfaces.discRiemannSurface.toRiemannAtlas H) :
    ∃ A : specialUnitarySignatureOneOne, ∀ z : Hyperbolic.extendedUnitDisc,
      (specialUnitarySignatureOneOneProjection A).val z.val = (H z).val := by
  obtain ⟨M, hM, hEq⟩ := Surfaces.discRiemannSurface_automorphism_exists_mobius H hH
  obtain ⟨A, hA⟩ := mobiusSpecialLinearProjection_surjective M
  have hpres : (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) ''
      Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc := by rw [hA]; exact hM
  refine ⟨⟨A, mem_specialUnitarySignatureOneOne_of_disc_preserving A hpres⟩, ?_⟩
  intro z
  change (mobiusSpecialLinearProjection A).val z.val = (H z).val
  rw [hA]
  exact hEq z

end LowDimensionalTopology.Geometry.Mobius
