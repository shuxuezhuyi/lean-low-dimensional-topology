/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Auxiliary.Algebra.Matrix
public import LowDimensionalTopology.Geometry.Mobius.FractionalLinear
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
The matrix projection to the actual group of extended fractional linear
permutations. Identifying this group with the reflection-generated group
requires the separate geometric generation theorem.
-/

@[expose] public section

namespace LowDimensionalTopology.Geometry.Mobius

open LowDimensionalTopology.Geometry.Auxiliary.Algebra
open scoped OnePoint

/-- The matrix formula for the squared trace. -/
noncomputable def matrixSquaredTrace (A : Auxiliary.Algebra.ComplexMatrix2) : ℂ := A.trace ^ 2 / A.det

/-- The normalized Frobenius norm. -/
noncomputable def matrixNormalizedNorm (A : Auxiliary.Algebra.ComplexMatrix2) : ℝ :=
  Auxiliary.Algebra.matrixNorm A / Real.sqrt ‖A.det‖

/-- The absolute trace is the nonnegative square root of the modulus of the squared trace. -/
noncomputable def matrixTraceAbs (A : Auxiliary.Algebra.ComplexMatrix2) : ℝ := Real.sqrt ‖matrixSquaredTrace A‖

/-- The squared trace is unchanged by nonzero scalar multiplication. -/
theorem matrixSquaredTrace_scalar (A : Auxiliary.Algebra.ComplexMatrix2) (c : ℂ) (hc : c ≠ 0) :
    matrixSquaredTrace (c • A) = matrixSquaredTrace A := by
  unfold matrixSquaredTrace
  rw [Matrix.trace_smul, Matrix.det_smul]
  simp only [Fintype.card_fin, smul_eq_mul, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hc)

/-- The normalized Frobenius norm is unchanged by nonzero scalar multiplication. -/
theorem matrixNormalizedNorm_scalar (A : Auxiliary.Algebra.ComplexMatrix2) (c : ℂ) (hc : c ≠ 0) :
    matrixNormalizedNorm (c • A) = matrixNormalizedNorm A := by
  unfold matrixNormalizedNorm
  rw [Auxiliary.Algebra.matrixNorm_scalar, Matrix.det_smul]
  simp only [Fintype.card_fin, norm_mul, norm_pow]
  rw [Real.sqrt_mul (sq_nonneg ‖c‖), Real.sqrt_sq (norm_nonneg c)]
  exact mul_div_mul_left _ _ (norm_ne_zero_iff.mpr hc)

/-- The squared trace is invariant under matrix conjugation. -/
theorem matrixSquaredTrace_conjugation (A B : Auxiliary.Algebra.ComplexMatrix2) (hB : Auxiliary.Algebra.Nonsingular B) :
    matrixSquaredTrace (B * A * B⁻¹) = matrixSquaredTrace A := by
  unfold matrixSquaredTrace
  rw [Auxiliary.Algebra.trace_conjugation A B hB, Auxiliary.Algebra.determinant_conjugate A B hB]

/-- projection to the actual group of fractional linear permutations. -/
noncomputable def matrixProjection : FractionalLinearMatrix →* fractionalLinearGroup :=
  fractionalLinearHom.rangeRestrict

/-- Every element of the represented transformation group has a matrix representative. -/
theorem matrixProjection_surjective : Function.Surjective matrixProjection :=
  fractionalLinearHom.rangeRestrict_surjective

/-- The projection has the extended fractional linear action as its underlying permutation. -/
theorem matrixProjection_apply (A : FractionalLinearMatrix) :
    (matrixProjection A : Equiv.Perm ExtendedComplex) = fractionalLinear A := rfl

/-- A nonzero scalar matrix fixes every point of the extended plane. -/
theorem fractionalLinear_scalar (u : ℂˣ) (z : ExtendedComplex) :
    fractionalLinear (Matrix.GeneralLinearGroup.scalar (Fin 2) u) z = z := by
  cases z using OnePoint.rec with
  | infty =>
    simp [fractionalLinear_infty, Matrix.GeneralLinearGroup.scalar, Matrix.scalar]
  | coe z =>
    simp [fractionalLinear_coe, Matrix.GeneralLinearGroup.scalar, Matrix.scalar, u.ne_zero]

/-- Scalar matrices belong to the kernel of the matrix projection. -/
theorem matrixProjection_scalar (u : ℂˣ) :
    matrixProjection (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  exact fractionalLinear_scalar u

/-- exactly the nonzero scalar matrices act trivially. -/
theorem matrixProjection_eq_one_iff (g : FractionalLinearMatrix) :
    matrixProjection g = 1 ↔ ∃ u : ℂˣ, g = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  constructor
  · intro hg
    have hfix (z : ExtendedComplex) : g • z = z := by
      have hp := congrArg (fun f : fractionalLinearGroup => (f : Equiv.Perm ExtendedComplex) z) hg
      exact hp
    have hc : g 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.mp (hfix ∞)
    have hd : g 1 1 ≠ 0 := by
      have hdet := g.det_ne_zero
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
      exact (mul_ne_zero_iff.mp hdet).2
    have hb : g 0 1 = 0 := by
      have hzero := hfix ((0 : ℂ) : ExtendedComplex)
      simpa [OnePoint.smul_some_eq_ite, hc, hd] using hzero
    have ha : g 0 0 = g 1 1 := by
      have hone := hfix ((1 : ℂ) : ExtendedComplex)
      simpa [OnePoint.smul_some_eq_ite, hc, hd, hb, div_eq_iff hd] using hone
    refine ⟨Units.mk0 (g 1 1) hd, ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, hc, hb, ha]
  · rintro ⟨u, rfl⟩
    exact matrixProjection_scalar u

/-- The kernel is the center of the general linear group. -/
theorem matrixProjection_kernel : matrixProjection.ker = Subgroup.center FractionalLinearMatrix := by
  ext g
  rw [MonoidHom.mem_ker, matrixProjection_eq_one_iff,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨fun ⟨u, hu⟩ => ⟨u, hu.symm⟩, fun ⟨u, hu⟩ => ⟨u, hu.symm⟩⟩

/-- The quotient by scalar matrices is the actual fractional linear permutation group. -/
noncomputable def projectiveFractionalEquiv :
    Matrix.ProjGenLinGroup (Fin 2) ℂ ≃* fractionalLinearGroup :=
  QuotientGroup.liftEquiv (Subgroup.center FractionalLinearMatrix)
    matrixProjection_surjective matrixProjection_kernel.symm

/-- The quotient equivalence is induced by the matrix projection. -/
theorem projectiveFractionalEquiv_mk (g : FractionalLinearMatrix) :
    projectiveFractionalEquiv (Matrix.ProjGenLinGroup.mk g) = matrixProjection g := rfl

/-- Two matrices represent the same map exactly when they differ by a nonzero scalar. -/
theorem matrixProjection_eq_iff (A B : FractionalLinearMatrix) :
    matrixProjection A = matrixProjection B ↔
      ∃ u : ℂˣ, A * Matrix.GeneralLinearGroup.scalar (Fin 2) u = B := by
  change projectiveFractionalEquiv (Matrix.ProjGenLinGroup.mk A) =
      projectiveFractionalEquiv (Matrix.ProjGenLinGroup.mk B) ↔ _
  rw [projectiveFractionalEquiv.injective.eq_iff, Matrix.ProjGenLinGroup.mk_eq_mk_iff]

/-- Multiplication by a scalar matrix is scalar multiplication of its coefficient matrix. -/
theorem generalLinear_mul_scalar_val (g : FractionalLinearMatrix) (u : ℂˣ) :
    ((g * Matrix.GeneralLinearGroup.scalar (Fin 2) u : FractionalLinearMatrix) : Auxiliary.Algebra.ComplexMatrix2) =
      (u : ℂ) • (g : Auxiliary.Algebra.ComplexMatrix2) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, mul_comm]

/-- The normalized trace formula is independent of the matrix representative. -/
theorem matrixSquaredTrace_eq_of_projection_eq (A B : FractionalLinearMatrix)
    (h : matrixProjection A = matrixProjection B) :
    matrixSquaredTrace A = matrixSquaredTrace B := by
  obtain ⟨u, rfl⟩ := (matrixProjection_eq_iff A B).mp h
  rw [generalLinear_mul_scalar_val, matrixSquaredTrace_scalar _ _ u.ne_zero]

/-- The normalized norm formula is independent of the matrix representative. -/
theorem matrixNormalizedNorm_eq_of_projection_eq (A B : FractionalLinearMatrix)
    (h : matrixProjection A = matrixProjection B) :
    matrixNormalizedNorm A = matrixNormalizedNorm B := by
  obtain ⟨u, rfl⟩ := (matrixProjection_eq_iff A B).mp h
  rw [generalLinear_mul_scalar_val, matrixNormalizedNorm_scalar _ _ u.ne_zero]

/-- A representative is used only through quantities proved independent of that choice. -/
noncomputable def fractionalRepresentative (f : fractionalLinearGroup) : FractionalLinearMatrix :=
  Classical.choose (matrixProjection_surjective f)

/-- The chosen matrix represents the specified fractional linear permutation. -/
theorem fractionalRepresentative_spec (f : fractionalLinearGroup) :
    matrixProjection (fractionalRepresentative f) = f :=
  Classical.choose_spec (matrixProjection_surjective f)

/-- The squared trace descends to the group of fractional linear permutations. -/
noncomputable def fractionalSquaredTrace (f : fractionalLinearGroup) : ℂ :=
  matrixSquaredTrace (fractionalRepresentative f)

/-- The normalized Frobenius norm on the represented transformation group. -/
noncomputable def fractionalNormalizedNorm (f : fractionalLinearGroup) : ℝ :=
  matrixNormalizedNorm (fractionalRepresentative f)

/-- The absolute trace of a represented transformation. -/
noncomputable def fractionalTraceAbs (f : fractionalLinearGroup) : ℝ :=
  Real.sqrt ‖fractionalSquaredTrace f‖

/-- Any matrix representative computes the descended squared trace. -/
theorem fractionalSquaredTrace_projection (g : FractionalLinearMatrix) :
    fractionalSquaredTrace (matrixProjection g) = matrixSquaredTrace g := by
  exact matrixSquaredTrace_eq_of_projection_eq _ _ (fractionalRepresentative_spec _)

/-- Any matrix representative computes the descended normalized norm. -/
theorem fractionalNormalizedNorm_projection (g : FractionalLinearMatrix) :
    fractionalNormalizedNorm (matrixProjection g) = matrixNormalizedNorm g := by
  exact matrixNormalizedNorm_eq_of_projection_eq _ _ (fractionalRepresentative_spec _)

/-- squared trace is invariant under conjugation. -/
theorem fractionalSquaredTrace_conjugation (f h : fractionalLinearGroup) :
    fractionalSquaredTrace (h * f * h⁻¹) = fractionalSquaredTrace f := by
  obtain ⟨A, rfl⟩ := matrixProjection_surjective f
  obtain ⟨B, rfl⟩ := matrixProjection_surjective h
  rw [← map_inv, ← map_mul, ← map_mul, fractionalSquaredTrace_projection,
    fractionalSquaredTrace_projection]
  simpa only [Units.val_mul, Matrix.coe_units_inv] using
    matrixSquaredTrace_conjugation A B B.det_ne_zero

/-- Restriction of the matrix projection to the special linear group. -/
noncomputable def specialLinearProjection : Auxiliary.Algebra.SpecialLinear2 →* fractionalLinearGroup :=
  matrixProjection.comp Matrix.SpecialLinearGroup.toGL

/-- Over the complex numbers every represented transformation has a determinant-one matrix. -/
theorem specialLinearProjection_surjective : Function.Surjective specialLinearProjection := by
  intro f
  obtain ⟨g, rfl⟩ := matrixProjection_surjective f
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ((g : Auxiliary.Algebra.ComplexMatrix2).det)⁻¹ zero_lt_two
  have hc0 : c ≠ 0 := by
    intro hz
    have hd : (g : Auxiliary.Algebra.ComplexMatrix2).det⁻¹ = 0 := by rw [← hc, hz]; norm_num
    exact g.det_ne_zero (inv_eq_zero.mp hd)
  let A : Auxiliary.Algebra.SpecialLinear2 := ⟨c • (g : Auxiliary.Algebra.ComplexMatrix2), by
    rw [Matrix.det_smul, Fintype.card_fin, hc, inv_mul_cancel₀ g.det_ne_zero]⟩
  refine ⟨A, ?_⟩
  change matrixProjection (Matrix.SpecialLinearGroup.toGL A) = matrixProjection g
  symm
  apply (matrixProjection_eq_iff g _).mpr
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  rw [generalLinear_mul_scalar_val]
  rfl

/-- Determinant-one representatives differ by exactly a sign. -/
theorem specialLinear_same_projection_iff (A B : Auxiliary.Algebra.SpecialLinear2) :
    specialLinearProjection A = specialLinearProjection B ↔
      (B : Auxiliary.Algebra.ComplexMatrix2) = A ∨ (B : Auxiliary.Algebra.ComplexMatrix2) = -(A :
        Auxiliary.Algebra.ComplexMatrix2) := by
  change matrixProjection (Matrix.SpecialLinearGroup.toGL A) =
      matrixProjection (Matrix.SpecialLinearGroup.toGL B) ↔ _
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (matrixProjection_eq_iff _ _).mp h
    have hv := congrArg (fun g : FractionalLinearMatrix => (g : Auxiliary.Algebra.ComplexMatrix2)) hu
    rw [generalLinear_mul_scalar_val] at hv
    change (u : ℂ) • (A : Auxiliary.Algebra.ComplexMatrix2) = (B : Auxiliary.Algebra.ComplexMatrix2) at hv
    have hd := congrArg Matrix.det hv
    rw [Matrix.det_smul, Fintype.card_fin, A.det_coe, B.det_coe, mul_one] at hd
    rcases sq_eq_one_iff.mp hd with hpos | hneg
    · left
      simpa only [hpos, one_smul] using hv.symm
    · right
      simpa only [hneg, neg_one_smul] using hv.symm
  · rintro (hpos | hneg)
    · have hAB : B = A := Subtype.ext hpos
      rw [hAB]
    · apply (matrixProjection_eq_iff _ _).mpr
      refine ⟨Units.mk0 (-1 : ℂ) (by norm_num), ?_⟩
      apply Units.ext
      rw [generalLinear_mul_scalar_val]
      simpa only [Units.val_mk0, neg_one_smul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
        using hneg.symm

/-- The restricted kernel consists of the two scalar sign matrices. -/
theorem specialLinearProjection_eq_one_iff (A : Auxiliary.Algebra.SpecialLinear2) :
    specialLinearProjection A = 1 ↔
      (A : Auxiliary.Algebra.ComplexMatrix2) = 1 ∨ (A : Auxiliary.Algebra.ComplexMatrix2) = -1 := by
  simpa only [map_one, Matrix.SpecialLinearGroup.coe_one, eq_comm] using
    specialLinear_same_projection_iff 1 A

/-- The kernel of the restricted projection is the center of the special linear group. -/
theorem specialLinearProjection_kernel :
    specialLinearProjection.ker = Subgroup.center Auxiliary.Algebra.SpecialLinear2 := by
  ext A
  rw [MonoidHom.mem_ker]
  change matrixProjection (Matrix.SpecialLinearGroup.toGL A) = 1 ↔ _
  rw [← MonoidHom.mem_ker, matrixProjection_kernel,
    Matrix.SpecialLinearGroup.toGL_mem_center_iff]

/-- The represented transformation group is also the projective special linear quotient. -/
noncomputable def projectiveSpecialFractionalEquiv :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ ≃* fractionalLinearGroup :=
  QuotientGroup.liftEquiv (Subgroup.center Auxiliary.Algebra.SpecialLinear2)
    specialLinearProjection_surjective specialLinearProjection_kernel.symm

/-- Every represented transformation has exactly two distinct determinant-one representatives. -/
theorem specialLinear_exactly_two_representatives (f : fractionalLinearGroup) :
    ∃ A B : Auxiliary.Algebra.SpecialLinear2, A ≠ B ∧ specialLinearProjection A = f ∧
      specialLinearProjection B = f ∧
      ∀ C : Auxiliary.Algebra.SpecialLinear2, specialLinearProjection C = f ↔ C = A ∨ C = B := by
  obtain ⟨A, hA⟩ := specialLinearProjection_surjective f
  let B : Auxiliary.Algebra.SpecialLinear2 := ⟨-(A : Auxiliary.Algebra.ComplexMatrix2), by
    rw [Matrix.det_neg, Fintype.card_fin, A.det_coe]
    norm_num⟩
  have hAB : specialLinearProjection A = specialLinearProjection B :=
    (specialLinear_same_projection_iff A B).mpr (Or.inr rfl)
  have hB : specialLinearProjection B = f := hAB.symm.trans hA
  refine ⟨A, B, ?_, hA, hB, ?_⟩
  · intro h
    have hm : (A : Auxiliary.Algebra.ComplexMatrix2) = -(A : Auxiliary.Algebra.ComplexMatrix2) := congrArg Subtype.val h
    have hz : (A : Auxiliary.Algebra.ComplexMatrix2) = 0 := by
      ext i j
      have hij := congrArg (fun M : Auxiliary.Algebra.ComplexMatrix2 => M i j) hm
      exact CharZero.eq_neg_self_iff.mp hij
    have hd := A.det_coe
    simp [hz] at hd
  · intro C
    constructor
    · intro hC
      have hAC : specialLinearProjection A = specialLinearProjection C := hA.trans hC.symm
      rcases (specialLinear_same_projection_iff A C).mp hAC with heq | hneg
      · exact Or.inl (Subtype.ext heq)
      · exact Or.inr (Subtype.ext hneg)
    · rintro (rfl | rfl)
      · exact hA
      · exact hB

/-- On determinant-one representatives the squared-trace denominator disappears. -/
theorem matrixSquaredTrace_specialLinear (A : Auxiliary.Algebra.SpecialLinear2) :
    matrixSquaredTrace A = (A : Auxiliary.Algebra.ComplexMatrix2).trace ^ 2 := by
  simp only [matrixSquaredTrace, A.det_coe, div_one]

/-- On determinant-one representatives the normalized norm is the Frobenius norm. -/
theorem matrixNormalizedNorm_specialLinear (A : Auxiliary.Algebra.SpecialLinear2) :
    matrixNormalizedNorm A = Auxiliary.Algebra.matrixNorm A := by
  simp only [matrixNormalizedNorm, A.det_coe, norm_one, Real.sqrt_one, div_one]

/-- The determinant-one formula computes the descended squared trace. -/
theorem fractionalSquaredTrace_specialLinearProjection (A : Auxiliary.Algebra.SpecialLinear2) :
    fractionalSquaredTrace (specialLinearProjection A) = (A : Auxiliary.Algebra.ComplexMatrix2).trace ^ 2 := by
  change fractionalSquaredTrace (matrixProjection (Matrix.SpecialLinearGroup.toGL A)) = _
  rw [fractionalSquaredTrace_projection]
  exact matrixSquaredTrace_specialLinear A

/-- The determinant-one formula computes the descended normalized norm. -/
theorem fractionalNormalizedNorm_specialLinearProjection (A : Auxiliary.Algebra.SpecialLinear2) :
    fractionalNormalizedNorm (specialLinearProjection A) = Auxiliary.Algebra.matrixNorm A := by
  change fractionalNormalizedNorm (matrixProjection (Matrix.SpecialLinearGroup.toGL A)) = _
  rw [fractionalNormalizedNorm_projection]
  exact matrixNormalizedNorm_specialLinear A

end LowDimensionalTopology.Geometry.Mobius
