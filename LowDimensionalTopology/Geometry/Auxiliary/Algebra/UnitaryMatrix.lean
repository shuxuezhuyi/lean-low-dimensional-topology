/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Auxiliary.Algebra.Matrix
public import LowDimensionalTopology.Geometry.Auxiliary.Algebra.Quaternion

/-!
Special unitary matrices, their quaternion characterization, and their isometric
action on the Frobenius matrix space.
-/

@[expose] public section

open scoped Matrix.Norms.Frobenius

namespace LowDimensionalTopology.Geometry.Auxiliary.Algebra

/-- The special unitary group. -/
abbrev SpecialUnitary2 := ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)

/-- Membership in the special unitary group in the norm-preserving convention. -/
theorem specialUnitary_mem_iff (A : ComplexMatrix2) :
    A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ↔ A.det = 1 ∧ UnitaryMatrix A := by
  rw [Matrix.mem_specialUnitaryGroup_iff, ← unitaryMatrix_iff_mem_unitaryGroup]
  exact and_comm

/-- The squared modulus of a unitary determinant. -/
theorem unitary_determinant_norm_sq (A : ComplexMatrix2) (hA : UnitaryMatrix A) :
    ‖A.det‖ ^ 2 = 1 := by
  have hd := congrArg Matrix.det ((unitaryMatrix_iff_mul_conjTranspose A).mp hA)
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at hd
  simpa only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.one_re,
    Complex.normSq_eq_norm_sq] using congrArg Complex.re hd

/-- The modulus of a unitary determinant. -/
theorem unitary_determinant_norm (A : ComplexMatrix2) (hA : UnitaryMatrix A) :
    ‖A.det‖ = 1 := by
  nlinarith [unitary_determinant_norm_sq A hA, norm_nonneg A.det]

/-- equation: the product with the Hermitian transpose. -/
theorem matrix_mul_conjTranspose_entries (A : ComplexMatrix2) :
    A * A.conjTranspose =
      !![((Complex.normSq (A 0 0) + Complex.normSq (A 0 1) : ℝ) : ℂ),
          A 0 0 * star (A 1 0) + A 0 1 * star (A 1 1);
        star (A 0 0) * A 1 0 + star (A 0 1) * A 1 1,
          ((Complex.normSq (A 1 0) + Complex.normSq (A 1 1) : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_conj,
      mul_comm]

/-- equation: the special-linear norm defect. -/
theorem specialLinear_matrixNorm_defect (A : ComplexMatrix2) (hA : A.det = 1) :
    ‖A 0 0 - star (A 1 1)‖ ^ 2 + ‖A 0 1 + star (A 1 0)‖ ^ 2 =
      matrixNorm A ^ 2 - 2 := by
  have hd := congrArg Complex.re hA
  rw [determinant_formula] at hd
  simp only [Complex.sub_re, Complex.mul_re, Complex.one_re] at hd
  rw [matrixNorm_sq]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
    Complex.sub_im, Complex.add_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [hd]

/-- The quaternion matrix model is equivalent to its two entry constraints. -/
theorem quaternionMatrix_range_iff_entries (A : ComplexMatrix2) :
    A ∈ Set.range quaternionMatrix ↔ A 1 1 = star (A 0 0) ∧ A 1 0 = -star (A 0 1) := by
  rw [quaternionMatrix_range]
  constructor
  · rintro ⟨z, w, rfl⟩
    simp
  · rintro ⟨hd, hc⟩
    refine ⟨A 0 0, A 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hd, hc]

/-- The unitary condition gives the norm condition. -/
theorem unitary_matrixNorm_sq (A : ComplexMatrix2) (hA : UnitaryMatrix A) :
    matrixNorm A ^ 2 = 2 := by
  have hs : matrixScalarProduct A A = (2 : ℂ) := by
    rw [matrixScalarProduct, (unitaryMatrix_iff_mul_conjTranspose A).mp hA,
      Matrix.trace_fin_two]
    norm_num
  rw [matrixScalarProduct_self] at hs
  exact_mod_cast hs

/-- The norm condition gives the quaternion condition. -/
theorem quaternion_of_matrixNorm_sq (A : ComplexMatrix2) (hA : A.det = 1)
    (hN : matrixNorm A ^ 2 = 2) : A ∈ Set.range quaternionMatrix := by
  have hsum := specialLinear_matrixNorm_defect A hA
  rw [hN, sub_self] at hsum
  have ha : A 0 0 = star (A 1 1) := by
    have hz : ‖A 0 0 - star (A 1 1)‖ = 0 := by
      nlinarith [sq_nonneg ‖A 0 1 + star (A 1 0)‖, norm_nonneg (A 0 0 - star (A 1 1))]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  have hb : A 0 1 = -star (A 1 0) := by
    have hz : ‖A 0 1 + star (A 1 0)‖ = 0 := by
      nlinarith [sq_nonneg ‖A 0 0 - star (A 1 1)‖, norm_nonneg (A 0 1 + star (A 1 0))]
    exact eq_neg_of_add_eq_zero_left (norm_eq_zero.mp hz)
  apply (quaternionMatrix_range_iff_entries A).mpr
  constructor
  · simpa using (congrArg star ha).symm
  · simpa using (congrArg (fun z : ℂ => -star z) hb).symm

/-- The quaternion condition gives unitarity. -/
theorem unitary_of_quaternion (A : ComplexMatrix2) (hA : A.det = 1)
    (hq : A ∈ Set.range quaternionMatrix) : UnitaryMatrix A := by
  obtain ⟨hd, hc⟩ := (quaternionMatrix_range_iff_entries A).mp hq
  apply (unitaryMatrix_inverse_iff A).mpr
  constructor
  · rw [hA]
    exact one_ne_zero
  · rw [inverse_formula, hA, inv_one, one_smul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hd, hc]

/-- The three equivalent descriptions. -/
theorem specialLinear_unitary_iff_norm_iff_quaternion (A : ComplexMatrix2) (hA : A.det = 1) :
    (UnitaryMatrix A ↔ matrixNorm A ^ 2 = 2) ∧
      (matrixNorm A ^ 2 = 2 ↔ A ∈ Set.range quaternionMatrix) := by
  exact ⟨⟨unitary_matrixNorm_sq A, fun h =>
      unitary_of_quaternion A hA (quaternion_of_matrixNorm_sq A hA h)⟩,
    ⟨quaternion_of_matrixNorm_sq A hA, fun h =>
      unitary_matrixNorm_sq A (unitary_of_quaternion A hA h)⟩⟩

/-- The special unitary group is the quaternion intersection. -/
theorem specialUnitary_quaternion_intersection (A : ComplexMatrix2) :
    A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ↔
      A.det = 1 ∧ A ∈ Set.range quaternionMatrix := by
  rw [specialUnitary_mem_iff]
  constructor
  · rintro ⟨hd, hu⟩
    exact ⟨hd, quaternion_of_matrixNorm_sq A hd (unitary_matrixNorm_sq A hu)⟩
  · rintro ⟨hd, hq⟩
    exact ⟨hd, unitary_of_quaternion A hd hq⟩

/-- A unitary matrix preserves the Euclidean length of row vectors. -/
theorem unitary_preserves_row_norm (A : ComplexMatrix2) (hA : UnitaryMatrix A)
    (x : EuclideanSpace ℂ (Fin 2)) :
    ‖WithLp.toLp 2 (Matrix.vecMul x.ofLp A)‖ = ‖x‖ := hA x

/-- A unitary matrix preserves the Euclidean length of column vectors. -/
theorem unitary_preserves_column_norm (A : ComplexMatrix2) (hA : UnitaryMatrix A)
    (x : EuclideanSpace ℂ (Fin 2)) :
    ‖WithLp.toLp 2 (Matrix.mulVec A x.ofLp)‖ = ‖x‖ := by
  have ht : UnitaryMatrix A.transpose :=
    (unitaryMatrix_iff_mem_unitaryGroup A.transpose).mpr
      (Matrix.transpose_mem_unitaryGroup_iff.mpr ((unitaryMatrix_iff_mem_unitaryGroup A).mp hA))
  simpa only [Matrix.vecMul_transpose] using ht x

/-- The row-vector quadratic form is preserved. -/
theorem unitary_preserves_row_quadratic (A : ComplexMatrix2) (hA : UnitaryMatrix A)
    (x : Fin 2 → ℂ) :
    ‖(Matrix.vecMul x A) 0‖ ^ 2 + ‖(Matrix.vecMul x A) 1‖ ^ 2 =
      ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
  have h := congrArg (fun r : ℝ => r ^ 2)
    (unitary_preserves_row_norm A hA (WithLp.toLp 2 x))
  simpa only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, PiLp.toLp_apply] using h

/-- The scalar product determines the nonnegative Frobenius norm. -/
theorem matrixNorm_eq_of_scalarProduct_self_eq {A B : ComplexMatrix2}
    (h : matrixScalarProduct A A = matrixScalarProduct B B) : matrixNorm A = matrixNorm B := by
  apply (sq_eq_sq₀ (matrixNorm_nonneg A) (matrixNorm_nonneg B)).mp
  rw [matrixScalarProduct_self, matrixScalarProduct_self] at h
  exact_mod_cast h

/-- right multiplication by a unitary matrix preserves Frobenius norm. -/
theorem unitary_matrixNorm_mul_right (A X : ComplexMatrix2) (hA : UnitaryMatrix A) :
    matrixNorm (X * A) = matrixNorm X := by
  apply matrixNorm_eq_of_scalarProduct_self_eq
  simp only [matrixScalarProduct, Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc X A (A.conjTranspose * X.conjTranspose),
    ← Matrix.mul_assoc A A.conjTranspose X.conjTranspose,
    (unitaryMatrix_iff_mul_conjTranspose A).mp hA, Matrix.one_mul]

/-- left multiplication by a unitary matrix preserves Frobenius norm. -/
theorem unitary_matrixNorm_mul_left (A X : ComplexMatrix2) (hA : UnitaryMatrix A) :
    matrixNorm (A * X) = matrixNorm X := by
  have ha : A.conjTranspose * A = 1 :=
    mul_eq_one_comm.mp ((unitaryMatrix_iff_mul_conjTranspose A).mp hA)
  apply matrixNorm_eq_of_scalarProduct_self_eq
  simp only [matrixScalarProduct, Matrix.conjTranspose_mul]
  rw [Matrix.trace_mul_comm (A * X) (X.conjTranspose * A.conjTranspose),
    Matrix.mul_assoc X.conjTranspose A.conjTranspose (A * X),
    ← Matrix.mul_assoc A.conjTranspose A X, ha, Matrix.one_mul,
    Matrix.trace_mul_comm X.conjTranspose X]

/-- A unitary matrix has a unitary inverse. -/
theorem unitary_inverse (A : ComplexMatrix2) (hA : UnitaryMatrix A) : UnitaryMatrix A⁻¹ := by
  have hi := ((unitaryMatrix_inverse_iff A).mp hA).2
  rw [hi]
  apply (unitaryMatrix_iff_mul_conjTranspose A.conjTranspose).mpr
  simpa only [Matrix.conjTranspose_conjTranspose] using
    mul_eq_one_comm.mp ((unitaryMatrix_iff_mul_conjTranspose A).mp hA)

/-- unitary conjugation preserves Frobenius norm. -/
theorem unitary_matrixNorm_conjugation (A X : ComplexMatrix2) (hA : UnitaryMatrix A) :
    matrixNorm (A * X * A⁻¹) = matrixNorm X := by
  rw [unitary_matrixNorm_mul_right A⁻¹ (A * X) (unitary_inverse A hA),
    unitary_matrixNorm_mul_left A X hA]

/-- unitary conjugation preserves the matrix metric. -/
theorem unitary_conjugation_distance (A X Y : ComplexMatrix2) (hA : UnitaryMatrix A) :
    matrixDistance (A * X * A⁻¹) (A * Y * A⁻¹) = matrixDistance X Y := by
  simpa only [matrixDistance, mul_sub, sub_mul] using
    unitary_matrixNorm_conjugation A (X - Y) hA

/-- Conjugation by an invertible matrix is a bijection of the complete matrix space. -/
noncomputable def matrixConjugationEquiv (A : ComplexMatrix2) (hA : A.det ≠ 0) :
    ComplexMatrix2 ≃ ComplexMatrix2 where
  toFun X := A * X * A⁻¹
  invFun X := A⁻¹ * X * A
  left_inv X := by
    calc
      A⁻¹ * (A * X * A⁻¹) * A = (A⁻¹ * A) * X * (A⁻¹ * A) := by simp only [mul_assoc]
      _ = X := by rw [A.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hA), one_mul, mul_one]
  right_inv X := by
    calc
      A * (A⁻¹ * X * A) * A⁻¹ = (A * A⁻¹) * X * (A * A⁻¹) := by simp only [mul_assoc]
      _ = X := by rw [A.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hA), one_mul, mul_one]

/-- A unitary matrix gives an isometric bijection of the Frobenius matrix space. -/
noncomputable def unitaryConjugationIsometry (A : ComplexMatrix2) (hA : UnitaryMatrix A) :
    ComplexMatrix2 ≃ᵢ ComplexMatrix2 where
  toEquiv := matrixConjugationEquiv A ((unitaryMatrix_inverse_iff A).mp hA).1
  isometry_toFun := isometry_iff_dist_eq.mpr fun X Y => by
    simpa only [matrixConjugationEquiv, matrixDistance_eq_dist] using
      unitary_conjugation_distance A X Y hA

/-- special unitary conjugation is an isometry onto matrix space. -/
noncomputable def specialUnitaryConjugationIsometry (A : SpecialUnitary2) : ComplexMatrix2 ≃ᵢ ComplexMatrix2 :=
  unitaryConjugationIsometry A ((specialUnitary_mem_iff A).mp A.property).2

/-- The isometry is the stated conjugation map. -/
theorem specialUnitaryConjugationIsometry_apply (A : SpecialUnitary2) (X : ComplexMatrix2) :
    specialUnitaryConjugationIsometry A X = (A : ComplexMatrix2) * X * (A : ComplexMatrix2)⁻¹ := rfl

end LowDimensionalTopology.Geometry.Auxiliary.Algebra
