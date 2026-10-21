/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
Basic matrix groups and their determinant, trace, and Frobenius norm.
-/

@[expose] public section

open scoped Matrix.Norms.Frobenius

namespace LowDimensionalTopology.Geometry.Auxiliary.Algebra

/-- The matrices used. -/
abbrev ComplexMatrix2 := Matrix (Fin 2) (Fin 2) ℂ

/-- nonsingularity. -/
def Nonsingular (A : ComplexMatrix2) : Prop := A.det ≠ 0

/-- The general linear group. -/
abbrev GeneralLinear2 := Matrix.GeneralLinearGroup (Fin 2) ℂ

/-- The special linear group. -/
abbrev SpecialLinear2 := Matrix.SpecialLinearGroup (Fin 2) ℂ

/-- The Euclidean length of a complex vector. -/
noncomputable def complexVectorNorm {n : ℕ} (z : Fin n → ℂ) : ℝ := ‖WithLp.toLp 2 z‖

/-- The Euclidean length is the square root of the sum of squared component lengths. -/
theorem complexVectorNorm_formula {n : ℕ} (z : Fin n → ℂ) :
    complexVectorNorm z = Real.sqrt (∑ i, ‖z i‖ ^ 2) := by
  exact PiLp.norm_eq_of_L2 _

/-- A real matrix is orthogonal when right multiplication preserves length. -/
def OrthogonalMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n), ‖WithLp.toLp 2 (Matrix.vecMul x.ofLp A)‖ = ‖x‖

/-- The class denoted by O(n). -/
def OrthogonalMatrices (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | OrthogonalMatrix A}

/-- A complex matrix is unitary when right multiplication preserves length. -/
def UnitaryMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ z : EuclideanSpace ℂ (Fin n), ‖WithLp.toLp 2 (Matrix.vecMul z.ofLp A)‖ = ‖z‖

/-- The identity matrix of any finite dimension. -/
def matrixIdentity (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := 1

/-- The determinant in any finite dimension. -/
abbrev matrixDeterminant {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℂ := A.det

/-- matrix transpose. -/
abbrev transposeMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) := A.transpose

/-- entrywise complex conjugation. -/
def conjugateMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) := A.map (starRingEnd ℂ)

/-- invertibility in general finite dimension. -/
theorem general_nonsingular_iff_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A.det ≠ 0 ↔ IsUnit A := by
  simp [Matrix.isUnit_iff_isUnit_det]

/-- The two inverse identities in general finite dimension. -/
theorem general_inverse_identities {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0) :
    A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 :=
  ⟨A.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hA),
    A.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hA)⟩

/-- determinant multiplicativity in general finite dimension. -/
theorem general_determinant_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A * B).det = A.det * B.det := Matrix.det_mul A B

/-- determinant conjugation invariance in general finite dimension. -/
theorem general_determinant_conjugation {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hB : B.det ≠ 0) : (B * A * B⁻¹).det = A.det :=
  Matrix.det_conj ((general_nonsingular_iff_isUnit B).mp hB) A

/-- The usual complex vector-space structure on matrices. -/
abbrev complexMatricesModule : Module ℂ ComplexMatrix2 := inferInstance

/-- A scalar product produces a normed additive group. -/
@[instance_reducible]
noncomputable def scalarProductNormedGroup {E : Type*} [AddCommGroup E] [Module ℂ E]
    (c : InnerProductSpace.Core ℂ E) : NormedAddCommGroup E := by
  letI := c
  exact InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

/-- The metric induced by a scalar product. -/
@[instance_reducible]
noncomputable def scalarProductMetric {E : Type*} [AddCommGroup E] [Module ℂ E]
    (c : InnerProductSpace.Core ℂ E) : MetricSpace E := by
  letI := scalarProductNormedGroup c
  infer_instance

/-- The determinant of a two by two matrix. -/
theorem determinant_formula (A : ComplexMatrix2) :
    A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A

/-- nonsingularity is equivalent to multiplicative invertibility. -/
theorem nonsingular_iff_isUnit (A : ComplexMatrix2) : Nonsingular A ↔ IsUnit A := by
  simp [Nonsingular, Matrix.isUnit_iff_isUnit_det]


theorem determinant_mul (A B : ComplexMatrix2) : (A * B).det = A.det * B.det :=
  Matrix.det_mul A B

/-- equation: reversing the factors leaves the determinant unchanged. -/
theorem determinant_mul_comm (A B : ComplexMatrix2) : (A * B).det = (B * A).det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm]


theorem determinant_conjugate (A B : ComplexMatrix2) (hB : Nonsingular B) :
    (B * A * B⁻¹).det = A.det :=
  Matrix.det_conj ((nonsingular_iff_isUnit B).mp hB) A

/-- A nonsingular matrix multiplied by its inverse is the identity. -/
theorem matrix_mul_inverse (A : ComplexMatrix2) (hA : Nonsingular A) : A * A⁻¹ = 1 :=
  A.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hA)

/-- The inverse is also a left inverse. -/
theorem matrix_inverse_mul (A : ComplexMatrix2) (hA : Nonsingular A) : A⁻¹ * A = 1 :=
  A.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hA)

/-- The inverse of a nonsingular matrix is nonsingular. -/
theorem nonsingular_inverse (A : ComplexMatrix2) (hA : Nonsingular A) : Nonsingular A⁻¹ := by
  exact isUnit_iff_ne_zero.mp (A.isUnit_nonsing_inv_det (isUnit_iff_ne_zero.mpr hA))

/-- The explicit inverse formula. -/
theorem inverse_formula (A : ComplexMatrix2) :
    A⁻¹ = A.det⁻¹ • !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two]

/-- The trace. -/
theorem trace_formula (A : ComplexMatrix2) : A.trace = A 0 0 + A 1 1 := Matrix.trace_fin_two A

/-- trace is unchanged by interchanging two factors. -/
theorem trace_mul_comm (A B : ComplexMatrix2) : (A * B).trace = (B * A).trace :=
  Matrix.trace_mul_comm A B

/-- trace is invariant under conjugation. -/
theorem trace_conjugation (A B : ComplexMatrix2) (hB : Nonsingular B) :
    (B * A * B⁻¹).trace = A.trace :=
  Matrix.trace_conj ((nonsingular_iff_isUnit B).mp hB) A

/-- trace respects scalar multiplication. -/
theorem trace_scalar (c : ℂ) (A : ComplexMatrix2) : (c • A).trace = c * A.trace :=
  Matrix.trace_smul c A

/-- transpose preserves trace. -/
theorem trace_transpose (A : ComplexMatrix2) : A.transpose.trace = A.trace :=
  Matrix.trace_transpose A

/-- equation: the Hermitian transpose. -/
abbrev hermitianTranspose (A : ComplexMatrix2) : ComplexMatrix2 := A.conjTranspose

/-- The scalar product, linear in its first argument. -/
def matrixScalarProduct (A B : ComplexMatrix2) : ℂ := (A * B.conjTranspose).trace

/-- The Frobenius norm, rather than the operator norm. -/
noncomputable def matrixNorm (A : ComplexMatrix2) : ℝ := ‖A‖

/-- The defining expression for the Frobenius norm. -/
theorem matrixNorm_formula (A : ComplexMatrix2) :
    matrixNorm A = Real.sqrt (‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 +
      ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) := by
  rw [matrixNorm, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp [Fin.sum_univ_two, add_assoc]

/-- nonnegativity. -/
theorem matrixNorm_nonneg (A : ComplexMatrix2) : 0 ≤ matrixNorm A := norm_nonneg A

/-- definiteness. -/
theorem matrixNorm_eq_zero_iff (A : ComplexMatrix2) : matrixNorm A = 0 ↔ A = 0 := norm_eq_zero

/-- absolute homogeneity. -/
theorem matrixNorm_scalar (c : ℂ) (A : ComplexMatrix2) :
    matrixNorm (c • A) = ‖c‖ * matrixNorm A := norm_smul c A

/-- The triangle inequality. -/
theorem matrixNorm_add_le (A B : ComplexMatrix2) :
    matrixNorm (A + B) ≤ matrixNorm A + matrixNorm B := norm_add_le A B

/-- submultiplicativity of the Frobenius norm. -/
theorem matrixNorm_mul_le (A B : ComplexMatrix2) :
    matrixNorm (A * B) ≤ matrixNorm A * matrixNorm B := Matrix.frobenius_norm_mul A B

/-- The square of the Frobenius norm is the sum of the squared entry norms. -/
theorem matrixNorm_sq (A : ComplexMatrix2) :
    matrixNorm A ^ 2 = ‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 +
      ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2 := by
  rw [matrixNorm_formula, Real.sq_sqrt]
  positivity

/-- The entrywise expression for the scalar product. -/
theorem matrixScalarProduct_formula (A B : ComplexMatrix2) :
    matrixScalarProduct A B = A 0 0 * star (B 0 0) + A 0 1 * star (B 0 1) +
      A 1 0 * star (B 1 0) + A 1 1 * star (B 1 1) := by
  simp [matrixScalarProduct, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    add_assoc]

/-- linearity in the first argument. -/
theorem matrixScalarProduct_linear (c d : ℂ) (A B C : ComplexMatrix2) :
    matrixScalarProduct (c • A + d • B) C =
      c * matrixScalarProduct A C + d * matrixScalarProduct B C := by
  simp [matrixScalarProduct, Matrix.add_mul, Matrix.trace_add,
    Matrix.trace_smul]

/-- Hermitian symmetry. -/
theorem matrixScalarProduct_symm (A B : ComplexMatrix2) :
    matrixScalarProduct B A = star (matrixScalarProduct A B) := by
  simpa [matrixScalarProduct, Matrix.conjTranspose_mul] using
    Matrix.trace_conjTranspose (A * B.conjTranspose)

/-- The scalar product of a matrix with itself equals its squared Frobenius norm. -/
theorem matrixScalarProduct_self (A : ComplexMatrix2) :
    matrixScalarProduct A A = (matrixNorm A ^ 2 : ℝ) := by
  rw [matrixNorm_sq, matrixScalarProduct_formula]
  simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_add]

/-- The scalar product with itself is nonnegative and real. -/
theorem matrixScalarProduct_self_nonneg (A : ComplexMatrix2) :
    0 ≤ (matrixScalarProduct A A).re ∧ (matrixScalarProduct A A).im = 0 := by
  rw [matrixScalarProduct_self]
  constructor
  · simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using sq_nonneg (matrixNorm A)
  · simp only [Complex.ofReal_im]

/-- definiteness of the scalar product. -/
theorem matrixScalarProduct_self_eq_zero_iff (A : ComplexMatrix2) :
    matrixScalarProduct A A = 0 ↔ A = 0 := by
  rw [matrixScalarProduct_self]
  simp [matrixNorm_eq_zero_iff]

/-- The scalar product induces the stated norm. -/
theorem matrixNorm_eq_sqrt_scalarProduct (A : ComplexMatrix2) :
    matrixNorm A = Real.sqrt (matrixScalarProduct A A).re := by
  rw [matrixScalarProduct_self]
  simp only [Complex.ofReal_re]
  exact (Real.sqrt_sq (matrixNorm_nonneg A)).symm

/-- Entry vectors provide the Euclidean model of the matrix scalar product. -/
noncomputable def matrixEntryVector (A : ComplexMatrix2) :
    EuclideanSpace ℂ (Fin 2 × Fin 2) := WithLp.toLp 2 (fun ij => A ij.1 ij.2)

/-- The Euclidean entry-vector norm agrees with the Frobenius norm. -/
theorem matrixEntryVector_norm (A : ComplexMatrix2) : ‖matrixEntryVector A‖ = matrixNorm A := by
  rw [matrixNorm_formula]
  simp [matrixEntryVector, PiLp.norm_eq_of_L2, Fintype.sum_prod_type, Fin.sum_univ_two,
    add_assoc]

/-- Our convention is linear in the first entry, reversing Mathlib's inner arguments. -/
theorem matrixScalarProduct_eq_inner (A B : ComplexMatrix2) :
    matrixScalarProduct A B = inner ℂ (matrixEntryVector B) (matrixEntryVector A) := by
  simp [matrixScalarProduct_formula, matrixEntryVector, PiLp.inner_apply,
    RCLike.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_two, add_assoc]

/-- The scalar-product inequality. -/
theorem matrixScalarProduct_norm_le (A B : ComplexMatrix2) :
    ‖matrixScalarProduct A B‖ ≤ matrixNorm A * matrixNorm B := by
  rw [matrixScalarProduct_eq_inner]
  simpa [matrixEntryVector_norm, mul_comm] using
    norm_inner_le_norm (matrixEntryVector B) (matrixEntryVector A)

/-- The adjugate preserves the Frobenius norm for two by two matrices. -/
theorem matrixNorm_adjugate (A : ComplexMatrix2) : matrixNorm A.adjugate = matrixNorm A := by
  simp [Matrix.adjugate_fin_two, matrixNorm_formula, add_comm, add_left_comm, add_assoc]

/-- The norm of the inverse. -/
theorem matrixNorm_inverse (A : ComplexMatrix2) (hA : Nonsingular A) :
    ‖A.det‖ * matrixNorm A⁻¹ = matrixNorm A := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, matrixNorm_scalar, norm_inv, matrixNorm_adjugate,
    ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hA), one_mul]

/-- The determinant bound. -/
theorem determinant_norm_le (A : ComplexMatrix2) : 2 * ‖A.det‖ ≤ matrixNorm A ^ 2 := by
  have hdet : ‖A.det‖ ≤ ‖A 0 0‖ * ‖A 1 1‖ + ‖A 0 1‖ * ‖A 1 0‖ := by
    rw [determinant_formula]
    simpa only [norm_mul] using norm_sub_le (A 0 0 * A 1 1) (A 0 1 * A 1 0)
  rw [matrixNorm_sq]
  nlinarith [sq_nonneg (‖A 0 0‖ - ‖A 1 1‖), sq_nonneg (‖A 0 1‖ - ‖A 1 0‖)]

/-- The metric induced by the Frobenius norm. -/
noncomputable def matrixDistance (A B : ComplexMatrix2) : ℝ := matrixNorm (A - B)

/-- The matrix metric is exactly the Frobenius metric. -/
theorem matrixDistance_eq_dist (A B : ComplexMatrix2) : matrixDistance A B = dist A B :=
  (dist_eq_norm A B).symm

/-- The entrywise expression for the matrix metric. -/
theorem matrixDistance_formula (A B : ComplexMatrix2) :
    matrixDistance A B = Real.sqrt (‖A 0 0 - B 0 0‖ ^ 2 + ‖A 0 1 - B 0 1‖ ^ 2 +
      ‖A 1 0 - B 1 0‖ ^ 2 + ‖A 1 1 - B 1 1‖ ^ 2) := by
  exact matrixNorm_formula (A - B)

/-- definiteness of the matrix metric. -/
theorem matrixDistance_eq_zero_iff (A B : ComplexMatrix2) :
    matrixDistance A B = 0 ↔ A = B := by
  rw [matrixDistance_eq_dist]
  exact dist_eq_zero

/-- symmetry of the matrix metric. -/
theorem matrixDistance_symm (A B : ComplexMatrix2) : matrixDistance A B = matrixDistance B A := by
  simp only [matrixDistance_eq_dist, dist_comm]

/-- The triangle inequality for the matrix metric. -/
theorem matrixDistance_triangle (A B C : ComplexMatrix2) :
    matrixDistance A B ≤ matrixDistance A C + matrixDistance C B := by
  simp only [matrixDistance_eq_dist]
  exact dist_triangle A C B

/-- continuity of the norm. -/
theorem matrixNorm_continuous : Continuous matrixNorm := continuous_norm

/-- continuity of the determinant. -/
theorem matrixDeterminant_continuous : Continuous (Matrix.det : ComplexMatrix2 → ℂ) :=
  continuous_id.matrix_det

/-- continuity of the trace. -/
theorem matrixTrace_continuous : Continuous (Matrix.trace : ComplexMatrix2 → ℂ) :=
  continuous_id.matrix_trace

/-- continuity of matrix multiplication. -/
theorem matrixMultiplication_continuous :
    Continuous (fun p : ComplexMatrix2 × ComplexMatrix2 => p.1 * p.2) := continuous_mul

/-- continuity of inversion at every nonsingular matrix. -/
theorem matrixInverse_continuousAt (A : ComplexMatrix2) (hA : Nonsingular A) :
    ContinuousAt (Inv.inv : ComplexMatrix2 → ComplexMatrix2) A := by
  apply continuousAt_matrix_inv A
  simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hA

/-- The general linear group is a topological group. -/
theorem generalLinear_isTopologicalGroup : IsTopologicalGroup GeneralLinear2 := inferInstance

/-- The usual topology on the general linear group is the matrix subspace topology. -/
theorem generalLinear_val_isEmbedding :
    Topology.IsEmbedding (fun A : GeneralLinear2 => (A : ComplexMatrix2)) :=
  Units.isEmbedding_val_mk'
    (fun A hA => (matrixInverse_continuousAt A ((nonsingular_iff_isUnit A).mpr hA)).continuousWithinAt)
    (fun A => (Matrix.coe_units_inv A).symm)

/-- limits commute with matrix multiplication. -/
theorem matrix_mul_tendsto {α : Type*} {l : Filter α}
    {f g : α → ComplexMatrix2} {A B : ComplexMatrix2}
    (hf : Filter.Tendsto f l (nhds A)) (hg : Filter.Tendsto g l (nhds B)) :
    Filter.Tendsto (fun x => f x * g x) l (nhds (A * B)) := hf.mul hg

/-- convergence for the matrix metric is entrywise convergence. -/
theorem matrix_tendsto_iff {α : Type*} {l : Filter α}
    (f : α → ComplexMatrix2) (A : ComplexMatrix2) :
    Filter.Tendsto f l (nhds A) ↔
      ∀ i j, Filter.Tendsto (fun x => f x i j) l (nhds (A i j)) := by
  exact tendsto_pi_nhds.trans (forall_congr' fun _ => tendsto_pi_nhds)

/-- Right multiplication preserves Euclidean length exactly for unitary matrices. -/
theorem rowNormPreserving_iff {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜) :
    (∀ x : EuclideanSpace 𝕜 (Fin n), ‖WithLp.toLp 2 (Matrix.vecMul x.ofLp A)‖ = ‖x‖) ↔
      A * A.conjTranspose = 1 := by
  let f := Matrix.toEuclideanLin A.transpose
  have hf (x : EuclideanSpace 𝕜 (Fin n)) :
      f x = WithLp.toLp 2 (Matrix.vecMul x.ofLp A) := by
    simp only [f, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_transpose]
  constructor
  · intro h
    have hn : ∀ x, ‖f x‖ = ‖x‖ := by simpa only [hf] using h
    have hi := (LinearMap.norm_map_iff_inner_map_map f).mp hn
    ext i j
    have hij := hi (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
    simpa [hf, EuclideanSpace.single, Matrix.single_one_vecMul,
      ← inner_matrix_row_row, Matrix.row, EuclideanSpace.inner_single_left,
      Matrix.one_apply, eq_comm] using hij
  · intro h
    have hi : ∀ x y, inner 𝕜 (f x) (f y) = inner 𝕜 x y := by
      intro x y
      let X : Matrix Unit (Fin n) 𝕜 := Matrix.replicateRow Unit x.ofLp
      let Y : Matrix Unit (Fin n) 𝕜 := Matrix.replicateRow Unit y.ofLp
      have hX : WithLp.toLp 2 ((X * A) ()) = f x := by
        rw [hf]
        rfl
      have hY : WithLp.toLp 2 ((Y * A) ()) = f y := by
        rw [hf]
        rfl
      calc
        inner 𝕜 (f x) (f y) = ((Y * A) * (X * A).conjTranspose) () () := by
          rw [← hX, ← hY]
          exact inner_matrix_row_row (X * A) (Y * A) () ()
        _ = (Y * X.conjTranspose) () () := by
          rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
            ← Matrix.mul_assoc A A.conjTranspose, h, Matrix.one_mul]
        _ = inner 𝕜 x y := by
          exact (inner_matrix_row_row X Y () ()).symm
    have hn := (LinearMap.norm_map_iff_inner_map_map f).mpr hi
    simpa only [hf] using hn

/-- Orthogonality is equivalent to the usual transpose inverse equation. -/
theorem orthogonalMatrix_iff_mul_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    OrthogonalMatrix A ↔ A * A.transpose = 1 := by
  simpa only [OrthogonalMatrix, Matrix.conjTranspose_eq_transpose_of_trivial] using
    rowNormPreserving_iff A

/-- Unitarity is equivalent to the usual Hermitian inverse equation. -/
theorem unitaryMatrix_iff_mul_conjTranspose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    UnitaryMatrix A ↔ A * A.conjTranspose = 1 := rowNormPreserving_iff A

/-- The orthogonal inverse characterization, with invertibility explicit. -/
theorem orthogonalMatrix_inverse_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    OrthogonalMatrix A ↔ A.det ≠ 0 ∧ A⁻¹ = A.transpose := by
  constructor
  · intro h
    have hm := (orthogonalMatrix_iff_mul_transpose A).mp h
    exact ⟨Matrix.det_ne_zero_of_right_inverse hm, Matrix.inv_eq_right_inv hm⟩
  · rintro ⟨hd, hi⟩
    apply (orthogonalMatrix_iff_mul_transpose A).mpr
    rw [← hi]
    exact A.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hd)

/-- An orthogonal matrix has determinant one or negative one. -/
theorem orthogonalMatrix_determinant {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : OrthogonalMatrix A) : A.det = 1 ∨ A.det = -1 := by
  have hd := congrArg Matrix.det ((orthogonalMatrix_iff_mul_transpose A).mp hA)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
  exact sq_eq_one_iff.mp (by simpa only [pow_two] using hd)

/-- The unitary inverse characterization, with invertibility explicit. -/
theorem unitaryMatrix_inverse_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    UnitaryMatrix A ↔ A.det ≠ 0 ∧ A⁻¹ = A.conjTranspose := by
  constructor
  · intro h
    have hm := (unitaryMatrix_iff_mul_conjTranspose A).mp h
    exact ⟨Matrix.det_ne_zero_of_right_inverse hm, Matrix.inv_eq_right_inv hm⟩
  · rintro ⟨hd, hi⟩
    apply (unitaryMatrix_iff_mul_conjTranspose A).mpr
    rw [← hi]
    exact A.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hd)

/-- The geometric norm-preserving orthogonal matrices agree with Mathlib's group. -/
theorem orthogonalMatrix_iff_mem_orthogonalGroup {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    OrthogonalMatrix A ↔ A ∈ Matrix.orthogonalGroup (Fin n) ℝ :=
  (orthogonalMatrix_iff_mul_transpose A).trans
    (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).symm

/-- The geometric norm-preserving unitary matrices agree with Mathlib's group. -/
theorem unitaryMatrix_iff_mem_unitaryGroup {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    UnitaryMatrix A ↔ A ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  (unitaryMatrix_iff_mul_conjTranspose A).trans Matrix.mem_unitaryGroup_iff.symm

end LowDimensionalTopology.Geometry.Auxiliary.Algebra
