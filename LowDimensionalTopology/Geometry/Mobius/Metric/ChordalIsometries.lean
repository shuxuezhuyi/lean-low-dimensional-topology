/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Mobius.FractionalLinear
public import LowDimensionalTopology.Geometry.Inversive.Stereographic
public import LowDimensionalTopology.Geometry.Auxiliary.Algebra.UnitaryMatrix

/-!
# Unitary matrices and chordal isometries

The actual sphere-induced chordal metric is transported through the standard
complex coordinates. Nonzero homogeneous vectors handle every pole and infinity.
This module proves the unitary/chordal-isometry equivalence for the actual
fractional-linear action. The hyperbolic and ball-model clauses require separate
geometric bridges.
-/

@[expose] public section

namespace LowDimensionalTopology.Geometry.Mobius

open LowDimensionalTopology.Geometry.Auxiliary.Algebra
open scoped OnePoint LinearAlgebra.Projectivization

noncomputable section

/-- The geometric chordal distance transported through the standard complex coordinates. -/
def complexChordalDist (z w : ExtendedComplex) : ℝ :=
  Inversive.chordalDist (extendedComplexEuclideanHomeomorph z)
    (extendedComplexEuclideanHomeomorph w)

/-- The original sphere-induced chordal metric on the extended complex plane. -/
abbrev complexChordalMetricSpace : MetricSpace ExtendedComplex := by
  let := Inversive.chordalMetricSpace 2
  exact extendedComplexEuclideanHomeomorph.isEmbedding.comapMetricSpace _

/-- The chordal metric has the original one-point compactification topology. -/
theorem complexChordalMetricSpace_topology :
    complexChordalMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace ExtendedComplex) := rfl

theorem complexChordalMetricSpace_dist (z w : ExtendedComplex) :
    @dist _ complexChordalMetricSpace.toDist z w = complexChordalDist z w := rfl

theorem complexChordalDist_nonneg (z w : ExtendedComplex) :
    0 ≤ complexChordalDist z w := dist_nonneg

theorem complexChordalDist_comm (z w : ExtendedComplex) :
    complexChordalDist z w = complexChordalDist w z := dist_comm _ _

theorem complexChordalDist_coe_coe (z w : ℂ) :
    complexChordalDist z w =
      2 * ‖z - w‖ / (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2)) := by
  unfold complexChordalDist
  rw [extendedComplexEuclideanHomeomorph_coe, extendedComplexEuclideanHomeomorph_coe,
    Inversive.chordalDist_coe_coe]
  simp only [dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map]

theorem complexChordalDist_coe_infty (z : ℂ) :
    complexChordalDist z ∞ = 2 / Real.sqrt (1 + ‖z‖ ^ 2) := by
  unfold complexChordalDist
  rw [extendedComplexEuclideanHomeomorph_coe, extendedComplexEuclideanHomeomorph_infty,
    Inversive.chordalDist_coe_infty]
  simp only [LinearIsometryEquiv.norm_map]

@[simp] theorem complexChordalDist_infty_infty : complexChordalDist ∞ ∞ = 0 := dist_self _

theorem complexChordalDist_coe_coe_sq (z w : ℂ) :
    complexChordalDist z w ^ 2 =
      4 * ‖z - w‖ ^ 2 / ((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) := by
  rw [complexChordalDist_coe_coe, div_pow, mul_pow, mul_pow,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  ring

theorem complexChordalDist_coe_infty_sq (z : ℂ) :
    complexChordalDist z ∞ ^ 2 = 4 / (1 + ‖z‖ ^ 2) := by
  rw [complexChordalDist_coe_infty, div_pow, Real.sq_sqrt (by positivity)]
  norm_num

/-- Homogeneous coordinates, with the zero second coordinate representing infinity. -/
def complexProjectivePoint (v : Fin 2 → ℂ) : ExtendedComplex :=
  if v 1 = 0 then ∞ else (v 0 / v 1 : ℂ)

theorem complexProjectivePoint_eq_projectivization (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    complexProjectivePoint v =
      (OnePoint.equivProjectivization ℂ).symm (Projectivization.mk ℂ v hv) := by
  simp only [complexProjectivePoint, OnePoint.equivProjectivization_symm_apply_mk,
    div_eq_mul_inv, mul_comm]

/-- Chordal distance in arbitrary nonzero homogeneous complex coordinates. -/
theorem complexChordalDist_projective_sq (v w : Fin 2 → ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    complexChordalDist (complexProjectivePoint v) (complexProjectivePoint w) ^ 2 =
      4 * ‖v 0 * w 1 - v 1 * w 0‖ ^ 2 /
        ((‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) * (‖w 0‖ ^ 2 + ‖w 1‖ ^ 2)) := by
  by_cases hv1 : v 1 = 0
  · have hv0 : v 0 ≠ 0 := by
      intro hv0
      exact hv (by ext i; fin_cases i <;> simp [hv0, hv1])
    by_cases hw1 : w 1 = 0
    · simp [complexProjectivePoint, hv1, hw1]
    · simp only [complexProjectivePoint, hv1, ite_true, hw1, ite_false,
        complexChordalDist_comm ∞, complexChordalDist_coe_infty_sq,
        zero_mul, sub_zero, norm_mul, norm_zero]
      rw [norm_div, div_pow]
      have hvn : ‖v 0‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
      have hwn : ‖w 1‖ ≠ 0 := norm_ne_zero_iff.mpr hw1
      have hws : ‖w 0‖ ^ 2 + ‖w 1‖ ^ 2 ≠ 0 := by positivity
      field_simp
      ring
  · by_cases hw1 : w 1 = 0
    · rw [complexChordalDist_comm]
      have hw0 : w 0 ≠ 0 := by
        intro hw0
        exact hw (by ext i; fin_cases i <;> simp [hw0, hw1])
      simp only [complexProjectivePoint, hv1, hw1, ite_true, ite_false,
        complexChordalDist_comm ∞, complexChordalDist_coe_infty_sq,
        mul_zero, zero_sub, norm_neg, norm_mul, norm_zero]
      rw [norm_div, div_pow]
      have hvn : ‖v 1‖ ≠ 0 := norm_ne_zero_iff.mpr hv1
      have hwn : ‖w 0‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
      have hvs : ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    · simp only [complexProjectivePoint, hv1, hw1, ite_false,
        complexChordalDist_coe_coe_sq]
      have hdiff : v 0 / v 1 - w 0 / w 1 =
          (v 0 * w 1 - v 1 * w 0) / (v 1 * w 1) := by field_simp
      rw [hdiff, norm_div, norm_mul, norm_div, norm_div, div_pow, div_pow, div_pow, mul_pow]
      have hvn : ‖v 1‖ ≠ 0 := norm_ne_zero_iff.mpr hv1
      have hwn : ‖w 1‖ ≠ 0 := norm_ne_zero_iff.mpr hw1
      have hvs : ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 ≠ 0 := by positivity
      have hws : ‖w 0‖ ^ 2 + ‖w 1‖ ^ 2 ≠ 0 := by positivity
      field_simp
      ring

/-- The homogeneous chart intertwines the genuine matrix and fractional-linear actions. -/
theorem complexProjectivePoint_smul (g : FractionalLinearMatrix) (v : Fin 2 → ℂ)
    (hv : v ≠ 0) :
    complexProjectivePoint (g • v) = fractionalLinear g (complexProjectivePoint v) := by
  apply (OnePoint.equivProjectivization ℂ).injective
  rw [complexProjectivePoint_eq_projectivization _ ((smul_ne_zero_iff_ne g).mpr hv),
    Equiv.apply_symm_apply, fractionalLinear_apply, OnePoint.equivProjectivization_smul,
    complexProjectivePoint_eq_projectivization _ hv, Equiv.apply_symm_apply,
    Projectivization.smul_mk]

/-- A fixed nonzero homogeneous representative of each point of the sphere. -/
def complexProjectiveVector (z : ExtendedComplex) : Fin 2 → ℂ :=
  z.elim ![1, 0] fun w => ![w, 1]

theorem complexProjectiveVector_ne_zero (z : ExtendedComplex) :
    complexProjectiveVector z ≠ 0 := by
  cases z using OnePoint.rec with
  | infty => simp [complexProjectiveVector]
  | coe z => simp [complexProjectiveVector]

theorem complexProjectivePoint_vector (z : ExtendedComplex) :
    complexProjectivePoint (complexProjectiveVector z) = z := by
  cases z using OnePoint.rec with
  | infty => simp [complexProjectiveVector, complexProjectivePoint]
  | coe z => simp [complexProjectiveVector, complexProjectivePoint]

/-- The Euclidean square length of a complex two-vector. -/
def complexVectorQuadratic (v : Fin 2 → ℂ) : ℝ := ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2

theorem complexVectorQuadratic_pos {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    0 < complexVectorQuadratic v := by
  have hex : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra! h
    exact hv (by ext i; fin_cases i <;> simp [h.1, h.2])
  rcases hex with h | h <;> unfold complexVectorQuadratic
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr h)) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr h))

/-- A unitary matrix preserves the homogeneous quadratic norm. -/
theorem unitary_complexVectorQuadratic (g : FractionalLinearMatrix)
    (hg : Auxiliary.Algebra.UnitaryMatrix (g : Auxiliary.Algebra.ComplexMatrix2)) (v : Fin 2 → ℂ) :
    complexVectorQuadratic (g • v) = complexVectorQuadratic v := by
  have h := congrArg (fun r : ℝ => r ^ 2)
    (Auxiliary.Algebra.unitary_preserves_column_norm (g : Auxiliary.Algebra.ComplexMatrix2) hg (WithLp.toLp 2 v))
  simpa only [complexVectorQuadratic, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
    PiLp.toLp_apply, Matrix.smul_eq_mulVec, Units.smul_def] using h

/-- The alternating determinant of two homogeneous columns transforms by the matrix determinant. -/
theorem homogeneous_wedge_smul (g : FractionalLinearMatrix) (v w : Fin 2 → ℂ) :
    (g • v) 0 * (g • w) 1 - (g • v) 1 * (g • w) 0 =
      (g : Auxiliary.Algebra.ComplexMatrix2).det * (v 0 * w 1 - v 1 * w 0) := by
  simp only [Matrix.GeneralLinearGroup.fin_two_smul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.det_fin_two]
  ring

/-- Unitary matrices preserve the actual sphere-induced chordal distance, including infinity. -/
theorem unitary_fractionalLinear_chordal_distance (g : FractionalLinearMatrix)
    (hg : Auxiliary.Algebra.UnitaryMatrix (g : Auxiliary.Algebra.ComplexMatrix2)) (z w : ExtendedComplex) :
    complexChordalDist (fractionalLinear g z) (fractionalLinear g w) = complexChordalDist z w := by
  let v := complexProjectiveVector z
  let u := complexProjectiveVector w
  have hv : v ≠ 0 := complexProjectiveVector_ne_zero z
  have hu : u ≠ 0 := complexProjectiveVector_ne_zero w
  have hsq : complexChordalDist (fractionalLinear g z) (fractionalLinear g w) ^ 2 =
      complexChordalDist z w ^ 2 := by
    rw [← complexProjectivePoint_vector z, ← complexProjectivePoint_vector w,
      ← complexProjectivePoint_smul g _ hv, ← complexProjectivePoint_smul g _ hu,
      complexChordalDist_projective_sq _ _ ((smul_ne_zero_iff_ne g).mpr hv)
        ((smul_ne_zero_iff_ne g).mpr hu), complexChordalDist_projective_sq _ _ hv hu,
      homogeneous_wedge_smul, norm_mul, Auxiliary.Algebra.unitary_determinant_norm (g :
        Auxiliary.Algebra.ComplexMatrix2) hg, one_mul]
    change 4 * ‖v 0 * u 1 - v 1 * u 0‖ ^ 2 /
      (complexVectorQuadratic (g • v) * complexVectorQuadratic (g • u)) = _
    rw [unitary_complexVectorQuadratic g hg v, unitary_complexVectorQuadratic g hg u]
    rfl
  exact (sq_eq_sq₀ (complexChordalDist_nonneg _ _) (complexChordalDist_nonneg _ _)).mp hsq

/-- The exact chordal action formula in homogeneous coordinates for every invertible matrix. -/
theorem fractionalLinear_homogeneous_chordal_sq (g : FractionalLinearMatrix)
    (v w : Fin 2 → ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    complexChordalDist (fractionalLinear g (complexProjectivePoint v))
      (fractionalLinear g (complexProjectivePoint w)) ^ 2 =
      4 * ‖(g : Auxiliary.Algebra.ComplexMatrix2).det‖ ^ 2 * ‖v 0 * w 1 - v 1 * w 0‖ ^ 2 /
        (complexVectorQuadratic (g • v) * complexVectorQuadratic (g • w)) := by
  rw [← complexProjectivePoint_smul g v hv, ← complexProjectivePoint_smul g w hw,
    complexChordalDist_projective_sq _ _ ((smul_ne_zero_iff_ne g).mpr hv)
      ((smul_ne_zero_iff_ne g).mpr hw), homogeneous_wedge_smul, norm_mul, mul_pow]
  unfold complexVectorQuadratic
  ring

/-- Chordal preservation constrains the product of the two homogeneous quadratic denominators. -/
theorem chordal_isometry_chart_product (g : FractionalLinearMatrix)
    (hdet : ‖(g : Auxiliary.Algebra.ComplexMatrix2).det‖ = 1)
    (hg : ∀ z w, complexChordalDist (fractionalLinear g z) (fractionalLinear g w) =
      complexChordalDist z w) (z : ℂ) :
    complexVectorQuadratic (g • ![z, 1]) * complexVectorQuadratic (g • ![1, 0]) =
      1 + ‖z‖ ^ 2 := by
  have hv : (![z, 1] : Fin 2 → ℂ) ≠ 0 := by simp
  have hw : (![1, 0] : Fin 2 → ℂ) ≠ 0 := by simp
  have h := congrArg (fun r : ℝ => r ^ 2)
    (hg (complexProjectivePoint ![z, 1]) (complexProjectivePoint ![1, 0]))
  rw [fractionalLinear_homogeneous_chordal_sq g _ _ hv hw,
    complexChordalDist_projective_sq _ _ hv hw] at h
  simp only [hdet, complexVectorQuadratic, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_zero, zero_sub, norm_neg, norm_one,
    one_pow, mul_one, norm_zero] at h
  norm_num at h
  have hvp := complexVectorQuadratic_pos ((smul_ne_zero_iff_ne g).mpr hv)
  have hwp := complexVectorQuadratic_pos ((smul_ne_zero_iff_ne g).mpr hw)
  have hzp : 0 < ‖z‖ ^ 2 + 1 := by positivity
  have heq : 4 / (complexVectorQuadratic (g • ![z, 1]) *
      complexVectorQuadratic (g • ![1, 0])) = 4 / (‖z‖ ^ 2 + 1) := by
    simpa [complexVectorQuadratic, Matrix.GeneralLinearGroup.fin_two_smul] using h
  have hcross := (div_eq_div_iff (mul_ne_zero hvp.ne' hwp.ne') hzp.ne').mp heq
  nlinarith

/-- The homogeneous norm satisfies the complex parallelogram law. -/
theorem complexVectorQuadratic_parallelogram (v w : Fin 2 → ℂ) :
    complexVectorQuadratic (v + w) + complexVectorQuadratic (v - w) =
      2 * (complexVectorQuadratic v + complexVectorQuadratic w) := by
  have h0 := parallelogram_law_with_norm ℂ (v 0) (w 0)
  have h1 := parallelogram_law_with_norm ℂ (v 1) (w 1)
  simp only [complexVectorQuadratic, Pi.add_apply, Pi.sub_apply]
  nlinarith

@[simp] theorem complexVectorQuadratic_neg (v : Fin 2 → ℂ) :
    complexVectorQuadratic (-v) = complexVectorQuadratic v := by
  simp only [complexVectorQuadratic, Pi.neg_apply, norm_neg]

/-- Chordal preservation and determinant of unit modulus force the first column to be unit. -/
theorem chordal_isometry_first_column_norm (g : FractionalLinearMatrix)
    (hdet : ‖(g : Auxiliary.Algebra.ComplexMatrix2).det‖ = 1)
    (hg : ∀ z w, complexChordalDist (fractionalLinear g z) (fractionalLinear g w) =
      complexChordalDist z w) : complexVectorQuadratic (g • ![1, 0]) = 1 := by
  let x : Fin 2 → ℂ := g • ![1, 0]
  let y : Fin 2 → ℂ := g • ![0, 1]
  have hplus : g • (![1, 1] : Fin 2 → ℂ) = x + y := by
    ext i
    fin_cases i <;> simp [x, y, Matrix.GeneralLinearGroup.fin_two_smul]
  have hminus : g • (![-1, 1] : Fin 2 → ℂ) = -(x - y) := by
    ext i
    fin_cases i <;> simp [x, y, Matrix.GeneralLinearGroup.fin_two_smul] <;> ring
  have h0 := chordal_isometry_chart_product g hdet hg 0
  have h1 := chordal_isometry_chart_product g hdet hg 1
  have hm := chordal_isometry_chart_product g hdet hg (-1)
  norm_num only [norm_zero, norm_one, norm_neg, zero_pow, one_pow, add_zero] at h0 h1 hm
  rw [hplus] at h1
  rw [hminus, complexVectorQuadratic_neg] at hm
  have hpar := congrArg (fun r => r * complexVectorQuadratic x)
    (complexVectorQuadratic_parallelogram x y)
  have hx : 0 < complexVectorQuadratic x :=
    complexVectorQuadratic_pos ((smul_ne_zero_iff_ne g).mpr (by simp))
  change complexVectorQuadratic y * complexVectorQuadratic x = 1 at h0
  change complexVectorQuadratic (x + y) * complexVectorQuadratic x = 2 at h1
  change complexVectorQuadratic (x - y) * complexVectorQuadratic x = 2 at hm
  change complexVectorQuadratic x = 1
  nlinarith

/-- Scalar multiplication changes the homogeneous quadratic norm by the scalar's squared norm. -/
theorem complexVectorQuadratic_smul (c : ℂ) (v : Fin 2 → ℂ) :
    complexVectorQuadratic (c • v) = ‖c‖ ^ 2 * complexVectorQuadratic v := by
  simp only [complexVectorQuadratic, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  ring

/-- Chordal preservation and normalized determinant preserve every homogeneous quadratic norm. -/
theorem chordal_isometry_preserves_quadratic (g : FractionalLinearMatrix)
    (hdet : ‖(g : Auxiliary.Algebra.ComplexMatrix2).det‖ = 1)
    (hg : ∀ z w, complexChordalDist (fractionalLinear g z) (fractionalLinear g w) =
      complexChordalDist z w) (v : Fin 2 → ℂ) :
    complexVectorQuadratic (g • v) = complexVectorQuadratic v := by
  have hfirst := chordal_isometry_first_column_norm g hdet hg
  have hchart (z : ℂ) :
      complexVectorQuadratic (g • ![z, 1]) = complexVectorQuadratic ![z, 1] := by
    have h := chordal_isometry_chart_product g hdet hg z
    rw [hfirst, mul_one] at h
    simpa [complexVectorQuadratic, add_comm] using h
  by_cases hv1 : v 1 = 0
  · have hv : v = v 0 • (![1, 0] : Fin 2 → ℂ) := by
      ext i
      fin_cases i <;> simp [hv1]
    rw [hv, smul_comm g (v 0), complexVectorQuadratic_smul, complexVectorQuadratic_smul, hfirst]
    simp [complexVectorQuadratic]
  · have hv : v = v 1 • (![v 0 / v 1, 1] : Fin 2 → ℂ) := by
      ext i
      fin_cases i
      · change v 0 = v 1 * (v 0 / v 1)
        field_simp
      · simp
    rw [hv, smul_comm g (v 1), complexVectorQuadratic_smul, complexVectorQuadratic_smul, hchart]

/-- Conversely, a determinant-normalized fractional-linear chordal isometry is unitary. -/
theorem unitary_of_fractionalLinear_chordal_distance (g : FractionalLinearMatrix)
    (hdet : ‖(g : Auxiliary.Algebra.ComplexMatrix2).det‖ = 1)
    (hg : ∀ z w, complexChordalDist (fractionalLinear g z) (fractionalLinear g w) =
      complexChordalDist z w) : Auxiliary.Algebra.UnitaryMatrix (g : Auxiliary.Algebra.ComplexMatrix2) := by
  have ht : Auxiliary.Algebra.UnitaryMatrix (g : Auxiliary.Algebra.ComplexMatrix2).transpose := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have h := chordal_isometry_preserves_quadratic g hdet hg x.ofLp
    simpa only [complexVectorQuadratic, Matrix.vecMul_transpose, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_two, PiLp.toLp_apply, Units.smul_def, Matrix.smul_eq_mulVec] using h
  exact (Auxiliary.Algebra.unitaryMatrix_iff_mem_unitaryGroup (g : Auxiliary.Algebra.ComplexMatrix2)).mpr
    (Matrix.transpose_mem_unitaryGroup_iff.mp
      ((Auxiliary.Algebra.unitaryMatrix_iff_mem_unitaryGroup (g : Auxiliary.Algebra.ComplexMatrix2).transpose).mp ht))

/-- The algebraic and chordal conditions are equivalent after normalizing the determinant. -/
theorem unitary_iff_fractionalLinear_chordal_distance (g : FractionalLinearMatrix)
    (hdet : ‖(g : Auxiliary.Algebra.ComplexMatrix2).det‖ = 1) :
    Auxiliary.Algebra.UnitaryMatrix (g : Auxiliary.Algebra.ComplexMatrix2) ↔
      ∀ z w, complexChordalDist (fractionalLinear g z) (fractionalLinear g w) =
        complexChordalDist z w :=
  ⟨fun hg => unitary_fractionalLinear_chordal_distance g hg,
    unitary_of_fractionalLinear_chordal_distance g hdet⟩

/-- The distance-preservation condition is isometry for the original sphere-induced metric. -/
theorem fractionalLinear_chordal_isometry_iff (g : FractionalLinearMatrix) :
    (letI := complexChordalMetricSpace; Isometry (fractionalLinear g)) ↔
      ∀ z w, complexChordalDist (fractionalLinear g z) (fractionalLinear g w) =
        complexChordalDist z w := by
  let := complexChordalMetricSpace
  exact isometry_iff_dist_eq

/-- ↔(v), for the actual extended fractional-linear action. -/
theorem unitary_iff_fractionalLinear_chordal_isometry (A : Auxiliary.Algebra.SpecialLinear2) :
    Auxiliary.Algebra.UnitaryMatrix (A : Auxiliary.Algebra.ComplexMatrix2) ↔
      (letI := complexChordalMetricSpace;
        Isometry (fractionalLinear (Matrix.SpecialLinearGroup.toGL A))) := by
  rw [fractionalLinear_chordal_isometry_iff]
  exact unitary_iff_fractionalLinear_chordal_distance (Matrix.SpecialLinearGroup.toGL A)
    (by change ‖(A : Auxiliary.Algebra.ComplexMatrix2).det‖ = 1; rw [A.det_coe, norm_one])

/-- A unitary matrix gives a bijective isometry of the geometric chordal sphere. -/
def unitaryFractionalLinearIsometry (g : FractionalLinearMatrix)
    (hg : Auxiliary.Algebra.UnitaryMatrix (g : Auxiliary.Algebra.ComplexMatrix2)) :
    letI := complexChordalMetricSpace
    ExtendedComplex ≃ᵢ ExtendedComplex := by
  let := complexChordalMetricSpace
  exact
    { toEquiv := fractionalLinear g
      isometry_toFun := (fractionalLinear_chordal_isometry_iff g).mpr
        (unitary_fractionalLinear_chordal_distance g hg) }

theorem unitaryFractionalLinearIsometry_apply (g : FractionalLinearMatrix)
    (hg : Auxiliary.Algebra.UnitaryMatrix (g : Auxiliary.Algebra.ComplexMatrix2)) (z : ExtendedComplex) :
    unitaryFractionalLinearIsometry g hg z = fractionalLinear g z := rfl

end
end LowDimensionalTopology.Geometry.Mobius
