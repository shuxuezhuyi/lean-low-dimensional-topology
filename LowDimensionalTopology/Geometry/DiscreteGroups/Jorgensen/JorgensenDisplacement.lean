module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfSpace.ParabolicHoroballs
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.MobiusDiscontinuity
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenIdentitySeparation
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
open Filter Topology
open scoped OnePoint ComplexConjugate Matrix.Norms.Frobenius
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius

/-- The trace-free part of a genuine determinant-one matrix. -/
def jorgensenCenteredMatrix (A : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2 :=
  (A : Auxiliary.Algebra.ComplexMatrix2) - (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) / 2) • 1

/-- Half-displacement in the original hyperbolic path metric. -/
def mobiusSinhDisplacement (f : Mobius.complexMobiusGroup) (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) : ℝ :=
  Real.sinh (Mobius.upperHalfSpacePathDist x (f • x) / 2)

/-- Orthogonal trace decomposition gives the exact centered Frobenius square. -/
theorem jorgensenCenteredMatrix_norm_sq (A : Auxiliary.Algebra.SpecialLinear2) :
    Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix A) ^ 2 =
      Auxiliary.Algebra.matrixNorm (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - ‖Matrix.trace (A :
        Auxiliary.Algebra.ComplexMatrix2)‖ ^ 2 / 2 := by
  rw [Auxiliary.Algebra.matrixNorm_sq, Auxiliary.Algebra.matrixNorm_sq]
  simp only [jorgensenCenteredMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, Matrix.trace_fin_two, Complex.sq_norm, Complex.normSq_apply]
  norm_num
  ring

/-- Equal-trace lifts express the product with the inverse by the two trace-free parts. -/
theorem jorgensen_centered_product_trace (A C : Auxiliary.Algebra.SpecialLinear2)
    (hC : Matrix.trace (C : Auxiliary.Algebra.ComplexMatrix2) = Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)) :
    Matrix.trace ((A * C⁻¹ : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) - 2 =
      (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4) / 2 -
        Matrix.trace (jorgensenCenteredMatrix A * jorgensenCenteredMatrix C) := by
  have hc : C 1 1 = A 0 0 + A 1 1 - C 0 0 := by
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two] at hC
    linear_combination hC
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, jorgensenCenteredMatrix, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  norm_num
  rw [hc]
  ring

/-- The original commutator is the product with the inverse of its genuine conjugate. -/
theorem jorgensen_centered_commutator_trace (A B : Auxiliary.Algebra.SpecialLinear2) :
    Matrix.trace (Mobius.Classification.specialCommutator A B : Auxiliary.Algebra.ComplexMatrix2) - 2 =
      (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4) / 2 -
        Matrix.trace (jorgensenCenteredMatrix A * jorgensenCenteredMatrix (B * A * B⁻¹)) := by
  have he : Mobius.Classification.specialCommutator A B = A * (B * A * B⁻¹)⁻¹ := by
    unfold Mobius.Classification.specialCommutator
    group
  rw [he]
  exact jorgensen_centered_product_trace A (B * A * B⁻¹) (Mobius.Classification.specialLinear_trace_conjugation A B)

/-- Jorgensen's inequality controls the product of the two centered norms for the original generator pair. -/
theorem jorgensen_centered_norm_bound (A B : Auxiliary.Algebra.SpecialLinear2)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({Mobius.mobiusSpecialLinearProjection A, Mobius.mobiusSpecialLinearProjection B} : Set
        Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure
      ({Mobius.mobiusSpecialLinearProjection A, Mobius.mobiusSpecialLinearProjection B} : Set
        Mobius.complexMobiusGroup))) :
    1 ≤ (3 / 2 : ℝ) * ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4‖ +
      Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix A) * Auxiliary.Algebra.matrixNorm
        (jorgensenCenteredMatrix (B * A * B⁻¹)) := by
  have hj := one_le_jorgensenDefect_of_discrete_nonElementary _ _ hD hH
  rw [jorgensenDefect_representatives, jorgensenMatrixDefect, jorgensen_centered_commutator_trace] at hj
  have ht := norm_sub_le ((Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4) / 2)
    (Matrix.trace (jorgensenCenteredMatrix A * jorgensenCenteredMatrix (B * A * B⁻¹)))
  rw [norm_div] at ht
  norm_num only [Complex.norm_ofNat] at ht
  have hc := jorgensen_trace_mul_norm_le (jorgensenCenteredMatrix A) (jorgensenCenteredMatrix (B * A * B⁻¹))
  linarith

/-- Half-displacement is nonnegative in the actual H3 metric. -/
theorem mobiusSinhDisplacement_nonneg (f : Mobius.complexMobiusGroup) (x :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    0 ≤ mobiusSinhDisplacement f x := Real.sinh_nonneg_iff.mpr
      (div_nonneg (jorgensen_upperHalfSpacePathDist_nonneg _ _) (by norm_num))

/-- Actual isometric conjugation preserves the entire displacement function. -/
theorem mobiusSinhDisplacement_conjugation (f q : Mobius.complexMobiusGroup) (x :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    mobiusSinhDisplacement (q * f * q⁻¹) (q • x) = mobiusSinhDisplacement f x := by
  unfold mobiusSinhDisplacement
  rw [Hyperbolic.QuaternionHalfSpace.parabolicDisplacement_conjugation]

/-- The original trace-free Frobenius norm is an exact displacement quantity at j. -/
theorem jorgensenCenteredMatrix_norm_sq_displacement (A : Auxiliary.Algebra.SpecialLinear2) :
    Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix A) ^ 2 =
      4 * mobiusSinhDisplacement (Mobius.mobiusSpecialLinearProjection A)
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ^ 2 + 2 -
        ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)‖ ^ 2 / 2 := by
  rw [jorgensenCenteredMatrix_norm_sq, ← Mobius.mobiusNormalizedNorm_specialLinearProjection A,
    Mobius.mobiusNormalizedNorm_sq_eq_two_cosh_origin_displacement]
  let d := Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
    (Mobius.mobiusSpecialLinearProjection A • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
  have hc := Real.cosh_two_mul (d / 2)
  rw [show 2 * (d / 2) = d by ring] at hc
  have hs := Real.cosh_sq_sub_sinh_sq (d / 2)
  change 2 * Real.cosh d - ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)‖ ^ 2 / 2 =
    4 * Real.sinh (d / 2) ^ 2 + 2 - ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)‖ ^ 2 / 2
  nlinarith

/-- The scalar trace defect bounds its real norm deficiency without any spectral restriction. -/
theorem jorgensen_trace_norm_gap (A : Auxiliary.Algebra.SpecialLinear2) :
    4 - ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)‖ ^ 2 ≤ ‖Matrix.trace (A :
      Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4‖ := by
  have h := norm_sub_norm_le (4 : ℂ) (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2)
  simpa only [Complex.norm_ofNat, norm_pow, norm_sub_rev] using h

/-- A uniform centered-norm square bound in terms of the actual displacement and trace defect. -/
theorem jorgensenCenteredMatrix_norm_sq_le (A : Auxiliary.Algebra.SpecialLinear2) :
    Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix A) ^ 2 ≤
      4 * mobiusSinhDisplacement (Mobius.mobiusSpecialLinearProjection A)
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ^ 2 +
        ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4‖ / 2 := by
  rw [jorgensenCenteredMatrix_norm_sq_displacement]
  linarith [jorgensen_trace_norm_gap A]

/-- The determinant-one quadratic trace identity is exact. -/
theorem jorgensen_trace_square (A : Auxiliary.Algebra.SpecialLinear2) :
    Matrix.trace ((A * A : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) = Matrix.trace (A
      : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 2 := by
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by simpa only [Matrix.det_fin_two] using A.det_coe
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination -2 * hd

/-- Cauchy-Schwarz bounds the trace-square term without choosing an eigenvector basis. -/
theorem jorgensen_trace_square_norm_le (A : Auxiliary.Algebra.SpecialLinear2) :
    ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 2‖ ≤ Auxiliary.Algebra.matrixNorm (A :
      Auxiliary.Algebra.ComplexMatrix2) ^ 2 := by
  have h := jorgensen_trace_mul_norm_le (A : Auxiliary.Algebra.ComplexMatrix2) (A : Auxiliary.Algebra.ComplexMatrix2)
  change ‖Matrix.trace ((A * A : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2)‖ ≤ _ at h
  simpa only [jorgensen_trace_square, pow_two] using h

/-- A quantitative maximum-displacement inequality for the original generator pair at j. -/
theorem jorgensen_max_displacement_at_j (f h : Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup))) :
    1 ≤ 2 * ‖Mobius.mobiusSquaredTrace f - 4‖ + 4 *
      (max (mobiusSinhDisplacement f Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
        (mobiusSinhDisplacement (h * f * h⁻¹) Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)) ^ 2 := by
  obtain ⟨A, rfl⟩ := Mobius.mobiusSpecialLinearProjection_surjective f
  obtain ⟨B, rfl⟩ := Mobius.mobiusSpecialLinearProjection_surjective h
  let C := B * A * B⁻¹
  let m := max (mobiusSinhDisplacement (Mobius.mobiusSpecialLinearProjection A)
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
    (mobiusSinhDisplacement (Mobius.mobiusSpecialLinearProjection C) Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
  have hC : Mobius.mobiusSpecialLinearProjection C =
      Mobius.mobiusSpecialLinearProjection B * Mobius.mobiusSpecialLinearProjection A *
        (Mobius.mobiusSpecialLinearProjection B)⁻¹ := by
    simp only [C, map_mul, map_inv]
  have htc : Matrix.trace (C : Auxiliary.Algebra.ComplexMatrix2) = Matrix.trace (A :
    Auxiliary.Algebra.ComplexMatrix2) :=
    Mobius.Classification.specialLinear_trace_conjugation A B
  have hA0 := mobiusSinhDisplacement_nonneg (Mobius.mobiusSpecialLinearProjection A)
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
  have hC0 := mobiusSinhDisplacement_nonneg (Mobius.mobiusSpecialLinearProjection C)
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
  have hmA : mobiusSinhDisplacement (Mobius.mobiusSpecialLinearProjection A)
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ≤ m := le_max_left _ _
  have hmC : mobiusSinhDisplacement (Mobius.mobiusSpecialLinearProjection C)
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ≤ m := le_max_right _ _
  have hm0 : 0 ≤ m := hA0.trans hmA
  have hsqA := jorgensenCenteredMatrix_norm_sq_le A
  have hsqC := jorgensenCenteredMatrix_norm_sq_le C
  rw [htc] at hsqC
  have hb := jorgensen_centered_norm_bound A B hD hH
  change 1 ≤ (3 / 2 : ℝ) * ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4‖ +
    Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix A) * Auxiliary.Algebra.matrixNorm
      (jorgensenCenteredMatrix C) at hb
  have hp : Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix A) * Auxiliary.Algebra.matrixNorm
    (jorgensenCenteredMatrix C) ≤
      4 * m ^ 2 + ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4‖ / 2 := by
    have hma := sq_le_sq₀ hA0 hm0 |>.mpr hmA
    have hmc := sq_le_sq₀ hC0 hm0 |>.mpr hmC
    nlinarith [sq_nonneg (Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix A) - Auxiliary.Algebra.matrixNorm
      (jorgensenCenteredMatrix C))]
  rw [Mobius.mobiusSquaredTrace_specialLinearProjection]
  change 1 ≤ 2 * ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4‖ +
    4 * (max (mobiusSinhDisplacement (Mobius.mobiusSpecialLinearProjection A)
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
      (mobiusSinhDisplacement (Mobius.mobiusSpecialLinearProjection B * Mobius.mobiusSpecialLinearProjection A *
        (Mobius.mobiusSpecialLinearProjection B)⁻¹) Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)) ^ 2
  rw [← hC]
  change 1 ≤ 2 * ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4‖ + 4 * m ^ 2
  linarith

/-- Trace-free matrices conjugate as actual matrices under the determinant-one group. -/
theorem jorgensenCenteredMatrix_conjugation (A B : Auxiliary.Algebra.SpecialLinear2) :
    jorgensenCenteredMatrix (B * A * B⁻¹) =
      (B : Auxiliary.Algebra.ComplexMatrix2) * jorgensenCenteredMatrix A * ((B⁻¹ :
        Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) := by
  have hc : (B : Auxiliary.Algebra.ComplexMatrix2) * ((B⁻¹ : Auxiliary.Algebra.SpecialLinear2) :
    Auxiliary.Algebra.ComplexMatrix2) = 1 := by
    change ((B * B⁻¹ : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) = 1
    simp
  rw [jorgensenCenteredMatrix, Mobius.Classification.specialLinear_trace_conjugation]
  simp only [jorgensenCenteredMatrix, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hc, Matrix.SpecialLinearGroup.coe_mul]

/-- Frobenius submultiplicativity controls actual centered conjugation by the actual conjugator norm. -/
theorem jorgensenCenteredMatrix_conjugation_norm_le (A B : Auxiliary.Algebra.SpecialLinear2) :
    Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix (B * A * B⁻¹)) ≤
      Auxiliary.Algebra.matrixNorm (B : Auxiliary.Algebra.ComplexMatrix2) ^ 2 * Auxiliary.Algebra.matrixNorm
        (jorgensenCenteredMatrix A) := by
  rw [jorgensenCenteredMatrix_conjugation]
  calc
    _ ≤ Auxiliary.Algebra.matrixNorm ((B : Auxiliary.Algebra.ComplexMatrix2) * jorgensenCenteredMatrix A) *
        Auxiliary.Algebra.matrixNorm ((B⁻¹ : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2)
          := Auxiliary.Algebra.matrixNorm_mul_le _ _
    _ ≤ (Auxiliary.Algebra.matrixNorm (B : Auxiliary.Algebra.ComplexMatrix2) * Auxiliary.Algebra.matrixNorm
      (jorgensenCenteredMatrix A)) *
        Auxiliary.Algebra.matrixNorm ((B⁻¹ : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) :=
      mul_le_mul_of_nonneg_right (Auxiliary.Algebra.matrixNorm_mul_le _ _) (Auxiliary.Algebra.matrixNorm_nonneg _)
    _ = _ := by rw [jorgensen_matrixNorm_inv]; ring

/-- Simultaneous genuine conjugation preserves the actual pair's admissibility. -/
theorem jorgensen_displacement_conjugation_admissible (f h q : Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup))) :
    Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({q * f * q⁻¹, q * h * q⁻¹} : Set Mobius.complexMobiusGroup)) ∧
    IsNonElementary (Subgroup.closure ({q * f * q⁻¹, q * h * q⁻¹} : Set Mobius.complexMobiusGroup)) := by
  let H := Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup)
  let _ : DiscreteTopology H := hD
  have he := jorgensen_generated_conjugation f h q
  constructor
  · rw [← he]
    exact DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q H
  · have hn := hH.conjugation q
    rwa [he] at hn

/-- Every genuine displacement calculation can be normalized at j by one actual Mobius map. -/
theorem jorgensen_displacement_normalize (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    ∃ q : Mobius.complexMobiusGroup, ∀ f : Mobius.complexMobiusGroup,
      Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ((q * f * q⁻¹) •
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) =
        Mobius.upperHalfSpacePathDist x (f • x) := by
  obtain ⟨h, hx⟩ := jorgensen_upperHalfSpace_transitive x
  have hq : h⁻¹ • x = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by rw [← hx, inv_smul_smul]
  refine ⟨h⁻¹, fun f => ?_⟩
  have hd := Hyperbolic.QuaternionHalfSpace.parabolicDisplacement_conjugation f h⁻¹ x
  rwa [hq] at hd

/-- An explicit exact displacement gap follows directly from centered matrix norms at j. -/
theorem jorgensen_log_displacement_gap_at_j (f h : Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup)))
    (hα : ‖Mobius.mobiusSquaredTrace f - 4‖ ≤ 1 / 4) :
    Real.log (149 / 100 : ℝ) < max (Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
      (f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ))
      (Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ (h •
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)) := by
  by_contra! hm
  obtain ⟨A, rfl⟩ := Mobius.mobiusSpecialLinearProjection_surjective f
  obtain ⟨B, rfl⟩ := Mobius.mobiusSpecialLinearProjection_surjective h
  let c : ℝ := (149 / 100 + (149 / 100)⁻¹) / 2
  have hc : Real.cosh (Real.log (149 / 100 : ℝ)) = c := Real.cosh_log (by norm_num)
  have hl : 0 < Real.log (149 / 100 : ℝ) := Real.log_pos (by norm_num)
  have hdA := (max_le_iff.mp hm).1
  have hdB := (max_le_iff.mp hm).2
  have hcoshA : Real.cosh (Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
      (Mobius.mobiusSpecialLinearProjection A • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)) ≤ c := by
    rw [← hc, Real.cosh_le_cosh, abs_of_nonneg (jorgensen_upperHalfSpacePathDist_nonneg _ _), abs_of_pos hl]
    exact hdA
  have hcoshB : Real.cosh (Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
      (Mobius.mobiusSpecialLinearProjection B • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)) ≤ c := by
    rw [← hc, Real.cosh_le_cosh, abs_of_nonneg (jorgensen_upperHalfSpacePathDist_nonneg _ _), abs_of_pos hl]
    exact hdB
  have hnormA : Auxiliary.Algebra.matrixNorm (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 ≤ 2 * c := by
    rw [← Mobius.mobiusNormalizedNorm_specialLinearProjection A,
      Mobius.mobiusNormalizedNorm_sq_eq_two_cosh_origin_displacement]
    linarith
  have hnormB : Auxiliary.Algebra.matrixNorm (B : Auxiliary.Algebra.ComplexMatrix2) ^ 2 ≤ 2 * c := by
    rw [← Mobius.mobiusNormalizedNorm_specialLinearProjection B,
      Mobius.mobiusNormalizedNorm_sq_eq_two_cosh_origin_displacement]
    linarith
  rw [Mobius.mobiusSquaredTrace_specialLinearProjection] at hα
  have hgap := jorgensen_trace_norm_gap A
  have hnormX := jorgensenCenteredMatrix_norm_sq A
  have hX : Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix A) ^ 2 ≤ 2 * c - 2 + 1 / 8 := by
    have ht : -(‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)‖ ^ 2) / 2 ≤ -2 + (1 / 8 : ℝ) := by
      nlinarith only [hgap, hα]
    calc
      _ = Auxiliary.Algebra.matrixNorm (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 + -(‖Matrix.trace (A :
        Auxiliary.Algebra.ComplexMatrix2)‖ ^ 2) / 2 := by rw [hnormX]; ring
      _ ≤ 2 * c + (-2 + (1 / 8 : ℝ)) := add_le_add hnormA ht
      _ = _ := by ring
  have hb := jorgensen_centered_norm_bound A B hD hH
  have hC := jorgensenCenteredMatrix_conjugation_norm_le A B
  have hprod : Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix A) * Auxiliary.Algebra.matrixNorm
    (jorgensenCenteredMatrix (B * A * B⁻¹)) ≤
      (2 * c) * (2 * c - 2 + 1 / 8) := by
    calc
      _ ≤ Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix A) *
          (Auxiliary.Algebra.matrixNorm (B : Auxiliary.Algebra.ComplexMatrix2) ^ 2 * Auxiliary.Algebra.matrixNorm
            (jorgensenCenteredMatrix A)) :=
        mul_le_mul_of_nonneg_left hC (Auxiliary.Algebra.matrixNorm_nonneg _)
      _ = Auxiliary.Algebra.matrixNorm (B : Auxiliary.Algebra.ComplexMatrix2) ^ 2 * Auxiliary.Algebra.matrixNorm
        (jorgensenCenteredMatrix A) ^ 2 := by ring
      _ ≤ _ := mul_le_mul hnormB hX (sq_nonneg _) (by dsimp [c]; norm_num)
  have hcnum : (3 / 2 : ℝ) * (1 / 4) + (2 * c) * (2 * c - 2 + 1 / 8) < 1 := by dsimp [c]; norm_num
  linarith

/-- The explicit logarithmic displacement gap is transported to every original H3 point. -/
theorem mobius_jorgensen_log_displacement_gap (f h : Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup)))
    (hα : ‖Mobius.mobiusSquaredTrace f - 4‖ ≤ 1 / 4) (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    Real.log (149 / 100 : ℝ) < max (Mobius.upperHalfSpacePathDist x (f • x)) (Mobius.upperHalfSpacePathDist x (h •
      x)) := by
  obtain ⟨q, hq⟩ := jorgensen_displacement_normalize x
  obtain ⟨hD', hH'⟩ := jorgensen_displacement_conjugation_admissible f h q hD hH
  have hα' : ‖Mobius.mobiusSquaredTrace (q * f * q⁻¹) - 4‖ ≤ 1 / 4 := by rwa [Mobius.mobiusSquaredTrace_conjugation]
  have hb := jorgensen_log_displacement_gap_at_j _ _ hD' hH' hα'
  rwa [hq f, hq h] at hb

/-- A rational comparison locates the explicit gap beyond the source's decimal prefix. -/
theorem jorgensen_log_gap_gt_thirty_nine_hundredths :
    (39 / 100 : ℝ) < Real.log (149 / 100 : ℝ) := by
  have h := Real.sum_range_le_log_div (x := (49 / 249 : ℝ)) (by norm_num) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The squared-trace neighborhood of the identity is open in the Möbius group. -/
def jorgensenTraceNeighbourhood : Set Mobius.complexMobiusGroup := {f | ‖Mobius.mobiusSquaredTrace f - 4‖ < 1 / 4}

theorem jorgensenTraceNeighbourhood_isOpen : IsOpen jorgensenTraceNeighbourhood :=
  isOpen_lt (jorgensen_mobiusSquaredTrace_continuous.sub continuous_const).norm continuous_const

theorem one_mem_jorgensenTraceNeighbourhood : (1 : Mobius.complexMobiusGroup) ∈ jorgensenTraceNeighbourhood := by
  have ht := Mobius.mobiusSquaredTrace_specialLinearProjection (1 : Auxiliary.Algebra.SpecialLinear2)
  norm_num [Matrix.trace_fin_two] at ht
  change ‖Mobius.mobiusSquaredTrace 1 - 4‖ < 1 / 4
  rw [ht]
  norm_num

/-- With a proved rational bound stronger than the printed decimal prefix. -/
theorem max_displacement_gt_constant_of_jorgensen_neighbourhood (f h : Mobius.complexMobiusGroup)
    (hf : f ∈ jorgensenTraceNeighbourhood)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup))) (x :
      Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (39 / 100 : ℝ) < max (Mobius.upperHalfSpacePathDist x (f • x)) (Mobius.upperHalfSpacePathDist x (h • x)) :=
  jorgensen_log_gap_gt_thirty_nine_hundredths.trans
    (mobius_jorgensen_log_displacement_gap f h hD hH hf.le x)

/-- The universal maximum-displacement estimate holds at every actual H3 point. -/
theorem mobius_jorgensen_max_displacement_squared (f h : Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup))) (x :
      Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    1 ≤ 2 * ‖Mobius.mobiusSquaredTrace f - 4‖ + 4 *
      (max (mobiusSinhDisplacement f x) (mobiusSinhDisplacement (h * f * h⁻¹) x)) ^ 2 := by
  obtain ⟨q, hq⟩ := jorgensen_displacement_normalize x
  obtain ⟨hD', hH'⟩ := jorgensen_displacement_conjugation_admissible f h q hD hH
  have hb := jorgensen_max_displacement_at_j _ _ hD' hH'
  have he : (q * h * q⁻¹) * (q * f * q⁻¹) * (q * h * q⁻¹)⁻¹ = q * (h * f * h⁻¹) * q⁻¹ := by group
  have hs (F : Mobius.complexMobiusGroup) : mobiusSinhDisplacement (q * F * q⁻¹)
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = mobiusSinhDisplacement F x := by
    unfold mobiusSinhDisplacement
    rw [hq]
  rwa [Mobius.mobiusSquaredTrace_conjugation, he, hs f, hs (h * f * h⁻¹)] at hb

/-- The actual estimate in fact holds for every generator type. -/
theorem quarter_le_max_sinh_displacement_of_trace_near_four (f h : Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup)))
    (hα : ‖Mobius.mobiusSquaredTrace f - 4‖ < 1 / 4) (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (1 / 4 : ℝ) ≤ max (mobiusSinhDisplacement f x) (mobiusSinhDisplacement (h * f * h⁻¹) x) := by
  have hb := mobius_jorgensen_max_displacement_squared f h hD hH x
  have hm0 : 0 ≤ max (mobiusSinhDisplacement f x) (mobiusSinhDisplacement (h * f * h⁻¹) x) :=
    (mobiusSinhDisplacement_nonneg f x).trans (le_max_left _ _)
  by_contra! hm
  nlinarith

/-- Positive-trace parabolic lifts have their trace-free part equal to their original difference. -/
theorem jorgensenCenteredMatrix_trace_two (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) = 2) :
    jorgensenCenteredMatrix A = (A : Auxiliary.Algebra.ComplexMatrix2) - 1 := by
  simp only [jorgensenCenteredMatrix, hA, div_self (by norm_num : (2 : ℂ) ≠ 0), one_smul]

/-- The original parabolic generator and its genuine conjugate satisfy the sharp product bound at j. -/
theorem jorgensen_parabolic_conjugate_at_j (f h : Mobius.complexMobiusGroup)
    (hf : Mobius.MobiusParabolic f)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup))) :
    (1 / 4 : ℝ) ≤ mobiusSinhDisplacement f Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ *
      mobiusSinhDisplacement (h * f * h⁻¹) Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
  obtain ⟨A, hA, htA⟩ := jorgensen_parabolic_positive_lift f hf
  obtain ⟨B, rfl⟩ := Mobius.mobiusSpecialLinearProjection_surjective h
  have hD' : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({Mobius.mobiusSpecialLinearProjection A, Mobius.mobiusSpecialLinearProjection B} : Set
        Mobius.complexMobiusGroup)) := by rwa [hA]
  have hH' : IsNonElementary (Subgroup.closure
      ({Mobius.mobiusSpecialLinearProjection A, Mobius.mobiusSpecialLinearProjection B} : Set
        Mobius.complexMobiusGroup)) := by rwa [hA]
  let C := B * A * B⁻¹
  have htC : Matrix.trace (C : Auxiliary.Algebra.ComplexMatrix2) = 2 :=
    (Mobius.Classification.specialLinear_trace_conjugation A B).trans htA
  have hC : Mobius.mobiusSpecialLinearProjection C = Mobius.mobiusSpecialLinearProjection B * f *
    (Mobius.mobiusSpecialLinearProjection B)⁻¹ := by
    simp only [C, map_mul, map_inv, hA]
  have hb := jorgensen_centered_norm_bound A B hD' hH'
  change 1 ≤ (3 / 2 : ℝ) * ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4‖ +
    Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix A) * Auxiliary.Algebra.matrixNorm
      (jorgensenCenteredMatrix C) at hb
  rw [htA] at hb
  norm_num only [sq, sub_self, norm_zero, mul_zero, zero_add] at hb
  rw [jorgensenCenteredMatrix_trace_two A htA, jorgensenCenteredMatrix_trace_two C htC,
    jorgensen_trace_two_difference_eq_sinh A htA, jorgensen_trace_two_difference_eq_sinh C htC, hA, hC] at hb
  change (1 / 4 : ℝ) ≤ Real.sinh (Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ (f
    • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) / 2) *
    Real.sinh (Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
      ((Mobius.mobiusSpecialLinearProjection B * f * (Mobius.mobiusSpecialLinearProjection B)⁻¹) •
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) / 2)
  nlinarith

/-- For the original group generated by the parabolic and its conjugator. -/
theorem quarter_le_parabolic_conjugate_sinh_displacement_product (f h : Mobius.complexMobiusGroup) (hf :
    Mobius.MobiusParabolic f)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup))) (x :
      Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (1 / 4 : ℝ) ≤ mobiusSinhDisplacement f x * mobiusSinhDisplacement (h * f * h⁻¹) x := by
  obtain ⟨q, hq⟩ := jorgensen_displacement_normalize x
  obtain ⟨hD', hH'⟩ := jorgensen_displacement_conjugation_admissible f h q hD hH
  have hf' : Mobius.MobiusParabolic (q * f * q⁻¹) := (Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q, rfl⟩)).mp hf
  have hb := jorgensen_parabolic_conjugate_at_j _ _ hf' hD' hH'
  have he : (q * h * q⁻¹) * (q * f * q⁻¹) * (q * h * q⁻¹)⁻¹ = q * (h * f * h⁻¹) * q⁻¹ := by group
  have hs (F : Mobius.complexMobiusGroup) : mobiusSinhDisplacement (q * F * q⁻¹)
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = mobiusSinhDisplacement F x := by
    unfold mobiusSinhDisplacement
    rw [hq]
  rwa [he, hs f, hs (h * f * h⁻¹)] at hb

/-- The original Frobenius square is twice cosh of displacement, equivalently four sinh-square plus two. -/
theorem jorgensen_matrixNorm_sq_displacement (A : Auxiliary.Algebra.SpecialLinear2) :
    Auxiliary.Algebra.matrixNorm (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 =
      4 * mobiusSinhDisplacement (Mobius.mobiusSpecialLinearProjection A)
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ^ 2 + 2 := by
  have h1 := jorgensenCenteredMatrix_norm_sq A
  have h2 := jorgensenCenteredMatrix_norm_sq_displacement A
  linarith

/-- A real hyperbolic trace-square gives both the exact centered norm and the minimum displacement bound. -/
theorem jorgensen_hyperbolic_matrix_data (A : Auxiliary.Algebra.SpecialLinear2) (r : ℝ) (hr : 4 < r)
    (hA : Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 = (r : ℂ)) :
    Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix A) ^ 2 =
      4 * mobiusSinhDisplacement (Mobius.mobiusSpecialLinearProjection A)
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ^ 2 - (r - 4) / 2 ∧
    r - 4 ≤ 4 * mobiusSinhDisplacement (Mobius.mobiusSpecialLinearProjection A)
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ^ 2 := by
  have hn : ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)‖ ^ 2 = r := by
    rw [← norm_pow, hA, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r)]
  have hcenter := jorgensenCenteredMatrix_norm_sq_displacement A
  rw [hn] at hcenter
  have htr := jorgensen_trace_square_norm_le A
  have he : ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 2‖ = r - 2 := by
    rw [hA]
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r - 2)]
  rw [he, jorgensen_matrixNorm_sq_displacement] at htr
  constructor <;> linarith

/-- The original hyperbolic generator and its genuine conjugate satisfy the source product bound at j. -/
theorem jorgensen_hyperbolic_conjugate_at_j (f h : Mobius.complexMobiusGroup) (hf : Mobius.MobiusHyperbolic f)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup))) :
    (1 / 8 : ℝ) ≤ mobiusSinhDisplacement f Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ *
      mobiusSinhDisplacement (h * f * h⁻¹) Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
  obtain ⟨r, hr, htrace⟩ := (Mobius.mobius_hyperbolic_iff_squaredTrace_real_gt_four f hf.1.1).mp hf
  obtain ⟨A, rfl⟩ := Mobius.mobiusSpecialLinearProjection_surjective f
  obtain ⟨B, rfl⟩ := Mobius.mobiusSpecialLinearProjection_surjective h
  rw [Mobius.mobiusSquaredTrace_specialLinearProjection] at htrace
  let C := B * A * B⁻¹
  let a := mobiusSinhDisplacement (Mobius.mobiusSpecialLinearProjection A)
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
  let b := mobiusSinhDisplacement (Mobius.mobiusSpecialLinearProjection C)
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
  let α := r - 4
  have hα : 0 < α := sub_pos.mpr hr
  have ha : 0 ≤ a := mobiusSinhDisplacement_nonneg _ _
  have hb : 0 ≤ b := mobiusSinhDisplacement_nonneg _ _
  have hct : Matrix.trace (C : Auxiliary.Algebra.ComplexMatrix2) ^ 2 = (r : ℂ) := by
    rw [show Matrix.trace (C : Auxiliary.Algebra.ComplexMatrix2) = Matrix.trace (A :
      Auxiliary.Algebra.ComplexMatrix2) from Mobius.Classification.specialLinear_trace_conjugation A B]
    exact htrace
  obtain ⟨hXA, hminA⟩ := jorgensen_hyperbolic_matrix_data A r hr htrace
  obtain ⟨hXC, hminC⟩ := jorgensen_hyperbolic_matrix_data C r hr hct
  change Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix A) ^ 2 = 4 * a ^ 2 - α / 2 at hXA
  change Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix C) ^ 2 = 4 * b ^ 2 - α / 2 at hXC
  change α ≤ 4 * a ^ 2 at hminA
  change α ≤ 4 * b ^ 2 at hminC
  have hmin : α ≤ 4 * a * b := by
    rcases le_total a b with hab | hab
    · nlinarith [mul_nonneg ha (sub_nonneg.mpr hab)]
    · nlinarith [mul_nonneg hb (sub_nonneg.mpr hab)]
  have hright : 0 ≤ 4 * a * b - α / 2 := by linarith
  have hprod : Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix A) * Auxiliary.Algebra.matrixNorm
    (jorgensenCenteredMatrix C) ≤
      4 * a * b - α / 2 := by
    apply (sq_le_sq₀ (mul_nonneg (Auxiliary.Algebra.matrixNorm_nonneg _) (Auxiliary.Algebra.matrixNorm_nonneg _))
      hright).mp
    have he : (4 * a * b - α / 2) ^ 2 -
        (Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix A) * Auxiliary.Algebra.matrixNorm
          (jorgensenCenteredMatrix C)) ^ 2 =
        2 * α * (a - b) ^ 2 := by rw [mul_pow, hXA, hXC]; ring
    nlinarith [mul_nonneg hα.le (sq_nonneg (a - b))]
  have hj := jorgensen_centered_norm_bound A B hD hH
  have heα : ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4‖ = α := by
    rw [htrace]
    change ‖(r : ℂ) - 4‖ = r - 4
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) from rfl, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
  rw [heα] at hj
  change 1 ≤ (3 / 2 : ℝ) * α + Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix A) *
    Auxiliary.Algebra.matrixNorm (jorgensenCenteredMatrix C) at hj
  have hC : Mobius.mobiusSpecialLinearProjection C =
      Mobius.mobiusSpecialLinearProjection B * Mobius.mobiusSpecialLinearProjection A *
        (Mobius.mobiusSpecialLinearProjection B)⁻¹ := by
    simp only [C, map_mul, map_inv]
  rw [← hC]
  change (1 / 8 : ℝ) ≤ a * b
  nlinarith

/-- With the genuine original group and path metric. -/
theorem eighth_le_hyperbolic_conjugate_sinh_displacement_product (f h : Mobius.complexMobiusGroup) (hf :
    Mobius.MobiusHyperbolic f)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure ({f, h} : Set Mobius.complexMobiusGroup))) (x :
      Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (1 / 8 : ℝ) ≤ mobiusSinhDisplacement f x * mobiusSinhDisplacement (h * f * h⁻¹) x := by
  obtain ⟨q, hq⟩ := jorgensen_displacement_normalize x
  obtain ⟨hD', hH'⟩ := jorgensen_displacement_conjugation_admissible f h q hD hH
  have hf' : Mobius.MobiusHyperbolic (q * f * q⁻¹) := Mobius.mobiusHyperbolic_conjugation_forward f q hf
  have hb := jorgensen_hyperbolic_conjugate_at_j _ _ hf' hD' hH'
  have he : (q * h * q⁻¹) * (q * f * q⁻¹) * (q * h * q⁻¹)⁻¹ = q * (h * f * h⁻¹) * q⁻¹ := by group
  have hs (F : Mobius.complexMobiusGroup) : mobiusSinhDisplacement (q * F * q⁻¹)
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = mobiusSinhDisplacement F x := by
    unfold mobiusSinhDisplacement
    rw [hq]
  rwa [he, hs f, hs (h * f * h⁻¹)] at hb

end LowDimensionalTopology.Geometry.DiscreteGroups
