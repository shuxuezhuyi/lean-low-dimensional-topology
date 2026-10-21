/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.Inversions
/-!
# The symmetric bracket

The polynomial identity defines the continuous value at a zero argument.
Away from that argument it agrees with the stated inversion formula.
The complex-plane expression, identity and unit-sphere level set
are verified in the fixed Euclidean norm.
-/

@[expose] public section
noncomputable section
open scoped RealInnerProductSpace ComplexConjugate
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}

def bracket (u v : Euclidean n) : ℝ :=
  Real.sqrt (1-2*inner ℝ u v+‖u‖^2*‖v‖^2)

theorem bracket_radicand_nonneg (u v : Euclidean n) :
    0 ≤ 1-2*inner ℝ u v+‖u‖^2*‖v‖^2 := by
  have h := real_inner_le_norm u v
  nlinarith [sq_nonneg (‖u‖*‖v‖-1)]

theorem bracket_nonneg (u v : Euclidean n) : 0 ≤ bracket u v := Real.sqrt_nonneg _

theorem bracket_sq (u v : Euclidean n) :
    bracket u v ^ 2 = 1-2*inner ℝ u v+‖u‖^2*‖v‖^2 :=
  Real.sq_sqrt (bracket_radicand_nonneg u v)

theorem bracket_zero_left (v : Euclidean n) : bracket 0 v=1 := by simp [bracket]
theorem bracket_zero_right (u : Euclidean n) : bracket u 0=1 := by simp [bracket]

theorem bracket_comm (u v : Euclidean n) : bracket u v=bracket v u := by
  unfold bracket
  rw [real_inner_comm u v]
  congr 1
  ring

theorem continuous_bracket : Continuous (fun p : Euclidean n × Euclidean n => bracket p.1 p.2) := by
  unfold bracket
  fun_prop

theorem norm_unitInversion (u : Euclidean n) : ‖unitInversion u‖ = ‖u‖⁻¹ := by
  simp only [unitInversion, norm_smul, norm_inv, norm_pow, norm_norm]
  by_cases hu : ‖u‖=0
  · simp [hu]
  · field_simp

theorem bracket_eq_inversion (u v : Euclidean n) (hu : u ≠ 0) :
    bracket u v=‖u‖*‖unitInversion u-v‖ := by
  apply (sq_eq_sq₀ (bracket_nonneg u v) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [bracket_sq, mul_pow, norm_sub_sq_real, norm_unitInversion]
  simp only [unitInversion, real_inner_smul_left]
  field_simp [norm_ne_zero_iff.mpr hu]

theorem bracket_sq_eq_distance_sq_add_norm_defects (u v : Euclidean n) :
    bracket u v^2=‖u-v‖^2+(‖u‖^2-1)*(‖v‖^2-1) := by
  rw [bracket_sq, norm_sub_sq_real]
  ring

theorem complex_bracket (z w : ℂ) :
    bracket (Complex.orthonormalBasisOneI.repr z) (Complex.orthonormalBasisOneI.repr w) =
      ‖1-conj z*w‖ := by
  apply (sq_eq_sq₀ (bracket_nonneg _ _) (norm_nonneg _)).mp
  rw [bracket_sq, Complex.orthonormalBasisOneI.repr.inner_map_map,
    Complex.orthonormalBasisOneI.repr.norm_map, Complex.orthonormalBasisOneI.repr.norm_map,
    norm_sub_sq_real]
  simp [Complex.inner, Complex.mul_re]
  ring
theorem norm_product_gap_le_bracket (u v : Euclidean n) :
    |1-‖u‖*‖v‖| ≤ bracket u v := by
  apply (sq_le_sq₀ (abs_nonneg _) (bracket_nonneg u v)).mp
  rw [sq_abs, bracket_sq]
  nlinarith [real_inner_le_norm u v]

theorem bracket_pos_on_unit_sphere (u v : Euclidean n) (hu : ‖u‖=1) (hv : ‖v‖<1) :
    0 < bracket u v := by
  have h := norm_product_gap_le_bracket u v
  rw [hu, one_mul, abs_of_pos (sub_pos.mpr hv)] at h
  linarith

theorem bracket_level_set (x v : Euclidean n) (hv : ‖v‖<1) :
    ‖x-v‖/bracket x v=1 ↔ ‖x‖=1 := by
  constructor
  · intro heq
    have hne : bracket x v ≠ 0 := by intro h; simp [h] at heq
    have heq' : ‖x-v‖=bracket x v := by simpa only [one_mul] using (div_eq_iff hne).mp heq
    have hsq := congrArg (fun r : ℝ => r^2) heq'
    rw [bracket_sq_eq_distance_sq_add_norm_defects] at hsq
    have hprod : (‖x‖^2-1)*(‖v‖^2-1)=0 := by linarith
    have hvne : ‖v‖^2-1 ≠ 0 := by nlinarith [norm_nonneg v]
    have hx := (mul_eq_zero.mp hprod).resolve_right hvne
    nlinarith [norm_nonneg x]
  · intro hx
    have hsq : ‖x-v‖^2=bracket x v^2 := by rw [bracket_sq_eq_distance_sq_add_norm_defects, hx]; ring
    have heq := (sq_eq_sq₀ (norm_nonneg _) (bracket_nonneg x v)).mp hsq
    rw [heq, div_self (bracket_pos_on_unit_sphere x v hx hv).ne']

theorem bracket_inversion_level_set (a x : Euclidean n) (ha : 1<‖a‖) :
    ‖x-unitInversion a‖/bracket x (unitInversion a)=1 ↔ ‖x‖=1 := by
  apply bracket_level_set
  rw [norm_unitInversion, inv_eq_one_div]
  exact (div_lt_one (zero_lt_one.trans ha)).mpr ha

theorem unit_sphere_eq_bracket_level (a : Euclidean n) (ha : 1<‖a‖) :
    Metric.sphere (0 : Euclidean n) 1 =
      {x | ‖x-unitInversion a‖/bracket x (unitInversion a)=1} := by
  ext x
  simpa only [Metric.mem_sphere, dist_zero_right, Set.mem_ofPred_eq] using
    (bracket_inversion_level_set a x ha).symm
end LowDimensionalTopology.Geometry.Inversive
