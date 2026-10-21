module
public import LowDimensionalTopology.Geometry.Mobius.InvariantDisc.InvariantDiscConverse
public import LowDimensionalTopology.Geometry.Mobius.Topology
public import LowDimensionalTopology.Geometry.Mobius.Dynamics.MobiusIteration
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenSharpness
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
open Filter Topology
open scoped OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups

/-- The determinant-one commutator lift is intrinsic to the actual transformations. -/
def mobiusCommutatorLift (f g : Mobius.complexMobiusGroup) : Auxiliary.Algebra.SpecialLinear2 :=
  Mobius.Classification.specialCommutator
    (Mobius.Classification.specialRepresentative (Mobius.complexMobiusEquivFractionalLinear f))
    (Mobius.Classification.specialRepresentative (Mobius.complexMobiusEquivFractionalLinear g))

/-- Any genuine determinant-one representatives give exactly the same commutator matrix. -/
theorem mobiusCommutatorLift_representatives (f g : Mobius.complexMobiusGroup) (A B : Auxiliary.Algebra.SpecialLinear2)
    (hA : Mobius.mobiusSpecialLinearProjection A = f) (hB : Mobius.mobiusSpecialLinearProjection B = g) :
    mobiusCommutatorLift f g = Mobius.Classification.specialCommutator A B := by
  unfold mobiusCommutatorLift
  rw [Mobius.Classification.specialCommutator_eq_left _ _ A
    ((Mobius.Classification.specialRepresentative_projection _).trans
      ((Mobius.mobiusSpecialLinearProjection_eq_iff A f).mp hA).symm),
    Mobius.Classification.specialCommutator_eq_right _ _ B
      ((Mobius.Classification.specialRepresentative_projection _).trans
        ((Mobius.mobiusSpecialLinearProjection_eq_iff B g).mp hB).symm)]

/-- The intrinsic matrix lifts the actual group commutator. -/
theorem mobiusCommutatorLift_projection (f g : Mobius.complexMobiusGroup) :
    Mobius.mobiusSpecialLinearProjection (mobiusCommutatorLift f g) = Mobius.mobiusCommutator f g := by
  obtain ⟨A, hA⟩ := Mobius.mobiusSpecialLinearProjection_surjective f
  obtain ⟨B, hB⟩ := Mobius.mobiusSpecialLinearProjection_surjective g
  rw [mobiusCommutatorLift_representatives f g A B hA hB]
  simp only [Mobius.Classification.specialCommutator, map_mul, map_inv, hA, hB, Mobius.mobiusCommutator]

/-- Its ordinary matrix trace is precisely the previously defined sign-independent trace. -/
theorem mobiusCommutatorLift_trace (f g : Mobius.complexMobiusGroup) :
    Matrix.trace (mobiusCommutatorLift f g : Auxiliary.Algebra.ComplexMatrix2) = Mobius.mobiusCommutatorTrace f g := rfl

/-- The actual scalar quantity in Jorgensen's inequality. -/
def jorgensenDefect (f g : Mobius.complexMobiusGroup) : ℝ :=
  ‖Mobius.mobiusSquaredTrace f - 4‖ + ‖Mobius.mobiusCommutatorTrace f g - 2‖

/-- The determinant-one matrix expression uses the ordinary commutator trace. -/
def jorgensenMatrixDefect (A B : Auxiliary.Algebra.SpecialLinear2) : ℝ :=
  ‖Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4‖ +
    ‖Matrix.trace (Mobius.Classification.specialCommutator A B : Auxiliary.Algebra.ComplexMatrix2) - 2‖

theorem jorgensenDefect_representatives (A B : Auxiliary.Algebra.SpecialLinear2) :
    jorgensenDefect (Mobius.mobiusSpecialLinearProjection A) (Mobius.mobiusSpecialLinearProjection B) =
      jorgensenMatrixDefect A B := by
  rw [jorgensenDefect, Mobius.mobiusSquaredTrace_specialLinearProjection,
    Mobius.mobiusCommutatorTrace_representatives _ _ A B rfl rfl]
  rfl

/-- One normalized iteration step, in the exact order used in the source. -/
def jorgensenStep (A B : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.SpecialLinear2 := B * A * B⁻¹

/-- The genuine determinant-one conjugation iterates. -/
def jorgensenIterate (A B : Auxiliary.Algebra.SpecialLinear2) : ℕ → Auxiliary.Algebra.SpecialLinear2
  | 0 => B
  | n + 1 => jorgensenStep A (jorgensenIterate A B n)

/-- The actual transformations of the matrix iteration are the actual conjugation iterates. -/
theorem jorgensenIterate_projection (A B : Auxiliary.Algebra.SpecialLinear2) (n : ℕ) :
    Mobius.mobiusSpecialLinearProjection (jorgensenIterate A B n) =
      ((fun h : Mobius.complexMobiusGroup => h * Mobius.mobiusSpecialLinearProjection A * h⁻¹)^[n])
        (Mobius.mobiusSpecialLinearProjection B) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [jorgensenIterate, jorgensenStep, map_mul, map_inv, ih,
      Function.iterate_succ_apply']

/-- The iteration remains inside any subgroup containing both matrices. -/
theorem jorgensenIterate_mem (K : Subgroup Auxiliary.Algebra.SpecialLinear2) (A B : Auxiliary.Algebra.SpecialLinear2)
    (hA : A ∈ K) (hB : B ∈ K) (n : ℕ) : jorgensenIterate A B n ∈ K := by
  induction n with
  | zero => exact hB
  | succ n ih => exact K.mul_mem (K.mul_mem ih hA) (K.inv_mem ih)

/-- A complex multiplicative recurrence contracts to zero when its coefficient tends inside the unit disc. -/
theorem jorgensen_tendsto_zero_of_recurrence {a e : ℕ → ℂ} {z : ℂ}
    (he : Tendsto e atTop (𝓝 z)) (hz : ‖z‖ < 1)
    (hr : ∀ n, a (n + 1) = e n * a n) : Tendsto a atTop (𝓝 0) := by
  obtain ⟨q, hq, hq1⟩ := exists_between hz
  apply Summable.tendsto_atTop_zero
  apply summable_of_ratio_norm_eventually_le hq1
  filter_upwards [he.norm.eventually_le_const hq] with n hn
  rw [hr, norm_mul]
  exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)

/-- All four exact parabolic recurrence coefficients. -/
theorem jorgensenStep_parabolic (B : Auxiliary.Algebra.SpecialLinear2) :
    jorgensenStep Mobius.invariantDiscTranslationLift B 0 0 = 1 - B 0 0 * B 1 0 ∧
    jorgensenStep Mobius.invariantDiscTranslationLift B 0 1 = (B 0 0) ^ 2 ∧
    jorgensenStep Mobius.invariantDiscTranslationLift B 1 0 = -(B 1 0) ^ 2 ∧
    jorgensenStep Mobius.invariantDiscTranslationLift B 1 1 = 1 + B 0 0 * B 1 0 := by
  have hd : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using B.det_coe
  have hs (i j : Fin 2) : jorgensenStep Mobius.invariantDiscTranslationLift B i j =
      ((B : Auxiliary.Algebra.ComplexMatrix2) * !![(1 : ℂ), 1; 0, 1] * Matrix.adjugate (B :
        Auxiliary.Algebra.ComplexMatrix2)) i j := rfl
  simp only [hs, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    mul_one, mul_zero, add_zero]
  constructor
  · linear_combination hd
  constructor
  · ring
  constructor
  · ring
  · linear_combination hd

/-- All four exact diagonal recurrence coefficients. -/
theorem jorgensenStep_diagonal (A B : Auxiliary.Algebra.SpecialLinear2) (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) :
    jorgensenStep A B 0 0 = A 0 0 + (A 0 0 - A 1 1) * B 0 1 * B 1 0 ∧
    jorgensenStep A B 0 1 = -(A 0 0 - A 1 1) * B 0 0 * B 0 1 ∧
    jorgensenStep A B 1 0 = (A 0 0 - A 1 1) * B 1 0 * B 1 1 ∧
    jorgensenStep A B 1 1 = A 1 1 - (A 0 0 - A 1 1) * B 0 1 * B 1 0 := by
  have hd : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using B.det_coe
  have hs (i j : Fin 2) : jorgensenStep A B i j =
      ((B : Auxiliary.Algebra.ComplexMatrix2) * (A : Auxiliary.Algebra.ComplexMatrix2) * Matrix.adjugate (B :
        Auxiliary.Algebra.ComplexMatrix2)) i j := rfl
  simp only [hs, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    h01, h10, mul_zero, zero_add, add_zero]
  constructor
  · linear_combination A 0 0 * hd
  constructor
  · ring
  constructor
  · ring
  · linear_combination A 1 1 * hd

/-- The trace defect of the normalized parabolic pair is exactly the lower-left squared norm. -/
theorem jorgensenMatrixDefect_parabolic (B : Auxiliary.Algebra.SpecialLinear2) :
    jorgensenMatrixDefect Mobius.invariantDiscTranslationLift B = ‖B 1 0‖ ^ 2 := by
  have ht := Mobius.Classification.specialCommutator_trace_triangular Mobius.invariantDiscTranslationLift B (by rfl)
  norm_num [Mobius.invariantDiscTranslationLift] at ht
  simp only [jorgensenMatrixDefect, Mobius.invariantDiscTranslationLift, Matrix.trace_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.of_apply] at *
  rw [ht]
  norm_num [norm_pow]

/-- The diagonal trace-square defect is the square of the eigenvalue difference. -/
theorem jorgensen_diagonal_trace_defect (A : Auxiliary.Algebra.SpecialLinear2) (h01 : A 0 1 = 0) :
    Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4 = (A 0 0 - A 1 1) ^ 2 := by
  have hd : A 0 0 * A 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, h01, zero_mul, sub_zero] using A.det_coe
  rw [Matrix.trace_fin_two]
  linear_combination 4 * hd

/-- The normalized diagonal Jorgensen defect factors into the exact contraction parameter. -/
theorem jorgensenMatrixDefect_diagonal (A B : Auxiliary.Algebra.SpecialLinear2)
    (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) :
    jorgensenMatrixDefect A B = (1 + ‖B 0 1 * B 1 0‖) * ‖A 0 0 - A 1 1‖ ^ 2 := by
  have ht := Mobius.Classification.specialCommutator_trace_triangular A B h10
  simp only [h01, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, add_zero] at ht
  rw [jorgensenMatrixDefect, jorgensen_diagonal_trace_defect A h01, ht]
  have he : 2 - (A 0 0 - A 1 1) ^ 2 * B 1 0 * B 0 1 - 2 =
      -(A 0 0 - A 1 1) ^ 2 * (B 0 1 * B 1 0) := by ring
  rw [he, norm_mul, norm_neg, norm_pow]
  ring

/-- The nonlinear parabolic scalar recurrence has geometric decay and a vanishing mixed term. -/
theorem jorgensen_parabolic_scalar_limits {a c : ℕ → ℂ}
    (ha : ∀ n, a (n + 1) = 1 - a n * c n)
    (hc : ∀ n, c (n + 1) = -(c n) ^ 2) (hc0 : ‖c 0‖ < 1) :
    Tendsto c atTop (𝓝 0) ∧ Tendsto (fun n => a n * c n) atTop (𝓝 0) := by
  let r := ‖c 0‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := hc0
  have hcle : ∀ n, ‖c n‖ ≤ r := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [hc, norm_neg, norm_pow]
      nlinarith [norm_nonneg (c n)]
  have hcpow : ∀ n, ‖c n‖ ≤ r ^ n := by
    intro n
    induction n with
    | zero => simpa using hr1.le
    | succ n ih =>
      rw [hc, norm_neg, norm_pow, pow_succ]
      calc
        ‖c n‖ ^ 2 ≤ ‖c n‖ * r := by nlinarith [hcle n, norm_nonneg (c n)]
        _ ≤ r ^ n * r := mul_le_mul_of_nonneg_right ih hr0
  have hcn : Tendsto c atTop (𝓝 0) :=
    squeeze_zero_norm hcpow (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
  have hale : ∀ n, ‖a n‖ ≤ (n : ℝ) + ‖a 0‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ha]
      calc
        ‖1 - a n * c n‖ ≤ 1 + ‖a n‖ * ‖c n‖ := by
          simpa only [norm_one, norm_mul] using norm_sub_le (1 : ℂ) (a n * c n)
        _ ≤ 1 + ‖a n‖ := by nlinarith [hcle n, norm_nonneg (a n), norm_nonneg (c n)]
        _ ≤ ((n + 1 : ℕ) : ℝ) + ‖a 0‖ := by push_cast; linarith
  have hm : Tendsto (fun n : ℕ => ((n : ℝ) + ‖a 0‖) * r ^ n) atTop (𝓝 0) := by
    have ht := (tendsto_self_mul_const_pow_of_lt_one hr0 hr1).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul ‖a 0‖)
    simpa only [add_mul, zero_add, mul_zero] using ht
  refine ⟨hcn, squeeze_zero_norm (fun n => ?_) hm⟩
  rw [norm_mul]
  exact mul_le_mul (hale n) (hcpow n) (norm_nonneg _) (by positivity)

/-- Matrix convergence for the normalized parabolic iteration, without a discreteness assumption. -/
theorem jorgensenIterate_parabolic_tendsto (B : Auxiliary.Algebra.SpecialLinear2)
    (hB : jorgensenMatrixDefect Mobius.invariantDiscTranslationLift B < 1) :
    Tendsto (jorgensenIterate Mobius.invariantDiscTranslationLift B) atTop
      (𝓝 Mobius.invariantDiscTranslationLift) := by
  let F := jorgensenIterate Mobius.invariantDiscTranslationLift B
  have hrec n := jorgensenStep_parabolic (F n)
  have ha n : F (n + 1) 0 0 = 1 - F n 0 0 * F n 1 0 := (hrec n).1
  have hb n : F (n + 1) 0 1 = (F n 0 0) ^ 2 := (hrec n).2.1
  have hd n : F (n + 1) 1 1 = 1 + F n 0 0 * F n 1 0 := (hrec n).2.2.2
  have hc n : F (n + 1) 1 0 = -(F n 1 0) ^ 2 := (hrec n).2.2.1
  have hc0 : ‖F 0 1 0‖ < 1 := by
    rw [jorgensenMatrixDefect_parabolic] at hB
    change ‖B 1 0‖ < 1
    nlinarith [norm_nonneg (B 1 0)]
  obtain ⟨hcl, hac⟩ := jorgensen_parabolic_scalar_limits (a := fun n => F n 0 0) (c := fun n => F n 1 0) ha hc hc0
  have hal : Tendsto (fun n => F n 0 0) atTop (𝓝 1) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [ha, sub_zero] using tendsto_const_nhds.sub hac
  have hbl : Tendsto (fun n => F n 0 1) atTop (𝓝 1) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [hb, one_pow] using hal.pow 2
  have hdl : Tendsto (fun n => F n 1 1) atTop (𝓝 1) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [hd, add_zero] using (tendsto_const_nhds (x := (1 : ℂ))).add hac
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hal
  · exact hbl
  · exact hcl
  · exact hdl

/-- The diagonal recurrence forces the product of its off-diagonal coefficients to zero. -/
theorem jorgensen_diagonal_product_tendsto {p : ℕ → ℂ} {δ : ℂ}
    (hp : ∀ n, p (n + 1) = -(δ ^ 2) * (1 + p n) * p n)
    (hs : (1 + ‖p 0‖) * ‖δ‖ ^ 2 < 1) : Tendsto p atTop (𝓝 0) := by
  let s := (1 + ‖p 0‖) * ‖δ‖ ^ 2
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hstep n : ‖p (n + 1)‖ ≤ ‖δ‖ ^ 2 * (1 + ‖p n‖) * ‖p n‖ := by
    rw [hp, norm_mul, norm_mul, norm_neg, norm_pow]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    simpa only [norm_one] using norm_add_le (1 : ℂ) (p n)
  have hle : ∀ n, ‖p n‖ ≤ ‖p 0‖ := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      calc
        ‖p (n + 1)‖ ≤ ‖δ‖ ^ 2 * (1 + ‖p n‖) * ‖p n‖ := hstep n
        _ ≤ s * ‖p n‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          dsimp [s]
          nlinarith [mul_nonneg (sub_nonneg.mpr ih) (sq_nonneg ‖δ‖)]
        _ ≤ ‖p n‖ := by nlinarith [norm_nonneg (p n)]
        _ ≤ ‖p 0‖ := ih
  have hpow : ∀ n, ‖p n‖ ≤ s ^ n * ‖p 0‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        ‖p (n + 1)‖ ≤ ‖δ‖ ^ 2 * (1 + ‖p n‖) * ‖p n‖ := hstep n
        _ ≤ s * ‖p n‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          dsimp [s]
          nlinarith [mul_nonneg (sub_nonneg.mpr (hle n)) (sq_nonneg ‖δ‖)]
        _ ≤ s * (s ^ n * ‖p 0‖) := mul_le_mul_of_nonneg_left ih hs0
        _ = s ^ (n + 1) * ‖p 0‖ := by ring
  exact squeeze_zero_norm hpow (by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hs).mul_const ‖p 0‖)

/-- Both diagonal entries converge and the naturally weighted off-diagonal entries vanish. -/
theorem jorgensen_diagonal_scalar_limits {a b c d : ℕ → ℂ} {u v : ℂ}
    (huv : u * v = 1) (hdet : ∀ n, a n * d n - b n * c n = 1)
    (ha : ∀ n, a (n + 1) = u + (u - v) * b n * c n)
    (hb : ∀ n, b (n + 1) = -(u - v) * a n * b n)
    (hc : ∀ n, c (n + 1) = (u - v) * c n * d n)
    (hd : ∀ n, d (n + 1) = v - (u - v) * b n * c n)
    (hs : (1 + ‖b 0 * c 0‖) * ‖u - v‖ ^ 2 < 1) :
    Tendsto a atTop (𝓝 u) ∧ Tendsto d atTop (𝓝 v) ∧
      Tendsto (fun n => (u⁻¹) ^ n * b n) atTop (𝓝 0) ∧
      Tendsto (fun n => u ^ n * c n) atTop (𝓝 0) := by
  have hu : u ≠ 0 := by intro h; simp [h] at huv
  have hp : Tendsto (fun n => b n * c n) atTop (𝓝 0) := by
    apply jorgensen_diagonal_product_tendsto (δ := u - v) _ hs
    intro n
    rw [hb, hc]
    linear_combination -(u - v) ^ 2 * b n * c n * hdet n
  have hal : Tendsto a atTop (𝓝 u) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    have ht := (tendsto_const_nhds (x := u)).add (hp.const_mul (u - v))
    simpa only [ha, mul_assoc, mul_zero, add_zero] using ht
  have hdl : Tendsto d atTop (𝓝 v) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    have ht := (tendsto_const_nhds (x := v)).sub (hp.const_mul (u - v))
    simpa only [hd, mul_assoc, mul_zero, sub_zero] using ht
  have hδ : ‖u - v‖ < 1 := by
    nlinarith [norm_nonneg (u - v), mul_nonneg (norm_nonneg (b 0 * c 0)) (sq_nonneg ‖u - v‖)]
  refine ⟨hal, hdl, ?_, ?_⟩
  · apply jorgensen_tendsto_zero_of_recurrence
      (e := fun n => -(u - v) * (a n / u)) (z := -(u - v))
    · simpa only [div_self hu, mul_one] using (hal.div_const u).const_mul (-(u - v))
    · simpa only [norm_neg] using hδ
    · intro n
      rw [pow_succ, hb]
      field_simp
  · apply jorgensen_tendsto_zero_of_recurrence
      (e := fun n => (u - v) * u * d n) (z := u - v)
    · simpa only [mul_assoc, huv, mul_one] using hdl.const_mul ((u - v) * u)
    · exact hδ
    · intro n
      rw [pow_succ, hc]
      ring

/-- Powers of a diagonal determinant-one matrix retain the exact diagonal coefficients. -/
theorem jorgensen_diagonal_pow (A : Auxiliary.Algebra.SpecialLinear2) (h01 : A 0 1 = 0)
    (h10 : A 1 0 = 0) (n : ℕ) :
    ((A ^ n : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) = Matrix.diagonal (fun i => (A
      i i) ^ n) := by
  have hA : (A : Auxiliary.Algebra.ComplexMatrix2) = Matrix.diagonal (fun i => A i i) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10]
  rw [Matrix.SpecialLinearGroup.coe_pow, hA, Matrix.diagonal_pow]
  congr 1
  funext i
  simp only [Pi.pow_apply, Matrix.diagonal_apply_eq]

/-- The normalizing conjugations are actual matrix powers and therefore remain in the group. -/
theorem jorgensen_diagonal_conjugate (A B : Auxiliary.Algebra.SpecialLinear2) (h01 : A 0 1 = 0)
    (h10 : A 1 0 = 0) (n : ℕ) :
    ((A ^ n)⁻¹ * B * A ^ n) 0 0 = B 0 0 ∧
    ((A ^ n)⁻¹ * B * A ^ n) 0 1 = A 1 1 ^ (2 * n) * B 0 1 ∧
    ((A ^ n)⁻¹ * B * A ^ n) 1 0 = A 0 0 ^ (2 * n) * B 1 0 ∧
    ((A ^ n)⁻¹ * B * A ^ n) 1 1 = B 1 1 := by
  have hd : A 0 0 * A 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, h01, zero_mul, sub_zero] using A.det_coe
  have hp : A 0 0 ^ n * A 1 1 ^ n = 1 := by rw [← mul_pow, hd, one_pow]
  have hs (i j : Fin 2) : ((A ^ n)⁻¹ * B * A ^ n) i j =
      (Matrix.adjugate ((A ^ n : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) * (B :
        Auxiliary.Algebra.ComplexMatrix2) * ((A ^ n : Auxiliary.Algebra.SpecialLinear2) :
        Auxiliary.Algebra.ComplexMatrix2)) i j := rfl
  simp only [hs, jorgensen_diagonal_pow A h01 h10 n, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    ite_true, show ¬((0 : Fin 2) = 1) from by decide, show ¬((1 : Fin 2) = 0) from by decide,
    ite_false, neg_zero, zero_mul, mul_zero, zero_add, add_zero, two_mul, pow_add]
  constructor
  · linear_combination B 0 0 * hp
  constructor
  · ring
  constructor
  · ring
  · linear_combination B 1 1 * hp

/-- The normalized even-index diagonal iterates converge to the first generator. -/
theorem jorgensenIterate_diagonal_tendsto (A B : Auxiliary.Algebra.SpecialLinear2)
    (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) (hs : jorgensenMatrixDefect A B < 1) :
    Tendsto (fun n => (A ^ n)⁻¹ * jorgensenIterate A B (2 * n) * A ^ n) atTop (𝓝 A) := by
  let F := jorgensenIterate A B
  have hrec n := jorgensenStep_diagonal A (F n) h01 h10
  have ha n : F (n + 1) 0 0 = A 0 0 + (A 0 0 - A 1 1) * F n 0 1 * F n 1 0 := (hrec n).1
  have hb n : F (n + 1) 0 1 = -(A 0 0 - A 1 1) * F n 0 0 * F n 0 1 := (hrec n).2.1
  have hc n : F (n + 1) 1 0 = (A 0 0 - A 1 1) * F n 1 0 * F n 1 1 := (hrec n).2.2.1
  have hd n : F (n + 1) 1 1 = A 1 1 - (A 0 0 - A 1 1) * F n 0 1 * F n 1 0 := (hrec n).2.2.2
  have huv : A 0 0 * A 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, h01, zero_mul, sub_zero] using A.det_coe
  have hdet n : F n 0 0 * F n 1 1 - F n 0 1 * F n 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (F n).det_coe
  have hs' : (1 + ‖F 0 0 1 * F 0 1 0‖) * ‖A 0 0 - A 1 1‖ ^ 2 < 1 := by
    simpa only [jorgensenMatrixDefect_diagonal A B h01 h10, F, jorgensenIterate] using hs
  obtain ⟨hal, hdl, hbl, hcl⟩ := jorgensen_diagonal_scalar_limits
    (a := fun n => F n 0 0) (b := fun n => F n 0 1)
    (c := fun n => F n 1 0) (d := fun n => F n 1 1) huv hdet ha hb hc hd hs'
  have hv : A 1 1 = (A 0 0)⁻¹ := by exact eq_inv_of_mul_eq_one_right huv
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => by change n ≤ 2 * n; omega) tendsto_id
  have hconj n := jorgensen_diagonal_conjugate A (F (2 * n)) h01 h10 n
  have ha' n : ((A ^ n)⁻¹ * F (2 * n) * A ^ n) 0 0 = F (2 * n) 0 0 := (hconj n).1
  have hb' n : ((A ^ n)⁻¹ * F (2 * n) * A ^ n) 0 1 = A 1 1 ^ (2 * n) * F (2 * n) 0 1 := (hconj n).2.1
  have hc' n : ((A ^ n)⁻¹ * F (2 * n) * A ^ n) 1 0 = A 0 0 ^ (2 * n) * F (2 * n) 1 0 := (hconj n).2.2.1
  have hd' n : ((A ^ n)⁻¹ * F (2 * n) * A ^ n) 1 1 = F (2 * n) 1 1 := (hconj n).2.2.2
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  change Tendsto (fun n => ((A ^ n)⁻¹ * F (2 * n) * A ^ n) i j) atTop (𝓝 (A i j))
  fin_cases i <;> fin_cases j
  · exact (hal.comp h2n).congr' (Eventually.of_forall fun n => (ha' n).symm)
  · change Tendsto (fun n => ((A ^ n)⁻¹ * F (2 * n) * A ^ n) 0 1) atTop (𝓝 (A 0 1))
    rw [h01]
    apply (hbl.comp h2n).congr'
    exact Eventually.of_forall fun n => by
      change (A 0 0)⁻¹ ^ (2 * n) * F (2 * n) 0 1 = ((A ^ n)⁻¹ * F (2 * n) * A ^ n) 0 1
      simpa only [hv] using (hb' n).symm
  · change Tendsto (fun n => ((A ^ n)⁻¹ * F (2 * n) * A ^ n) 1 0) atTop (𝓝 (A 1 0))
    rw [h10]
    exact (hcl.comp h2n).congr' (Eventually.of_forall fun n => (hc' n).symm)
  · exact (hdl.comp h2n).congr' (Eventually.of_forall fun n => (hd' n).symm)

/-- Discreteness rules out a contracting parabolic iteration which never reaches its generator. -/
theorem jorgensen_parabolic_bound (K : Subgroup Auxiliary.Algebra.SpecialLinear2) [DiscreteTopology K]
    (B : Auxiliary.Algebra.SpecialLinear2) (hA : Mobius.invariantDiscTranslationLift ∈ K) (hB : B ∈ K)
    (hne : ∀ n, jorgensenIterate Mobius.invariantDiscTranslationLift B n ≠ Mobius.invariantDiscTranslationLift) :
    1 ≤ jorgensenMatrixDefect Mobius.invariantDiscTranslationLift B := by
  by_contra! hs
  let u : ℕ → K := fun n => ⟨_, jorgensenIterate_mem K _ B hA hB n⟩
  have he := DiscreteGroups.MatrixGroups.discrete_sequence_eventually_eq K u Mobius.invariantDiscTranslationLift
    (jorgensenIterate_parabolic_tendsto B hs)
  obtain ⟨n, hn⟩ := he.exists
  exact hne n hn

/-- The diagonal contraction contradicts discreteness in precisely the same actual group. -/
theorem jorgensen_diagonal_bound (K : Subgroup Auxiliary.Algebra.SpecialLinear2) [DiscreteTopology K]
    (A B : Auxiliary.Algebra.SpecialLinear2) (hA : A ∈ K) (hB : B ∈ K)
    (h01 : A 0 1 = 0) (h10 : A 1 0 = 0)
    (hne : ∀ n, jorgensenIterate A B n ≠ A) : 1 ≤ jorgensenMatrixDefect A B := by
  by_contra! hs
  let u : ℕ → K := fun n => ⟨(A ^ n)⁻¹ * jorgensenIterate A B (2 * n) * A ^ n,
    K.mul_mem (K.mul_mem (K.inv_mem (K.pow_mem hA n))
      (jorgensenIterate_mem K A B hA hB (2 * n))) (K.pow_mem hA n)⟩
  have he := DiscreteGroups.MatrixGroups.discrete_sequence_eventually_eq K u A (jorgensenIterate_diagonal_tendsto
    A B h01 h10 hs)
  obtain ⟨n, hn⟩ := he.exists
  apply hne (2 * n)
  change (A ^ n)⁻¹ * jorgensenIterate A B (2 * n) * A ^ n = A at hn
  calc
    jorgensenIterate A B (2 * n) = A ^ n * ((A ^ n)⁻¹ * jorgensenIterate A B (2 * n) * A ^ n) * (A ^ n)⁻¹ := by group
    _ = A ^ n * A * (A ^ n)⁻¹ := by rw [hn]
    _ = A := by group

/-- Non-elementarity prevents every finite stopping time of the actual conjugation iteration. -/
theorem jorgensenIterate_ne (A B : Auxiliary.Algebra.SpecialLinear2)
    (hf : Mobius.mobiusSpecialLinearProjection A ≠ 1) (hf2 : orderOf (Mobius.mobiusSpecialLinearProjection A) ≠ 2)
    (hH : IsNonElementary (Subgroup.closure
      ({Mobius.mobiusSpecialLinearProjection A, Mobius.mobiusSpecialLinearProjection B} : Set
        Mobius.complexMobiusGroup)))
    (n : ℕ) : jorgensenIterate A B n ≠ A := by
  intro he
  apply hH
  apply (Mobius.elementary_and_conjugation_second_iterate_eq_of_iterate_eq _ _ hf hf2 n _).1
  rw [← jorgensenIterate_projection, he]

/-- Both trace terms are invariant under simultaneous actual Mobius conjugation. -/
theorem jorgensenDefect_conjugation (f g q : Mobius.complexMobiusGroup) :
    jorgensenDefect (q * f * q⁻¹) (q * g * q⁻¹) = jorgensenDefect f g := by
  have hc : Mobius.mobiusCommutatorTrace (q * f * q⁻¹) (q * g * q⁻¹) = Mobius.mobiusCommutatorTrace f g := by
    simpa only [Mobius.mobiusCommutatorTrace, map_mul, map_inv] using
      Mobius.Classification.commutatorTrace_conjugation (Mobius.complexMobiusEquivFractionalLinear f)
        (Mobius.complexMobiusEquivFractionalLinear g) (Mobius.complexMobiusEquivFractionalLinear q)
  rw [jorgensenDefect, Mobius.mobiusSquaredTrace_conjugation, hc]
  rfl

/-- A genuine common boundary fixed point makes a two-generator group elementary. -/
theorem jorgensen_elementary_of_common_fixed (f g : Mobius.complexMobiusGroup) (z : Mobius.ExtendedComplex)
    (hf : f • z = z) (hg : g • z = z) :
    IsElementary (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)) := by
  have hle : Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup) ≤
      MulAction.stabilizer Mobius.complexMobiusGroup z := by
    apply (Subgroup.closure_le _).mpr
    intro h hh
    rcases Set.mem_insert_iff.mp hh with rfl | hh
    · exact hf
    · exact Set.mem_singleton_iff.mp hh ▸ hg
  exact isElementary_of_boundary_fixed _ z (fun h => hle h.property)

/-- In a non-elementary two-generator group neither generator can be the identity. -/
theorem jorgensen_left_ne_one (f g : Mobius.complexMobiusGroup)
    (hH : IsNonElementary (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup))) : f ≠ 1 := by
  intro hf
  subst f
  apply hH
  by_cases hg : g = 1
  · exact jorgensen_elementary_of_common_fixed 1 g ∞ (by simp) (by simp [hg])
  · obtain ⟨z, hz⟩ := mobius_nonidentity_boundary_fixed_exists g hg
    exact jorgensen_elementary_of_common_fixed 1 g z (by simp) hz

/-- An involution satisfies the desired lower bound directly, with no iteration needed. -/
theorem jorgensen_bound_of_order_two (f g : Mobius.complexMobiusGroup) (hf : f ≠ 1)
    (hf2 : orderOf f = 2) : 1 ≤ jorgensenDefect f g := by
  have ht := (Mobius.mobius_orderOf_eq_two_iff_squaredTrace_eq_zero f hf).mp hf2
  rw [jorgensenDefect, ht]
  norm_num only [zero_sub, norm_neg, Complex.norm_ofNat]
  linarith [norm_nonneg (Mobius.mobiusCommutatorTrace f g - 2)]

/-- The lower bound in every normalized standard form, with its true discrete preimage group. -/
theorem jorgensen_bound_standard (k : ℂˣ) (g : Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({Mobius.mobiusStandardElement k, g} : Set
      Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure ({Mobius.mobiusStandardElement k, g} : Set Mobius.complexMobiusGroup))) :
    1 ≤ jorgensenDefect (Mobius.mobiusStandardElement k) g := by
  have hf := jorgensen_left_ne_one _ _ hH
  by_cases hf2 : orderOf (Mobius.mobiusStandardElement k) = 2
  · exact jorgensen_bound_of_order_two _ g hf hf2
  let H := Subgroup.closure ({Mobius.mobiusStandardElement k, g} : Set Mobius.complexMobiusGroup)
  let K := H.comap Mobius.mobiusSpecialLinearProjection
  let _ : DiscreteTopology K := Mobius.discreteMobius_preimage H hD
  have hmemf : Mobius.mobiusStandardElement k ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hmemg : g ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨B, hB⟩ := Mobius.mobiusSpecialLinearProjection_surjective g
  have hBK : B ∈ K := by change Mobius.mobiusSpecialLinearProjection B ∈ H; rwa [hB]
  by_cases hk : k = 1
  · subst k
    have hA : Mobius.mobiusSpecialLinearProjection Mobius.invariantDiscTranslationLift =
      Mobius.mobiusStandardElement 1 :=
      Mobius.invariantDiscTranslationLift_projection
    have hAK : Mobius.invariantDiscTranslationLift ∈ K := by
      change Mobius.mobiusSpecialLinearProjection Mobius.invariantDiscTranslationLift ∈ H
      rwa [hA]
    have hn : ∀ n, jorgensenIterate Mobius.invariantDiscTranslationLift B n ≠ Mobius.invariantDiscTranslationLift := by
      intro n
      apply jorgensenIterate_ne
      · rwa [hA]
      · rwa [hA]
      · rwa [hA, hB]
    have hb := jorgensen_parabolic_bound K B hAK hBK hn
    rw [← jorgensenDefect_representatives, hA, hB] at hb
    exact hb
  · obtain ⟨A, hA, u, _, ha01, ha10, _⟩ := Mobius.Classification.specialStandard_lift k
    have hA' : Mobius.mobiusSpecialLinearProjection A = Mobius.mobiusStandardElement k :=
      (Mobius.mobiusSpecialLinearProjection_eq_iff A _).mpr (by simpa only [Mobius.mobiusStandardElement_equiv]
        using hA)
    have hk' : (k : ℂ) ≠ 1 := by intro he; exact hk (Units.ext he)
    have h01 : A 0 1 = 0 := by simpa only [ite_eq_right hk', mul_zero] using ha01
    have hAK : A ∈ K := by change Mobius.mobiusSpecialLinearProjection A ∈ H; rwa [hA']
    have hn : ∀ n, jorgensenIterate A B n ≠ A := by
      intro n
      apply jorgensenIterate_ne
      · rwa [hA']
      · rwa [hA']
      · rwa [hA', hB]
    have hb := jorgensen_diagonal_bound K A B hAK hBK h01 ha10 hn
    rw [← jorgensenDefect_representatives, hA', hB] at hb
    exact hb

/-- The actual two-generator subgroup is transported exactly by simultaneous conjugation. -/
theorem jorgensen_generated_conjugation (f g q : Mobius.complexMobiusGroup) :
    (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)).map (MulAut.conj q).toMonoidHom =
      Subgroup.closure ({q * f * q⁻¹, q * g * q⁻¹} : Set Mobius.complexMobiusGroup) := by
  simp only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
  rfl

/-- Jorgensen's inequality on the actual Mobius group. -/
theorem one_le_jorgensenDefect_of_discrete_nonElementary (f g : Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup))) :
    1 ≤ jorgensenDefect f g := by
  have hf := jorgensen_left_ne_one f g hH
  obtain ⟨k, hk⟩ := Mobius.mobius_nonidentity_conjugate_standard f hf
  obtain ⟨q, hq⟩ := isConj_iff.mp hk
  let H := Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)
  let _ : DiscreteTopology H := hD
  have hmap := jorgensen_generated_conjugation f g q
  have hD' : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({q * f * q⁻¹, q * g * q⁻¹} : Set Mobius.complexMobiusGroup)) := by
    rw [← hmap]
    exact DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q H
  have hH' := hH.conjugation q
  rw [hmap, hq] at hH'
  rw [hq] at hD'
  have hb := jorgensen_bound_standard k (q * g * q⁻¹) hD' hH'
  rw [← hq, jorgensenDefect_conjugation] at hb
  exact hb

/-- The same inequality for determinant-one matrices generating a discrete matrix subgroup. -/
theorem specialLinear_jorgensen_inequality (A B : Auxiliary.Algebra.SpecialLinear2)
    (hD : DiscreteTopology (Subgroup.closure ({A, B} : Set Auxiliary.Algebra.SpecialLinear2)))
    (hH : IsNonElementary (Subgroup.closure
      ({Mobius.mobiusSpecialLinearProjection A, Mobius.mobiusSpecialLinearProjection B} : Set
        Mobius.complexMobiusGroup))) :
    1 ≤ jorgensenMatrixDefect A B := by
  let K := Subgroup.closure ({A, B} : Set Auxiliary.Algebra.SpecialLinear2)
  let _ : DiscreteTopology K := hD
  have hm : K.map Mobius.mobiusSpecialLinearProjection = Subgroup.closure
      ({Mobius.mobiusSpecialLinearProjection A, Mobius.mobiusSpecialLinearProjection B} : Set
        Mobius.complexMobiusGroup) := by
    simp only [K, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
  have hD' := Mobius.discreteSpecialLinear_image K
  rw [hm] at hD'
  rw [← jorgensenDefect_representatives]
  exact one_le_jorgensenDefect_of_discrete_nonElementary _ _ hD' hH

/-- An actual discrete non-elementary pair attains the lower bound. -/
theorem exists_discrete_nonElementary_jorgensenDefect_eq_one :
    ∃ f g : Mobius.complexMobiusGroup,
      Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)) ∧
      IsNonElementary (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)) ∧
      jorgensenDefect f g = 1 := jorgensenSharpness_exists

/-- The numerical lower bound is the attained least defect among all actual admissible pairs. -/
theorem isLeast_jorgensenDefect :
    IsLeast {r : ℝ | ∃ f g : Mobius.complexMobiusGroup,
      Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)) ∧
      IsNonElementary (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)) ∧
      r = jorgensenDefect f g} 1 := by
  constructor
  · obtain ⟨f, g, hD, hH, he⟩ := exists_discrete_nonElementary_jorgensenDefect_eq_one
    exact ⟨f, g, hD, hH, he.symm⟩
  · rintro r ⟨f, g, hD, hH, rfl⟩
    exact one_le_jorgensenDefect_of_discrete_nonElementary f g hD hH

end LowDimensionalTopology.Geometry.DiscreteGroups
