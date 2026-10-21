/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementFunctions
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ConformalTypes
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The real special-linear trace survives native conjugation. -/
theorem hSL_trace_conjugation (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace ((B * A * B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) := by
  change Matrix.trace (((B*A : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
    ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) = _
  rw [Matrix.trace_mul_comm]
  change Matrix.trace ((B⁻¹*(B*A) : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = _
  simp

theorem hSL_trace_inverse (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.trace_fin_two, add_comm]

/--
In the literal native half-plane.
At trace zero the region is the genuine fixed-center set, whose singleton
characterization is proved separately. At other traces the strict source inequality is retained.
-/
def hCanonicalRegion (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Set ℍ :=
  if Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) = 0 then {z | A • z = z}
  else {z | Real.sinh (dist z (A • z) / 2) < |Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ)| / 2}

theorem hCanonicalRegion_of_trace_ne_zero (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0) :
    hCanonicalRegion A = {z | Real.sinh (dist z (A • z) / 2) <
      |Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ)| / 2} := by
  simp only [hCanonicalRegion, ite_eq_right ht]

theorem hCanonicalRegion_of_trace_zero (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) = 0) :
    hCanonicalRegion A = {z | A • z = z} := by simp only [hCanonicalRegion, ite_eq_left ht]

/-- The actual native conjugation-equivariance part. -/
theorem hCanonicalRegion_conjugation_mem (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    B • z ∈ hCanonicalRegion (B*A*B⁻¹) ↔ z ∈ hCanonicalRegion A := by
  unfold hCanonicalRegion
  rw [hSL_trace_conjugation]
  split_ifs with ht
  · change ((B*A*B⁻¹) • (B • z) = B • z) ↔ A • z = z
    simp only [mul_smul, inv_smul_smul]
    exact (MulAction.toPerm B).injective.eq_iff
  · change (Real.sinh (dist (B•z) ((B*A*B⁻¹) • (B•z)) / 2) < _) ↔ _
    have hd : dist (B•z) ((B*A*B⁻¹) • (B•z)) = dist z (A•z) := by
      simp only [mul_smul, inv_smul_smul]
      exact (isometry_smul ℍ B).dist_eq z (A•z)
    rw [hd]
    rfl

theorem hCanonicalRegion_conjugation (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    hCanonicalRegion (B*A*B⁻¹) = (fun z : ℍ => B•z) '' hCanonicalRegion A := by
  ext z
  constructor
  · intro hz
    refine ⟨B⁻¹•z, ?_, by simp⟩
    exact (hCanonicalRegion_conjugation_mem A B (B⁻¹•z)).mp (by simpa using hz)
  · rintro ⟨z, hz, rfl⟩
    exact (hCanonicalRegion_conjugation_mem A B z).mpr hz

/-- Inversion of the actual map leaves its canonical region unchanged. -/
theorem hCanonicalRegion_inverse (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    hCanonicalRegion A⁻¹ = hCanonicalRegion A := by
  unfold hCanonicalRegion
  rw [hSL_trace_inverse]
  split_ifs with ht
  · ext z
    change (A⁻¹ • z = z) ↔ A • z = z
    constructor
    · intro h
      have he := congrArg (fun w => A • w) h
      simpa using he.symm
    · intro h
      have he := congrArg (fun w => A⁻¹ • w) h
      simpa using he.symm
  · ext z
    change Real.sinh (dist z (A⁻¹ • z) / 2) < _ ↔ _
    have hd : dist z (A⁻¹ • z) = dist z (A • z) := by
      rw [← (isometry_smul ℍ A).dist_eq z (A⁻¹•z)]
      simp only [smul_inv_smul, dist_comm]
    rw [hd]
    rfl


/-- A trace-zero real special-linear matrix has a nonzero lower-left coefficient. -/
theorem hSL_trace_zero_lowerLeft_ne_zero (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) = 0) : A 1 0 ≠ 0 := by
  have hd : A 1 1 = -A 0 0 := by rw [Matrix.trace_fin_two] at ht; linarith
  intro hc
  have he := A.det_coe
  rw [Matrix.det_fin_two, hd, hc] at he
  nlinarith [sq_nonneg (A 0 0)]

/-- The genuine fixed center of a half-turn, expressed through its real matrix entries. -/
def hHalfTurnCenter (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) = 0) : ℍ :=
  metricProbe (A 0 0 / A 1 0) (1 / |A 1 0|)
    (one_div_pos.mpr (abs_pos.mpr (hSL_trace_zero_lowerLeft_ne_zero A ht)))

/-- A genuine trace-zero map has exactly one fixed point in the actual upper half-plane. -/
theorem hSL_trace_zero_fixed_iff (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) = 0) (z : ℍ) :
    A • z = z ↔ z = hHalfTurnCenter A ht := by
  have hc := hSL_trace_zero_lowerLeft_ne_zero A ht
  have hd : A 1 1 = -A 0 0 := by rw [Matrix.trace_fin_two] at ht; linarith
  have hdet : -(A 0 0) ^ 2 - A 0 1 * A 1 0 = 1 := by
    have h := A.det_coe
    rw [Matrix.det_fin_two, hd] at h
    nlinarith [h]
  rw [hSL_fixed_iff]
  have hcoords : z = hHalfTurnCenter A ht ↔
      A 1 0 * z.re = A 0 0 ∧ |A 1 0| * z.im = 1 := by
    constructor
    · intro hz
      subst z
      change A 1 0 * (A 0 0 / A 1 0) = A 0 0 ∧ |A 1 0| * (1 / |A 1 0|) = 1
      constructor <;> field_simp
    · rintro ⟨hx, hy⟩
      apply UpperHalfPlane.ext
      apply Complex.ext
      · change z.re = A 0 0 / A 1 0
        apply (eq_div_iff hc).mpr
        linarith
      · change z.im = 1 / |A 1 0|
        apply (eq_div_iff (abs_ne_zero.mpr hc)).mpr
        linarith
  rw [hcoords]
  constructor
  · intro he
    have hre := congrArg Complex.re he
    have him := congrArg Complex.im he
    norm_num [pow_two, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, hd] at hre him
    have hx : A 1 0 * z.re = A 0 0 := by
      have hp : z.im * (A 1 0 * z.re - A 0 0) = 0 := by nlinarith [him]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left z.im_ne_zero)
    refine ⟨hx, ?_⟩
    have hsx := congrArg (fun t : ℝ => t ^ 2) hx
    have hxy := congrArg (fun t : ℝ => A 0 0 * t) hx
    have hrc := congrArg (fun t : ℝ => A 1 0 * t) hre
    have hsy : (A 1 0) ^ 2 * z.im ^ 2 = 1 := by nlinarith [hrc, hdet]
    apply (sq_eq_sq₀ (show 0 ≤ |A 1 0| * z.im by positivity) (show (0:ℝ) ≤ 1 by norm_num)).mp
    simpa only [mul_pow, sq_abs, one_pow] using hsy
  · rintro ⟨hx, hy⟩
    apply Complex.ext
    · norm_num [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re, hd]
      have hsx := congrArg (fun t : ℝ => t ^ 2) hx
      have hsy := congrArg (fun t : ℝ => t ^ 2) hy
      have hxy := congrArg (fun t : ℝ => A 0 0 * t) hx
      rw [mul_pow, sq_abs] at hsy
      apply (mul_left_cancel₀ hc)
      nlinarith [hdet]
    · norm_num [pow_two, Complex.add_im, Complex.sub_im, Complex.mul_im, hd]
      have hprod := congrArg (fun t : ℝ => t * z.im) hx
      nlinarith [hprod]

/-- The order-two clause is a literal singleton with its genuine native center. -/
theorem hCanonicalRegion_halfTurn (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) = 0) :
    hCanonicalRegion A = {hHalfTurnCenter A ht} := by
  rw [hCanonicalRegion_of_trace_zero A ht]
  ext z
  exact hSL_trace_zero_fixed_iff A ht z


/-- The two opposite real determinant-one representatives have exactly the same native action. -/
theorem hSL_neg_smul (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    (-A) • z = A • z := by
  apply UpperHalfPlane.ext
  simp only [UpperHalfPlane.coe_specialLinearGroup_apply, Algebra.algebraMap_self_apply]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Complex.ofReal_neg, neg_mul, ← neg_add,
    neg_div_neg_eq]

/-- Trace zero is genuinely the native half-turn condition, not a new definition of an order. -/
theorem hSL_trace_zero_square (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) = 0) : A * A = -1 := by
  have hd : A 1 1 = -A 0 0 := by rw [Matrix.trace_fin_two] at ht; linarith
  have hdet : (A 0 0) ^ 2 + A 0 1 * A 1 0 = -1 := by
    have h := A.det_coe
    rw [Matrix.det_fin_two, hd] at h
    nlinarith
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.neg_apply, Matrix.one_apply] <;> norm_num
  all_goals try rw [hd]
  · nlinarith [hdet]
  · ring
  · ring
  · nlinarith [hdet]

/-- The displayed half-turn has exact order two as an actual permutation of the native plane. -/
theorem hSL_trace_zero_order (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) = 0) :
    orderOf (MulAction.toPerm A : Equiv.Perm ℍ) = 2 := by
  have hs : (MulAction.toPerm A : Equiv.Perm ℍ) ^ 2 = 1 := by
    apply Equiv.ext
    intro z
    rw [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    change A • (A • z) = z
    rw [← mul_smul, hSL_trace_zero_square A ht, hSL_neg_smul]
    exact one_smul _ _
  have hn : (MulAction.toPerm A : Equiv.Perm ℍ) ≠ 1 := by
    intro he
    let v := hHalfTurnCenter A ht
    let w := metricProbe v.re (2 * v.im) (by have hp := v.im_pos; positivity)
    have hw : A • w = w := congrArg (fun e : Equiv.Perm ℍ => e w) he
    have hwe := (hSL_trace_zero_fixed_iff A ht w).mp hw
    have hi := congrArg UpperHalfPlane.im hwe
    change 2 * v.im = v.im at hi
    linarith [v.im_pos]
  exact orderOf_eq_prime hs hn

/-- Canonical regions are independent of the sign choice of a real representative. -/
theorem hCanonicalRegion_neg (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    hCanonicalRegion (-A) = hCanonicalRegion A := by
  have ht : Matrix.trace ((-A : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      - Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg]
  unfold hCanonicalRegion
  rw [ht]
  simp only [neg_eq_zero, abs_neg]
  split_ifs
  · ext z
    change ((-A) • z = z) ↔ A • z = z
    rw [hSL_neg_smul]
  · ext z
    change Real.sinh (dist z ((-A) • z) / 2) < _ ↔ _
    rw [hSL_neg_smul]
    rfl


/--
For the actual geometric map, the exceptional case is
exactly the trace-zero branch, with no projective representative ambiguity.
-/
theorem realSLMobius_order_two_iff_trace_zero (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hn : realSLMobius A ≠ 1) :
    orderOf (realSLMobius A) = 2 ↔ Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  rw [Mobius.mobius_orderOf_eq_two_iff_squaredTrace_eq_zero _ hn, realSLMobius_squaredTrace]
  constructor
  · intro h
    have hr : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 = 0 := by exact_mod_cast h
    nlinarith [sq_nonneg (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ))]
  · intro h
    rw [h]
    norm_num

/-- The order-two branch is exactly the geometric singleton, for the actual Mobius map. -/
theorem hCanonicalRegion_of_order_two (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hn : realSLMobius A ≠ 1) (ho : orderOf (realSLMobius A) = 2) :
    ∃ v : ℍ, (∀ z : ℍ, A • z = z ↔ z = v) ∧ hCanonicalRegion A = {v} := by
  have ht := (realSLMobius_order_two_iff_trace_zero A hn).mp ho
  exact ⟨hHalfTurnCenter A ht, hSL_trace_zero_fixed_iff A ht, hCanonicalRegion_halfTurn A ht⟩

/-- Away from order two, the actual source inequality is the native region definition. -/
theorem hCanonicalRegion_of_order_ne_two (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hn : realSLMobius A ≠ 1) (ho : orderOf (realSLMobius A) ≠ 2) :
    hCanonicalRegion A = {z | Real.sinh (dist z (A•z) / 2) <
      |Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ)| / 2} := by
  apply hCanonicalRegion_of_trace_ne_zero
  intro ht
  exact ho ((realSLMobius_order_two_iff_trace_zero A hn).mpr ht)


/-- The actual parabolic standard canonical region is a genuine horocyclic half-plane. -/
theorem hCanonicalRegion_translation (t : ℝ) :
    hCanonicalRegion (hTranslationSL t) = {z : ℍ | |t| / 2 < z.im} := by
  rw [hCanonicalRegion_of_trace_ne_zero _ (by norm_num [hTranslationSL, Matrix.trace_fin_two])]
  ext z
  change Real.sinh (dist z (hTranslationSL t • z) / 2) < _ ↔ _
  rw [translation_half_displacement]
  norm_num [hTranslationSL, Matrix.trace_fin_two]
  rw [div_lt_iff₀ (by positivity : 0 < 2 * z.im)]
  constructor <;> intro h <;> linarith

end LowDimensionalTopology.Geometry.Hyperbolic
