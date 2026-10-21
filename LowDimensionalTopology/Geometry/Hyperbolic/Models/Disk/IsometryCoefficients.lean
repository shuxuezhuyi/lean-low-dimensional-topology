/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.IsometryClassification
public import LowDimensionalTopology.Geometry.Auxiliary.Algebra.Matrix
public import LowDimensionalTopology.Geometry.Mobius.MatrixRepresentation
public import Mathlib.Tactic

/-!
# Native disc isometry coefficients and matrix displacement
-/

@[expose] public section
open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- The diagonal coefficient obtained by conjugating an actual real SL2 matrix by Cayley. -/
def discCoefficientA (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ℂ :=
  ⟨(s 0 0 + s 1 1) / 2,(s 0 1 - s 1 0) / 2⟩

/-- The lower-left coefficient in the source disc convention. -/
def discCoefficientC (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ℂ :=
  ⟨(s 0 0 - s 1 1) / 2,(s 0 1 + s 1 0) / 2⟩

theorem disc_coefficients_unit (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ‖discCoefficientA s‖ ^ 2 - ‖discCoefficientC s‖ ^ 2 = 1 := by
  have hd := s.property
  rw [Matrix.det_fin_two] at hd
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply,discCoefficientA,discCoefficientC]
  nlinarith

/-- The native fractional-linear denominator is nonzero throughout the genuine disc. -/
theorem disc_coefficient_denom_ne_zero {a c : ℂ} (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1) (z : 𝔻) :
    c * z + conj a ≠ 0 := by
  have hca : ‖c‖ < ‖a‖ := by nlinarith [norm_nonneg a,norm_nonneg c]
  have hlt : ‖c * (z : ℂ)‖ < ‖a‖ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg c) z.norm_lt_one.le).trans_lt hca
  intro hz
  have he : c * (z : ℂ) = -conj a := eq_neg_of_add_eq_zero_left hz
  rw [he,norm_neg,Complex.norm_conj] at hlt
  exact (lt_irrefl _ hlt)

/-- The genuine native disc isometry induced by a real determinant-one matrix. -/
def discSL2Action (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : 𝔻) : 𝔻 :=
  halfPlaneToDisc (s • discToHalfPlane z)

theorem discSL2Action_isometry (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    letI := discHyperbolicMetric; Isometry (discSL2Action s) := by
  let := discHyperbolicMetric
  exact cayley_isometry.comp ((isometry_smul ℍ s).comp inverse_cayley_isometry)

theorem discSL2Action_coe (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : 𝔻) :
    (discSL2Action s z : ℂ) =
      (discCoefficientA s * z + conj (discCoefficientC s)) /
        (discCoefficientC s * z + conj (discCoefficientA s)) := by
  have h₁ := inverseCayley_denom_ne_zero z
  have h₂ := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ s) (discToHalfPlane z)
  change (s 1 0 : ℂ) * (discToHalfPlane z : ℂ) + s 1 1 ≠ 0 at h₂
  have h₃ := cayley_denom_ne_zero (s • discToHalfPlane z)
  have h₄ := disc_coefficient_denom_ne_zero (disc_coefficients_unit s) z
  change cayleyFormula ((s • discToHalfPlane z : ℍ) : ℂ) = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self_apply]
  change cayleyFormula (((s 0 0 : ℂ) * inverseCayleyFormula z + s 0 1) /
    ((s 1 0 : ℂ) * inverseCayleyFormula z + s 1 1)) = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply] at h₃
  simp only [Algebra.algebraMap_self_apply] at h₃
  change (((s 0 0 : ℂ) * inverseCayleyFormula z + s 0 1) /
    ((s 1 0 : ℂ) * inverseCayleyFormula z + s 1 1)) + Complex.I ≠ 0 at h₃
  change (s 1 0 : ℂ) * inverseCayleyFormula z + s 1 1 ≠ 0 at h₂
  rw [cayleyFormula]
  apply (div_eq_div_iff h₃ h₄).mpr
  field_simp [h₂]
  unfold inverseCayleyFormula
  field_simp [h₁]
  have hD : Complex.I * (1 + (z : ℂ)) * (s 1 0 : ℂ) + (1 - (z : ℂ)) * (s 1 1 : ℂ) ≠ 0 := by
    have he : Complex.I * (1 + (z : ℂ)) * (s 1 0 : ℂ) + (1 - (z : ℂ)) * (s 1 1 : ℂ) =
        ((s 1 0 : ℂ) * inverseCayleyFormula z + s 1 1) * (1 - (z : ℂ)) := by
      unfold inverseCayleyFormula
      field_simp [h₁]
    rw [he]
    exact mul_ne_zero h₂ h₁
  field_simp [hD]
  apply Complex.ext <;>
    simp [discCoefficientA,discCoefficientC,Complex.mul_re,Complex.mul_im] <;> ring

/-- The actual inverse coefficient construction; the source norm constraint is precisely det=1. -/
def discCoefficientsToSL (a c : ℂ) (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1) :
    Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![a.re + c.re,a.im + c.im;c.im - a.im,a.re - c.re],by
    rw [Matrix.det_fin_two]
    change (a.re + c.re) * (a.re - c.re) - (a.im + c.im) * (c.im - a.im) = 1
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,Complex.normSq_apply,
      Complex.normSq_apply] at h
    nlinarith⟩

theorem discCoefficientsToSL_A (a c : ℂ) (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1) :
    discCoefficientA (discCoefficientsToSL a c h) = a := by
  apply Complex.ext <;> simp [discCoefficientA,discCoefficientsToSL]; ring

theorem discCoefficientsToSL_C (a c : ℂ) (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1) :
    discCoefficientC (discCoefficientsToSL a c h) = c := by
  apply Complex.ext <;> simp [discCoefficientC,discCoefficientsToSL]; ring

/-- Native conjugation preserves the genuine disc. -/
def discConjugate (z : 𝔻) : 𝔻 :=
  Complex.UnitDisc.mk (conj (z : ℂ)) (by simpa only [Complex.norm_conj] using z.norm_lt_one)

theorem discConjugate_coe (z : 𝔻) : (discConjugate z : ℂ) = conj (z : ℂ) := rfl

theorem discToHalfPlane_conjugate (z : 𝔻) :
    discToHalfPlane (discConjugate z) = UpperHalfPlane.J • discToHalfPlane z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_J_smul]
  change inverseCayleyFormula (conj (z : ℂ)) = -conj (inverseCayleyFormula z)
  simp only [inverseCayleyFormula,map_div₀,map_mul,map_sub,map_add,map_one,
    Complex.conj_I,neg_mul,neg_neg]

theorem discConjugate_isometry :
    letI := discHyperbolicMetric; Isometry discConjugate := by
  let := discHyperbolicMetric
  apply Isometry.of_dist_eq
  intro z w
  change dist (discToHalfPlane (discConjugate z)) (discToHalfPlane (discConjugate w)) =
    dist (discToHalfPlane z) (discToHalfPlane w)
  rw [discToHalfPlane_conjugate,discToHalfPlane_conjugate]
  exact realGL_distance UpperHalfPlane.J _ _

/-- Every native disc isometry is the actual Cayley conjugate of a real determinant-one map,
possibly followed on its input by native complex conjugation. -/
theorem disc_isometry_exists_sl2_or_conjugate {f : 𝔻 → 𝔻} :
    letI := discHyperbolicMetric
    Isometry f → ∃ s : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      f = discSL2Action s ∨ f = discSL2Action s ∘ discConjugate := by
  let := discHyperbolicMetric
  intro hf
  obtain ⟨s,hs | hs⟩ := isometry_exists_sl2_or_reflected (disc_isometry_conjugate hf)
  · refine ⟨s,Or.inl ?_⟩
    funext z
    apply discToHalfPlane_injective
    have he := congrFun hs (discToHalfPlane z)
    simpa only [discMapConjugate,discSL2Action,Function.comp_def,
      halfPlaneToDisc_discToHalfPlane,discToHalfPlane_halfPlaneToDisc] using he
  · refine ⟨s,Or.inr ?_⟩
    funext z
    apply discToHalfPlane_injective
    have he := congrFun hs (discToHalfPlane z)
    simpa only [discMapConjugate,discSL2Action,Function.comp_def,
      halfPlaneToDisc_discToHalfPlane,discToHalfPlane_halfPlaneToDisc,
      discToHalfPlane_conjugate] using he

/-- The source's fractional-linear disc formula with arbitrary normalized coefficients. -/
def discCoefficientAction (a c : ℂ) (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1) : 𝔻 → 𝔻 :=
  discSL2Action (discCoefficientsToSL a c h)

theorem discCoefficientAction_coe (a c : ℂ) (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1) (z : 𝔻) :
    (discCoefficientAction a c h z : ℂ) = (a * z + conj c) / (c * z + conj a) := by
  rw [discCoefficientAction,discSL2Action_coe,discCoefficientsToSL_A,discCoefficientsToSL_C]

theorem discCoefficientAction_isometry (a c : ℂ) (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1) :
    letI := discHyperbolicMetric; Isometry (discCoefficientAction a c h) :=
  discSL2Action_isometry _

/-- Complete native disc isometry classification in the source's normalized complex coefficients. -/
theorem disc_isometry_iff_coefficient_formula (f : 𝔻 → 𝔻) :
    letI := discHyperbolicMetric
    Isometry f ↔ ∃ a c : ℂ, ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1 ∧
      ((∀ z : 𝔻, (f z : ℂ) = (a * z + conj c) / (c * z + conj a)) ∨
        (∀ z : 𝔻, (f z : ℂ) = (a * conj (z : ℂ) + conj c) / (c * conj (z : ℂ) + conj a))) := by
  let := discHyperbolicMetric
  constructor
  · intro hf
    obtain ⟨s,hs | hs⟩ := disc_isometry_exists_sl2_or_conjugate hf
    · refine ⟨discCoefficientA s,discCoefficientC s,disc_coefficients_unit s,Or.inl ?_⟩
      intro z
      rw [hs,discSL2Action_coe]
    · refine ⟨discCoefficientA s,discCoefficientC s,disc_coefficients_unit s,Or.inr ?_⟩
      intro z
      rw [hs,Function.comp_apply,discSL2Action_coe,discConjugate_coe]
  · rintro ⟨a,c,h,hf | hf⟩
    · have he : f = discCoefficientAction a c h := by
        funext z
        apply Complex.UnitDisc.coe_injective
        rw [discCoefficientAction_coe,hf]
      rw [he]
      exact discCoefficientAction_isometry a c h
    · have he : f = discCoefficientAction a c h ∘ discConjugate := by
        funext z
        apply Complex.UnitDisc.coe_injective
        rw [Function.comp_apply,discCoefficientAction_coe,discConjugate_coe,hf]
      rw [he]
      exact (discCoefficientAction_isometry a c h).comp discConjugate_isometry

/-- A normalized coefficient cannot vanish in the diagonal position. -/
theorem disc_coefficientA_ne_zero {a c : ℂ} (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1) : ‖a‖ ≠ 0 := by
  intro ha
  rw [ha] at h
  nlinarith [sq_nonneg ‖c‖]

theorem discCoefficientAction_origin_norm_sq (a c : ℂ) (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1) :
    ‖(discCoefficientAction a c h 0 : ℂ)‖ ^ 2 = ‖c‖ ^ 2 / ‖a‖ ^ 2 := by
  rw [discCoefficientAction_coe]
  simp [div_pow]

theorem discCoefficientAction_origin_one_sub_norm_sq (a c : ℂ)
    (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1) :
    1 - ‖(discCoefficientAction a c h 0 : ℂ)‖ ^ 2 = 1 / ‖a‖ ^ 2 := by
  rw [discCoefficientAction_origin_norm_sq]
  field_simp [disc_coefficientA_ne_zero h]
  linarith

/-- The actual native origin displacement determines both normalized coefficient moduli. -/
theorem discCoefficientAction_half_displacement (a c : ℂ) (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1) :
    ‖a‖ = Real.cosh (discPathDist 0 (discCoefficientAction a c h 0) / 2) ∧
      ‖c‖ = Real.sinh (discPathDist 0 (discCoefficientAction a c h 0) / 2) := by
  have hs := disc_sinh_half_distance_sq 0 (discCoefficientAction a c h 0)
  have hc := disc_cosh_half_distance_sq 0 (discCoefficientAction a c h 0)
  simp only [Complex.UnitDisc.coe_zero,zero_sub,norm_neg,norm_zero,zero_pow (by norm_num : 2 ≠ 0),
    sub_zero,one_mul,zero_mul,norm_one,one_pow] at hs hc
  rw [discCoefficientAction_origin_one_sub_norm_sq,discCoefficientAction_origin_norm_sq] at hs
  rw [discCoefficientAction_origin_one_sub_norm_sq] at hc
  have haN := disc_coefficientA_ne_zero h
  have hs' : Real.sinh (discPathDist 0 (discCoefficientAction a c h 0) / 2) ^ 2 = ‖c‖ ^ 2 := by
    rw [hs]
    field_simp [haN]
  have hc' : Real.cosh (discPathDist 0 (discCoefficientAction a c h 0) / 2) ^ 2 = ‖a‖ ^ 2 := by
    rw [hc]
    field_simp
  have hd : 0 ≤ discPathDist 0 (discCoefficientAction a c h 0) := by
    rw [discPathDist_eq_halfPlane]
    exact dist_nonneg
  exact ⟨(sq_eq_sq₀ (norm_nonneg a) (Real.cosh_pos _).le).mp hc'.symm,
    (sq_eq_sq₀ (norm_nonneg c) (Real.sinh_nonneg_iff.mpr (by positivity))).mp hs'.symm⟩

/-- The genuine normalized source disc matrix. -/
def discIsometryMatrix (a c : ℂ) : Auxiliary.Algebra.ComplexMatrix2 := !![a,conj c;c,conj a]

theorem discIsometryMatrix_det (a c : ℂ) (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1) :
    (discIsometryMatrix a c).det = 1 := by
  rw [Matrix.det_fin_two]
  change a * conj a - conj c * c = 1
  have h' : Complex.normSq a - Complex.normSq c = 1 := by
    simpa only [Complex.normSq_eq_norm_sq] using h
  rw [mul_comm (conj c) c,Complex.mul_conj,Complex.mul_conj]
  exact_mod_cast h'

theorem discIsometryMatrix_norm_sq (a c : ℂ) :
    Auxiliary.Algebra.matrixNorm (discIsometryMatrix a c) ^ 2 = 2 * (‖a‖ ^ 2 + ‖c‖ ^ 2) := by
  rw [Auxiliary.Algebra.matrixNorm_sq]
  simp only [discIsometryMatrix,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Complex.norm_conj]
  ring

/-- The actual normalized Frobenius norm equals twice the cosh of the native origin displacement. -/
theorem discIsometryMatrix_norm_displacement (a c : ℂ) (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1) :
    Auxiliary.Algebra.matrixNorm (discIsometryMatrix a c) ^ 2 =
      2 * Real.cosh (discPathDist 0 (discCoefficientAction a c h 0)) := by
  obtain ⟨ha,hc⟩ := discCoefficientAction_half_displacement a c h
  rw [discIsometryMatrix_norm_sq,ha,hc]
  have he := Real.cosh_two_mul (discPathDist 0 (discCoefficientAction a c h 0) / 2)
  rw [show 2 * (discPathDist 0 (discCoefficientAction a c h 0) / 2) =
    discPathDist 0 (discCoefficientAction a c h 0) by ring] at he
  nlinarith [Real.cosh_sq_sub_sinh_sq (discPathDist 0 (discCoefficientAction a c h 0) / 2)]

/-- The modulus of the real-action quotient is independent of its holomorphic branch. -/
theorem realGL_coe_norm (g : GL (Fin 2) ℝ) (z : ℍ) :
    ‖(g • z : ℍ).coe‖ = ‖UpperHalfPlane.num g z‖ / ‖UpperHalfPlane.denom g z‖ := by
  rw [UpperHalfPlane.coe_smul,UpperHalfPlane.σ]
  split_ifs <;> simp

theorem cosh_distance_I_from_norm (z : ℍ) :
    Real.cosh (dist UpperHalfPlane.I z) = (‖(z : ℂ)‖ ^ 2 + 1) / (2 * z.im) := by
  rw [dist_comm,UpperHalfPlane.cosh_dist']
  simp only [UpperHalfPlane.I_re,UpperHalfPlane.I_im,sub_zero,one_pow,mul_one,
    ← Complex.normSq_eq_norm_sq,Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  ring

/-- Actual norm of the numerator and denominator at i, in the real matrix coordinates. -/
theorem realGL_num_denom_I_norm_sq (g : GL (Fin 2) ℝ) :
    ‖UpperHalfPlane.num g UpperHalfPlane.I‖ ^ 2 = g 0 0 ^ 2 + g 0 1 ^ 2 ∧
      ‖UpperHalfPlane.denom g UpperHalfPlane.I‖ ^ 2 = g 1 0 ^ 2 + g 1 1 ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,UpperHalfPlane.num,UpperHalfPlane.denom,
    UpperHalfPlane.coe_I,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
    sub_zero,zero_add,add_zero]
  constructor <;> ring

/-- The full real matrix action, including its negative determinant branch, satisfies the displacement formula. -/
theorem realGL_cosh_displacement (g : GL (Fin 2) ℝ) :
    Real.cosh (dist UpperHalfPlane.I (g • UpperHalfPlane.I)) =
      (g 0 0 ^ 2 + g 0 1 ^ 2 + g 1 0 ^ 2 + g 1 1 ^ 2) / (2 * |g.val.det|) := by
  have hd : ‖UpperHalfPlane.denom g UpperHalfPlane.I‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (UpperHalfPlane.denom_ne_zero g UpperHalfPlane.I)
  have hdet : |g.val.det| ≠ 0 := abs_ne_zero.mpr g.det_ne_zero
  rw [cosh_distance_I_from_norm,realGL_coe_norm,div_pow,
    UpperHalfPlane.im_smul_eq_div_normSq,UpperHalfPlane.I_im,mul_one,
    Matrix.GeneralLinearGroup.val_det_apply,Complex.normSq_eq_norm_sq]
  obtain ⟨hN,hD⟩ := realGL_num_denom_I_norm_sq g
  have hD0 : g 1 0 ^ 2 + g 1 1 ^ 2 ≠ 0 := by rw [← hD]; exact pow_ne_zero 2 hd
  rw [hN,hD]
  field_simp
  ring

/-- Frobenius norm of the actual real representative embedded in complex matrices. -/
theorem realMobiusMatrix_norm_sq (g : GL (Fin 2) ℝ) :
    Auxiliary.Algebra.matrixNorm (complexifiedRealMobiusMatrix g).val ^ 2 =
      g 0 0 ^ 2 + g 0 1 ^ 2 + g 1 0 ^ 2 + g 1 1 ^ 2 := by
  rw [Auxiliary.Algebra.matrixNorm_sq]
  change ‖(g 0 0 : ℂ)‖ ^ 2 + ‖(g 0 1 : ℂ)‖ ^ 2 + ‖(g 1 0 : ℂ)‖ ^ 2 + ‖(g 1 1 : ℂ)‖ ^ 2 = _
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem complexifiedRealMobiusMatrix_det (g : GL (Fin 2) ℝ) :
    (complexifiedRealMobiusMatrix g).val.det = (g.val.det : ℂ) := by
  simp only [Matrix.det_fin_two]
  change (g 0 0 : ℂ) * (g 1 1 : ℂ) - (g 0 1 : ℂ) * (g 1 0 : ℂ) =
    ((g 0 0 * g 1 1 - g 0 1 * g 1 0 : ℝ) : ℂ)
  push_cast
  rfl

/-- The source's normalized matrix norm displacement identity holds for every real representative,
with no determinant normalization or orientation assumption left implicit. -/
theorem realMobiusMatrix_normalizedNorm_displacement (g : GL (Fin 2) ℝ) :
    Mobius.matrixNormalizedNorm (complexifiedRealMobiusMatrix g).val ^ 2 =
      2 * Real.cosh (dist UpperHalfPlane.I (g • UpperHalfPlane.I)) := by
  rw [Mobius.matrixNormalizedNorm,div_pow,Real.sq_sqrt (norm_nonneg _),
    realMobiusMatrix_norm_sq,complexifiedRealMobiusMatrix_det,Complex.norm_real,Real.norm_eq_abs,
    realGL_cosh_displacement]
  field_simp

/-- Both native coefficient branches have exactly the same actual image of the origin. -/
theorem disc_formula_origin_eq (f : 𝔻 → 𝔻) (a c : ℂ) (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1)
    (hf : (∀ z : 𝔻, (f z : ℂ) = (a * z + conj c) / (c * z + conj a)) ∨
      (∀ z : 𝔻, (f z : ℂ) = (a * conj (z : ℂ) + conj c) / (c * conj (z : ℂ) + conj a))) :
    f 0 = discCoefficientAction a c h 0 := by
  apply Complex.UnitDisc.coe_injective
  rw [discCoefficientAction_coe]
  rcases hf with hp | hm
  · exact hp 0
  · simpa only [Complex.UnitDisc.coe_zero,map_zero] using hm 0

/-- and, for either genuine disc coefficient branch. -/
theorem disc_formula_half_displacement (f : 𝔻 → 𝔻) (a c : ℂ)
    (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1)
    (hf : (∀ z : 𝔻, (f z : ℂ) = (a * z + conj c) / (c * z + conj a)) ∨
      (∀ z : 𝔻, (f z : ℂ) = (a * conj (z : ℂ) + conj c) / (c * conj (z : ℂ) + conj a))) :
    ‖c‖ = Real.sinh (discPathDist 0 (f 0) / 2) ∧
      ‖a‖ = Real.cosh (discPathDist 0 (f 0) / 2) := by
  rw [disc_formula_origin_eq f a c h hf]
  exact (discCoefficientAction_half_displacement a c h).symm

/-- The source disc matrix Frobenius displacement identity applies to both coefficient branches. -/
theorem disc_formula_matrixNorm_displacement (f : 𝔻 → 𝔻) (a c : ℂ)
    (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1)
    (hf : (∀ z : 𝔻, (f z : ℂ) = (a * z + conj c) / (c * z + conj a)) ∨
      (∀ z : 𝔻, (f z : ℂ) = (a * conj (z : ℂ) + conj c) / (c * conj (z : ℂ) + conj a))) :
    Auxiliary.Algebra.matrixNorm (discIsometryMatrix a c) ^ 2 = 2 * Real.cosh (discPathDist 0 (f 0)) := by
  rw [disc_formula_origin_eq f a c h hf]
  exact discIsometryMatrix_norm_displacement a c h

/-- Since the genuine source disc representative has determinant one, the existing projective
normalized norm agrees with its Frobenius norm. -/
theorem discIsometryMatrix_normalizedNorm (a c : ℂ) (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1) :
    Mobius.matrixNormalizedNorm (discIsometryMatrix a c) = Auxiliary.Algebra.matrixNorm (discIsometryMatrix a c) := by
  rw [Mobius.matrixNormalizedNorm,discIsometryMatrix_det a c h]
  simp

theorem disc_formula_normalizedNorm_displacement (f : 𝔻 → 𝔻) (a c : ℂ)
    (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1)
    (hf : (∀ z : 𝔻, (f z : ℂ) = (a * z + conj c) / (c * z + conj a)) ∨
      (∀ z : 𝔻, (f z : ℂ) = (a * conj (z : ℂ) + conj c) / (c * conj (z : ℂ) + conj a))) :
    Mobius.matrixNormalizedNorm (discIsometryMatrix a c) ^ 2 =
      2 * Real.cosh (discPathDist 0 (f 0)) := by
  rw [discIsometryMatrix_normalizedNorm a c h]
  exact disc_formula_matrixNorm_displacement f a c h hf

end
end LowDimensionalTopology.Geometry.Hyperbolic
