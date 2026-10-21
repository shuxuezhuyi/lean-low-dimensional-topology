/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ConformalTypes
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementFunctions
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius

/-- Uniqueness and real coefficients force a parabolic fixed point onto the actual ideal boundary. -/
theorem realSLMobius_parabolic_fixed_boundary (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) (p : Mobius.ExtendedComplex)
    (hp : (realSLMobius A).val p = p) : p ∈ halfPlaneIdealBoundary := by
  induction p using OnePoint.rec with
  | infty => simp [halfPlaneIdealBoundary]
  | coe z =>
    have hpoly := (Mobius.Classification.fractionalLinear_fixed_coe_iff
      (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map Complex.ofRealHom A)) z).mp
      (show Mobius.fractionalLinear _ (z : Mobius.ExtendedComplex) = z by
        simpa only [realSLMobius, MonoidHom.comp_apply, Mobius.invariantDisc_specialLinear_action] using hp)
    change (A 1 0 : ℂ) * (z*z) + ((A 1 1 : ℂ) - A 0 0) * z + -(A 0 1 : ℂ) = 0 at hpoly
    have hconj := congrArg conj hpoly
    simp only [map_add, map_mul, map_sub, map_neg, map_zero, Complex.conj_ofReal] at hconj
    have hfix : (realSLMobius A).val ((conj z : ℂ) : Mobius.ExtendedComplex) = (conj z : ℂ) := by
      have hfp := (Mobius.Classification.fractionalLinear_fixed_coe_iff
        (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map Complex.ofRealHom A)) (conj z)).mpr hconj
      simpa only [realSLMobius, MonoidHom.comp_apply, Mobius.invariantDisc_specialLinear_action] using hfp
    obtain ⟨w, hw⟩ := hA.2
    have he : ((conj z : ℂ) : Mobius.ExtendedComplex) = (z : ℂ) := (hw _).mp hfix |>.trans ((hw _).mp hp).symm
    have hce : conj z = z := (OnePoint.coe_eq_coe.mp he)
    have hi := congrArg Complex.im hce
    simp only [Complex.conj_im] at hi
    exact (coe_mem_halfPlaneIdealBoundary z).mpr (by linarith)

/-- Every genuine parabolic real matrix can move its unique ideal point to infinity by a real SL map. -/
theorem realSLMobius_parabolic_normalizer_infty (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) :
    ∃ q : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (realSLMobius (q*A*q⁻¹)).val ∞ = ∞ := by
  obtain ⟨p, hp⟩ := hA.2
  have hfp := (hp p).mpr rfl
  obtain ⟨q, hq⟩ := realSLMobius_exists_send_to_infty p (realSLMobius_parabolic_fixed_boundary A hA p hfp)
  refine ⟨q, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hq]
  exact DiscreteGroups.mobius_conjugate_fixedpoint _ _ p hfp

/-- Fixing infinity in the actual projective action is exactly the genuine triangular coefficient condition. -/
theorem realSLMobius_fixed_infty_iff (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (realSLMobius A).val ∞ = ∞ ↔ A 1 0 = 0 := by
  rw [realSLMobius, MonoidHom.comp_apply, Mobius.invariantDisc_specialLinear_action, Mobius.fractionalLinear_infty]
  change (if (A 1 0 : ℂ) = 0 then ∞ else ((A 0 0 / A 1 0 : ℂ) : Mobius.ExtendedComplex)) = ∞ ↔ _
  simp


/-- Opposite real special-linear lifts define exactly the same actual Mobius transformation. -/
theorem realSLMobius_neg (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    realSLMobius (-A) = realSLMobius A := by
  unfold realSLMobius
  simp only [MonoidHom.comp_apply]
  apply (Mobius.specialLinear_sameMobius_iff _ _).mpr
  right
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp [Mobius.specialLinearSignChange, Matrix.SpecialLinearGroup.coe_neg]

/-- A genuine parabolic triangular lift is precisely a nonzero real translation, up to its sign choice. -/
theorem hSL_parabolic_triangular_normal_form (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ)) ^ 2 = 4)
    (hc : A 1 0 = 0) (hn : realSLMobius A ≠ 1) :
    ∃ t : ℝ, t ≠ 0 ∧ (A = hTranslationSL t ∨ A = -hTranslationSL t) := by
  have had : A 0 0 * A 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using A.det_coe
  rw [Matrix.trace_fin_two] at ht
  have heq : A 0 0 = A 1 1 := by nlinarith [sq_nonneg (A 0 0 - A 1 1)]
  have ha : A 0 0 ^ 2 = (1 : ℝ) ^ 2 := by nlinarith [had]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ha with ha | ha
  · have hd : A 1 1 = 1 := by linarith
    have he : A = hTranslationSL (A 0 1) := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [hTranslationSL, ha, hd, hc]
    refine ⟨A 0 1, ?_, Or.inl he⟩
    intro hb
    have hA : A = 1 := by
      rw [he, hb]
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [hTranslationSL]
    exact hn (by rw [hA, map_one])
  · have hd : A 1 1 = -1 := by linarith
    have he : A = -hTranslationSL (-(A 0 1)) := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [hTranslationSL, Matrix.SpecialLinearGroup.coe_neg, ha, hd, hc]
    refine ⟨-(A 0 1), ?_, Or.inr he⟩
    intro hb
    have hA : A = -1 := by
      rw [he, hb]
      congr 1
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [hTranslationSL]
    exact hn (by rw [hA, realSLMobius_neg, map_one])

/-- Every actual parabolic real isometry has a genuine real SL normalizer and a nonzero translation parameter. -/
theorem realSLMobius_parabolic_normal_form (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) :
    ∃ q : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ t : ℝ, t ≠ 0 ∧
      (q*A*q⁻¹ = hTranslationSL t ∨ q*A*q⁻¹ = -hTranslationSL t) := by
  obtain ⟨q, hq⟩ := realSLMobius_parabolic_normalizer_infty A hA
  let G := q*A*q⁻¹
  have hproj : realSLMobius G = realSLMobius q * realSLMobius A * (realSLMobius q)⁻¹ := by
    simp only [G, map_mul, map_inv]
  have hp : Mobius.MobiusParabolic (realSLMobius G) := by
    rw [hproj]
    exact (Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨realSLMobius q, rfl⟩)).mp hA
  have ht := (realSLMobius_parabolic_iff G hp.1).mp hp
  have hc := (realSLMobius_fixed_infty_iff G).mp hq
  obtain ⟨t, ht0, he⟩ := hSL_parabolic_triangular_normal_form G ht hc hp.1
  exact ⟨q, t, ht0, he⟩

/-- The genuine upper-half-plane fixed center provided by Mathlib's elliptic quadratic. -/
def hEllipticCenter (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : (Matrix.trace A.val) ^ 2 < 4) : ℍ :=
  UpperHalfPlane.fixedPt (Matrix.SpecialLinearGroup.mapGL ℝ A) (by
    change Matrix.IsElliptic A.val
    simp only [Matrix.IsElliptic, Matrix.discr_fin_two, A.det_coe]
    linarith)

/-- The center is the unique native fixed point, rather than an abstract chosen parameter. -/
theorem hSL_elliptic_fixed_iff (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : (Matrix.trace A.val) ^ 2 < 4) (z : ℍ) :
    A • z = z ↔ z = hEllipticCenter A ht := by
  exact UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt (by
    change 0 < A.val.det
    rw [A.det_coe]
    norm_num) _

/-- A real determinant-one rotation about the literal upper-half-plane point I. -/
def hRotationSL (a b : ℝ) (hu : a^2+b^2=1) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![a,b; -b,a], by simpa [Matrix.det_fin_two, pow_two] using hu⟩

/-- Matrices fixing I are exactly genuine rotations, with their unit-circle parameters. -/
theorem hSL_fix_I_rotation (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hI : A • UpperHalfPlane.I = UpperHalfPlane.I) :
    ∃ (a b : ℝ) (hu : a^2+b^2=1), A = hRotationSL a b hu := by
  have he := (UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos
    (g := Matrix.SpecialLinearGroup.mapGL ℝ A) (by
      change 0 < A.val.det
      rw [A.det_coe]
      norm_num)).mp hI
  change A 0 0 = A 1 1 ∧ A 0 1 = -A 1 0 at he
  have hu : A 0 0 ^ 2 + A 0 1 ^ 2 = 1 := by
    have hd := A.det_coe
    rw [Matrix.det_fin_two] at hd
    rw [← he.1, he.2] at hd
    rw [he.2]
    nlinarith [hd]
  refine ⟨A 0 0, A 0 1, hu, ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hRotationSL, he.1, he.2]

/-- Every genuine real elliptic isometry has an actual SL rotation normalizer. -/
theorem realSLMobius_elliptic_normal_form (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) :
    ∃ (q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (a b : ℝ) (hu : a^2+b^2=1),
      q • hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA) = UpperHalfPlane.I ∧
      b ≠ 0 ∧ q*A*q⁻¹ = hRotationSL a b hu := by
  let ht := (realSLMobius_elliptic_iff A hA.1).mp hA
  let v := hEllipticCenter A ht
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) ℝ) v UpperHalfPlane.I
  have hv : A • v = v := (hSL_elliptic_fixed_iff A ht v).mpr rfl
  have hI : (q*A*q⁻¹) • UpperHalfPlane.I = UpperHalfPlane.I := by
    rw [← hq, mul_smul, mul_smul, inv_smul_smul, hv]
  obtain ⟨a,b,hu,he⟩ := hSL_fix_I_rotation (q*A*q⁻¹) hI
  refine ⟨q,a,b,hu,hq,?_,he⟩
  intro hb
  have ha : a^2 = (1:ℝ)^2 := by simpa [hb] using hu
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ha with ha | ha
  · have hrot : hRotationSL a b hu = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [hRotationSL, ha, hb]
    have hproj := congrArg realSLMobius (he.trans hrot)
    simp only [map_mul, map_inv, map_one] at hproj
    apply hA.1
    calc
      realSLMobius A = (realSLMobius q)⁻¹ * (realSLMobius q * realSLMobius A * (realSLMobius q)⁻¹) * realSLMobius q := by group
      _ = 1 := by rw [hproj]; simp
  · have hrot : hRotationSL a b hu = -1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [hRotationSL, Matrix.SpecialLinearGroup.coe_neg, ha, hb]
    have hproj := congrArg realSLMobius (he.trans hrot)
    simp only [map_mul, map_inv, realSLMobius_neg, map_one] at hproj
    apply hA.1
    calc
      realSLMobius A = (realSLMobius q)⁻¹ * (realSLMobius q * realSLMobius A * (realSLMobius q)⁻¹) * realSLMobius q := by group
      _ = 1 := by rw [hproj]; simp

end LowDimensionalTopology.Geometry.Hyperbolic
