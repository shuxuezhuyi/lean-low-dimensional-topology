/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalRegions
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicAxes
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ParabolicEllipticNormalForms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- With the genuine invariant geodesic and metric translation infimum. -/
theorem hyperbolic_half_displacement (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) (z : ℍ) :
    Real.sinh (dist z (f • z) / 2) =
      Real.cosh ((hHyperbolicAxis f hf ht).pointDist z) *
        Real.sinh (hTranslationLength (hSLIsometry f) / 2) := by
  obtain ⟨s,k,hk,_hk1,hL,hT,hact⟩ := hHyperbolicAxis_normalizer f hf ht
  have himage : (fun w : ℍ => s • w) '' (hHyperbolicAxis f hf ht).carrier =
      (HalfPlaneLine.vertical 0).carrier := by
    ext w
    constructor
    · rintro ⟨v,hv,rfl⟩
      change (s • v).re = 0
      rw [hL] at hv
      exact hv
    · intro hw
      change w.re = 0 at hw
      refine ⟨s⁻¹ • w, ?_, by simp⟩
      rw [hL]
      simpa using hw
  have hpd := (hHyperbolicAxis f hf ht).pointDist_isometry_image
    (HalfPlaneLine.vertical 0) (fun w : ℍ => s • w) (isometry_smul ℍ s) himage z
  have hd : dist z (f • z) = dist (s • z) (verticalDilationSL k hk • (s • z)) := by
    calc
      dist z (f • z) = dist (s • z) (s • (f • z)) := ((isometry_smul ℍ s).dist_eq z (f • z)).symm
      _ = dist (s • z) (verticalDilationSL k hk • (s • z)) := by
        rw [← hact]
        simp only [mul_smul, inv_smul_smul]
  rw [hd,dilation_half_displacement,hpd,hT]

/-- The repeated real root is extracted from the actual determinant and parabolic trace. -/
theorem hSL_parabolic_polynomial (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : (Matrix.trace A.val)^2 = 4) (hc : A 1 0 ≠ 0) (z : ℂ) :
    (A 1 0 : ℂ)*z^2 + ((A 1 1 : ℂ)-A 0 0)*z-A 0 1 =
      (A 1 0 : ℂ) * (z - (((A 0 0-A 1 1)/(2*A 1 0):ℝ):ℂ))^2 := by
  have hd := A.det_coe
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.trace_fin_two] at ht
  have he : (A 0 0-A 1 1)^2 + 4*A 1 0*A 0 1 = 0 := by nlinarith [hd]
  have hec : (((A 0 0-A 1 1)^2 + 4*A 1 0*A 0 1 : ℝ) : ℂ) = 0 := by exact_mod_cast he
  push_cast at hec ⊢
  field_simp [Complex.ofReal_ne_zero.mpr hc]
  linear_combination -hec

/-- at the actual finite parabolic boundary point. -/
theorem parabolic_finite_poisson_displacement (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : (Matrix.trace A.val)^2 = 4) (hc : A 1 0 ≠ 0) (z : ℍ) :
    Auxiliary.Analysis.halfPlanePoissonKernel z (some ((A 0 0-A 1 1)/(2*A 1 0))) *
      Real.sinh (dist z (A • z)/2) = |A 1 0|/2 := by
  let p : ℝ := (A 0 0-A 1 1)/(2*A 1 0)
  have hne : (z : ℂ) - (p : ℂ) ≠ 0 := by
    intro he
    have hi := congrArg Complex.im (sub_eq_zero.mp he)
    exact z.im_ne_zero (by simpa using hi)
  rw [hSL_half_displacement_polynomial, hSL_parabolic_polynomial A ht hc,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Auxiliary.Analysis.halfPlanePoissonKernel_finite]
  change z.im/‖(z : ℂ)-(p : ℂ)‖^2 * (|A 1 0| *‖(z : ℂ)-(p : ℂ)‖^2/(2*z.im)) = _
  field_simp [z.im_ne_zero, norm_ne_zero_iff.mpr hne]

/-- At infinity the parabolic Poisson product is the triangular translation coefficient. -/
theorem parabolic_infty_poisson_displacement (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : (Matrix.trace A.val)^2 = 4) (hc : A 1 0 = 0) (z : ℍ) :
    Auxiliary.Analysis.halfPlanePoissonKernel z none * Real.sinh (dist z (A • z)/2) = |A 0 1|/2 := by
  have hd := A.det_coe
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hd
  rw [Matrix.trace_fin_two] at ht
  have he : A 1 1-A 0 0 = 0 := by nlinarith [sq_nonneg (A 1 1-A 0 0)]
  rw [Auxiliary.Analysis.halfPlanePoissonKernel_infinity, hSL_half_displacement_polynomial]
  rw [show ((A 1 1 : ℂ)-A 0 0) = 0 by exact_mod_cast he, hc]
  simp only [Complex.ofReal_zero, zero_mul, zero_add, zero_sub, norm_neg,
    Complex.norm_real, Real.norm_eq_abs, UpperHalfPlane.coe_im]
  field_simp [z.im_ne_zero]

/-- The ideal boundary parameter used by the literal Poisson kernel. -/
def hPoissonBoundaryPoint : Option ℝ → Mobius.ExtendedComplex
  | none => ∞
  | some p => ((p : ℂ) : Mobius.ExtendedComplex)

/-- The parabolic Poisson product is globally constant at its unique genuine ideal fixed point. -/
theorem parabolic_poisson_displacement (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) :
    ∃ p : Option ℝ, ∃ C : ℝ, 0 < C ∧
      (∀ w : Mobius.ExtendedComplex, (realSLMobius A).val w = w ↔ w = hPoissonBoundaryPoint p) ∧
      ∀ z : ℍ, Auxiliary.Analysis.halfPlanePoissonKernel z p * Real.sinh (dist z (A • z)/2) = C := by
  have ht := (realSLMobius_parabolic_iff A hA.1).mp hA
  obtain ⟨v,hv⟩ := hA.2
  have hfixed (w : ℂ) : (realSLMobius A).val (w : Mobius.ExtendedComplex) = w ↔
      (A 1 0 : ℂ)*(w*w)+((A 1 1 : ℂ)-A 0 0)*w+ -(A 0 1 : ℂ) = 0 := by
    change Mobius.fractionalLinear (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map Complex.ofRealHom
      A)) (w : Mobius.ExtendedComplex) = w ↔ _
    exact Mobius.Classification.fractionalLinear_fixed_coe_iff _ w
  by_cases hc : A 1 0 = 0
  · have hi : (realSLMobius A).val ∞ = ∞ := by
      rw [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,Mobius.fractionalLinear_infty]
      change (if (A 1 0 : ℂ) = 0 then ∞ else _) = ∞
      simp [hc]
    have hb : A 0 1 ≠ 0 := by
      intro hb
      have h0 := (hfixed 0).mpr (by simp [hb])
      have he : ((0 : ℂ) : Mobius.ExtendedComplex) = ∞ := ((hv _).mp h0).trans ((hv _).mp hi).symm
      exact (OnePoint.coe_ne_infty (0 : ℂ)) he
    refine ⟨none, |A 0 1|/2, by positivity, ?_, parabolic_infty_poisson_displacement A ht hc⟩
    intro w
    rw [hv w]
    exact ⟨fun he => he.trans ((hv _).mp hi).symm, fun he => he.trans ((hv _).mp hi)⟩
  · let p : ℝ := (A 0 0-A 1 1)/(2*A 1 0)
    have hp : (realSLMobius A).val ((p : ℂ) : Mobius.ExtendedComplex) = (p : ℂ) := by
      apply (hfixed p).mpr
      have he := hSL_parabolic_polynomial A ht hc (p : ℂ)
      simpa only [p, sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, pow_two,
        sub_eq_add_neg] using he
    refine ⟨some p, |A 1 0|/2, by positivity, ?_, parabolic_finite_poisson_displacement A ht hc⟩
    intro w
    rw [hv w]
    exact ⟨fun he => he.trans ((hv _).mp hp).symm, fun he => he.trans ((hv _).mp hp)⟩

/-- The actual disc rotation multiplier of a native real rotation lift. -/
def hRotationMultiplier (a b : ℝ) : ℂ := (⟨a,b⟩ : ℂ) / conj (⟨a,b⟩ : ℂ)

theorem hRotationParameter_norm (a b : ℝ) (hu : a^2+b^2=1) : ‖(⟨a,b⟩ : ℂ)‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_mk]
  have he : a*a+b*b = 1 := by nlinarith [hu]
  rw [he,Real.sqrt_one]

theorem hRotationMultiplier_norm (a b : ℝ) (hu : a^2+b^2=1) :
    ‖hRotationMultiplier a b‖ = 1 := by
  rw [hRotationMultiplier,norm_div,Complex.norm_conj,hRotationParameter_norm a b hu]
  norm_num

/-- The native Cayley-conjugated matrix action is exactly the actual unit-disc rotation. -/
theorem hRotationSL_disc_action (a b : ℝ) (hu : a^2+b^2=1) (z : 𝔻) :
    discSL2Action (hRotationSL a b hu) z =
      discUnitRotation (hRotationMultiplier a b) (hRotationMultiplier_norm a b hu) z := by
  have hda : discCoefficientA (hRotationSL a b hu) = (⟨a,b⟩ : ℂ) := by
    apply Complex.ext <;> simp [discCoefficientA,hRotationSL]
  have hdc : discCoefficientC (hRotationSL a b hu) = 0 := by
    apply Complex.ext <;> simp [discCoefficientC,hRotationSL]
  apply Complex.UnitDisc.coe_injective
  rw [discSL2Action_coe,hda,hdc,discUnitRotation_coe]
  simp only [map_zero,add_zero,zero_mul,zero_add]
  dsimp [hRotationMultiplier]
  ring

/-- The true rotation parameter gives the exact sine-half-angle coefficient. -/
theorem hRotationMultiplier_half_norm (a b : ℝ) (hu : a^2+b^2=1) :
    ‖1-hRotationMultiplier a b‖/2 = |b| := by
  have hn := hRotationParameter_norm a b hu
  have hne : conj (⟨a,b⟩ : ℂ) ≠ 0 := by
    intro he
    have hz := congrArg norm he
    rw [Complex.norm_conj,hn,norm_zero] at hz
    norm_num at hz
  have he : 1-hRotationMultiplier a b =
      (conj (⟨a,b⟩ : ℂ)-(⟨a,b⟩ : ℂ))/conj (⟨a,b⟩ : ℂ) := by
    dsimp [hRotationMultiplier]
    field_simp
  have hi : conj (⟨a,b⟩ : ℂ)-(⟨a,b⟩ : ℂ) = (((-2*b):ℝ):ℂ)*Complex.I := by
    apply Complex.ext <;> simp; ring
  rw [he,norm_div,Complex.norm_conj,hn,div_one,hi,norm_mul,Complex.norm_I,
    mul_one,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  norm_num

/-- The rotation formula uses the genuine upper-half-plane center I and the native metric. -/
theorem rotation_half_displacement (a b : ℝ) (hu : a^2+b^2=1) (z : ℍ) :
    Real.sinh (dist z (hRotationSL a b hu • z)/2) =
      Real.sinh (dist z UpperHalfPlane.I) * |b| := by
  have hd := disc_rotation_half_displacement (hRotationMultiplier a b)
    (hRotationMultiplier_norm a b hu) (halfPlaneToDisc z)
  rw [← hRotationSL_disc_action a b hu] at hd
  simp only [discSL2Action,discPathDist_eq_halfPlane,discToHalfPlane_halfPlaneToDisc] at hd
  have h0 : discToHalfPlane 0 = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    simp [discToHalfPlane,inverseCayleyFormula]
  rw [h0,dist_comm UpperHalfPlane.I z] at hd
  rw [mul_div_assoc,hRotationMultiplier_half_norm a b hu] at hd
  exact hd

/-- For every elliptic map, with its genuine native fixed center. -/
theorem elliptic_half_displacement (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) :
    ∃ (a b : ℝ) (hu : a^2+b^2=1), b ≠ 0 ∧
      (∀ z : ℍ, Real.sinh (dist z (A • z)/2) =
        Real.sinh (dist z (hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA))) * |b|) ∧
      ∃ q : Matrix.SpecialLinearGroup (Fin 2) ℝ, q*A*q⁻¹ = hRotationSL a b hu := by
  obtain ⟨q,a,b,hu,hq,hb,he⟩ := realSLMobius_elliptic_normal_form A hA
  refine ⟨a,b,hu,hb,?_,q,he⟩
  intro z
  have hd : dist z (A • z) = dist (q • z) (hRotationSL a b hu • (q • z)) := by
    calc
      dist z (A • z) = dist (q • z) (q • (A • z)) := ((isometry_smul ℍ q).dist_eq z (A • z)).symm
      _ = dist (q • z) (hRotationSL a b hu • (q • z)) := by
        rw [← he]
        simp only [mul_smul,inv_smul_smul]
  have hv : dist z (hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)) =
      dist (q • z) UpperHalfPlane.I := by
    rw [← hq]
    exact ((isometry_smul ℍ q).dist_eq _ _).symm
  rw [hd,rotation_half_displacement,hv]

/-- The signed principal angle of the actual native rotation multiplier. -/
def hRotationAngle (a b : ℝ) : ℝ := Complex.arg (hRotationMultiplier a b)

theorem hRotationAngle_mem (a b : ℝ) : hRotationAngle a b ∈ Icc (-Real.pi) Real.pi :=
  ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩

theorem hRotationMultiplier_eq_exp (a b : ℝ) (hu : a^2+b^2=1) :
    hRotationMultiplier a b = Complex.exp (Complex.I * hRotationAngle a b) := by
  have he := Complex.norm_mul_exp_arg_mul_I (hRotationMultiplier a b)
  rw [hRotationMultiplier_norm a b hu,Complex.ofReal_one,one_mul] at he
  simpa only [hRotationAngle,mul_comm] using he.symm

theorem hRotationAngle_half_sine (a b : ℝ) (hu : a^2+b^2=1) :
    |Real.sin (hRotationAngle a b/2)| = |b| := by
  have he := hRotationMultiplier_half_norm a b hu
  rw [hRotationMultiplier_eq_exp a b hu,norm_sub_rev,
    Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,abs_mul] at he
  norm_num at he
  nlinarith [he]

/-- The angular and trace conventions agree for the actual normalized rotation. -/
theorem hRotationAngle_trace (a b : ℝ) (hu : a^2+b^2=1) :
    (Matrix.trace (hRotationSL a b hu).val)^2 = 4*(Real.cos (hRotationAngle a b/2))^2 := by
  have he := hRotationAngle_half_sine a b hu
  have hs := congrArg (fun x : ℝ => x^2) he
  simp only [sq_abs] at hs
  simp only [hRotationSL,Matrix.trace_fin_two,Matrix.of_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one]
  nlinarith [Real.sin_sq_add_cos_sq (hRotationAngle a b/2)]

/-- All three geometric quantities in the elliptic formula use one actual conjugacy and angle. -/
theorem elliptic_angular_displacement (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) :
    ∃ θ : ℝ, θ ∈ Icc (-Real.pi) Real.pi ∧
      (∀ z : ℍ, Real.sinh (dist z (A • z)/2) =
        Real.sinh (dist z (hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA))) * |Real.sin (θ/2)|) ∧
      (Matrix.trace A.val)^2 = 4*(Real.cos (θ/2))^2 ∧
      ∃ q : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        ∀ z : 𝔻, discSL2Action (q*A*q⁻¹) z =
          discUnitRotation (Complex.exp (Complex.I*θ)) (by simp [Complex.norm_exp]) z := by
  obtain ⟨a,b,hu,_hb,hdisp,q,hq⟩ := elliptic_half_displacement A hA
  refine ⟨hRotationAngle a b,hRotationAngle_mem a b,?_,?_,q,?_⟩
  · intro z
    rw [hdisp,hRotationAngle_half_sine a b hu]
  · have htr := hSL_trace_conjugation A q
    rw [hq] at htr
    rw [← htr]
    exact hRotationAngle_trace a b hu
  · intro z
    rw [hq,hRotationSL_disc_action]
    apply Complex.UnitDisc.coe_injective
    simp only [discUnitRotation_coe,hRotationMultiplier_eq_exp a b hu]

end LowDimensionalTopology.Geometry.Hyperbolic
