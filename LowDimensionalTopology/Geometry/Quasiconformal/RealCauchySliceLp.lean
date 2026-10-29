module

public import LowDimensionalTopology.Geometry.Quasiconformal.RealCauchyAuxiliary
public import LowDimensionalTopology.Geometry.Quasiconformal.RealPoissonLp
public import LowDimensionalTopology.Geometry.Quasiconformal.RieszBookConstant
public import LowDimensionalTopology.Geometry.Quasiconformal.RieszComplexMinkowski
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Finite horizontal Cauchy-slice norm estimates

The full Cauchy slice belongs to the original Lp before any real norm is
used. Its actual W integral, the supplied p/2 Minkowski step and the native
Poisson contraction then give the real-slice coefficient D(p)^(-1/2).
No Riesz estimate or slice inequality is assumed. The boundary/Fatou step
is separate and is not asserted here.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The FULL original complex Cauchy slice belongs to Lp. Imaginary-part
Poisson regularity alone is not used as a substitute for this assertion. -/
theorem realCauchyFunction_slice_memLp {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {p : ℝ} (hp : 2 ≤ p)
    {η : ℝ} (hη : 0 < η) :
    MemLp (fun ξ : ℝ => realCauchyFunction φ ((ξ : ℂ) + (η : ℂ) * I))
      (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hp2 : 0 ≤ p - 2 := by linarith
  let F : ℝ → ℂ := fun ξ => realCauchyFunction φ ((ξ : ℂ) + (η : ℂ) * I)
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro ξ
    have hline : Continuous (fun t : ℝ => (t : ℂ) + (η : ℂ) * I) := by fun_prop
    have hsite : ContinuousAt (realCauchyFunction φ) ((ξ : ℂ) + (η : ℂ) * I) :=
      (hasDerivAt_realCauchyFunction hφ hc
        (z := (ξ : ℂ) + (η : ℂ) * I) (by simpa using hη)).continuousAt
    change ContinuousAt ((realCauchyFunction φ) ∘
      (fun t : ℝ => (t : ℂ) + (η : ℂ) * I)) ξ
    exact ContinuousAt.comp (f := fun t : ℝ => (t : ℂ) + (η : ℂ) * I)
      (x := ξ) hsite hline.continuousAt
  obtain ⟨M, hM, hb⟩ := exists_realCauchy_decay_profile hφ hc (δ := η) hη
  let C : ℝ := M ^ (p - 2) * M ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hprofile : Integrable (fun ξ : ℝ => C / (1 + ‖ξ‖) ^ 2) volume := by
    have h := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2)
      (by norm_num)).const_mul C
    exact h.congr (Eventually.of_forall fun ξ => by
      simp only [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖ξ‖), Real.rpow_two,
        div_eq_mul_inv])
  have hbound (ξ : ℝ) : ‖F ξ‖ ^ p ≤ C / (1 + ‖ξ‖) ^ 2 := by
    have hx : ‖ξ‖ ≤ ‖(ξ : ℂ) + (η : ℂ) * I‖ := by
      simpa [Real.norm_eq_abs] using! Complex.abs_re_le_norm ((ξ : ℂ) + (η : ℂ) * I)
    have hfirst : ‖F ξ‖ ≤ M / (1 + ‖ξ‖) := by
      have hfirst0 : ‖F ξ‖ ≤ M / (1 + ‖(ξ : ℂ) + (η : ℂ) * I‖) :=
        (hb ((ξ : ℂ) + (η : ℂ) * I) (by simp)).1
      exact hfirst0.trans (by gcongr)
    have hFM : ‖F ξ‖ ≤ M := hfirst.trans (by
      apply (div_le_iff₀ (by positivity : 0 < 1 + ‖ξ‖)).2
      nlinarith [norm_nonneg ξ])
    calc
      _ = ‖F ξ‖ ^ (p - 2) * ‖F ξ‖ ^ 2 := by
        rw [← Real.rpow_two, ← Real.rpow_add_of_nonneg (norm_nonneg _) hp2 (by norm_num)]
        congr 1
        ring
      _ ≤ M ^ (p - 2) * (M / (1 + ‖ξ‖)) ^ 2 :=
        mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) hFM hp2)
          (pow_le_pow_left₀ (norm_nonneg _) hfirst 2)
          (sq_nonneg _) (Real.rpow_nonneg hM _)
      _ = C / (1 + ‖ξ‖) ^ 2 := by
        dsimp only [C]
        rw [div_pow]
        ring
  have hpower : Integrable (fun ξ : ℝ => ‖F ξ‖ ^ p) volume := by
    apply hprofile.mono'
      (hFcont.norm.rpow_const (fun _ => Or.inr hp0.le)).aestronglyMeasurable
    exact Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact hbound ξ
  have hE0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  apply (integrable_norm_rpow_iff hFcont.aestronglyMeasurable hE0 ENNReal.ofReal_ne_top).1
  simpa only [ENNReal.toReal_ofReal hp0.le] using hpower

private theorem finite_eLpNorm_rpow_eq_integral {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {p : ℝ} (hp : 0 < p) (hf : MemLp f (ENNReal.ofReal p) volume) :
    (eLpNorm f (ENNReal.ofReal p) volume).toReal ^ p = ∫ x : ℝ, ‖f x‖ ^ p := by
  have hE0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  rw [toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal
    hE0 ENNReal.ofReal_ne_top hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp.le]
  rw [← Real.rpow_mul (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _),
    inv_mul_cancel₀ hp.ne', Real.rpow_one]

/-- The book's stronger real-input coefficient, before its printed constant
is used in complexification. All full and component slice norms are finite
before the toReal calculation. -/
theorem realCauchyFunction_re_slice_norm_le {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {p : ℝ} (hp : 2 ≤ p)
    {η : ℝ} (hη : 0 < η) :
    (eLpNorm (fun ξ : ℝ => (realCauchyFunction φ ((ξ : ℂ) + (η : ℂ) * I)).re)
      (ENNReal.ofReal p) volume).toReal ≤
      (rieszBookDenominator p) ^ (-(1 / 2 : ℝ)) *
        (eLpNorm φ (ENNReal.ofReal p) volume).toReal := by
  have hp0 : 0 < p := by linarith
  have hpE0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  let F : ℝ → ℂ := fun ξ => realCauchyFunction φ ((ξ : ℂ) + (η : ℂ) * I)
  let U : ℝ → ℝ := fun ξ => (F ξ).re
  let V : ℝ → ℝ := fun ξ => (F ξ).im
  let c : ℝ := p / (p - 1)
  let B : ℝ := (rieszBookDenominator p) ^ (-(1 / 2 : ℝ))
  let NF : ℝ := (eLpNorm F (ENNReal.ofReal p) volume).toReal
  let NU : ℝ := (eLpNorm U (ENNReal.ofReal p) volume).toReal
  let NV : ℝ := (eLpNorm V (ENNReal.ofReal p) volume).toReal
  let Nφ : ℝ := (eLpNorm φ (ENNReal.ofReal p) volume).toReal
  have hc0 : 0 ≤ c := div_nonneg hp0.le (by linarith)
  have hF : MemLp F (ENNReal.ofReal p) volume := realCauchyFunction_slice_memLp hφ hc hp hη
  have hU : MemLp U (ENNReal.ofReal p) volume := by simpa only [U] using! hF.re
  have hV : MemLp V (ENNReal.ofReal p) volume := by simpa only [V] using! hF.im
  have hφp : MemLp φ (ENNReal.ofReal p) volume := hφ.memLp_of_hasCompactSupport hc
  have hIF : Integrable (fun ξ : ℝ => ‖F ξ‖ ^ p) volume := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using hF.integrable_norm_rpow hpE0 ENNReal.ofReal_ne_top
  have hIU : Integrable (fun ξ : ℝ => ‖U ξ‖ ^ p) volume := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using hU.integrable_norm_rpow hpE0 ENNReal.ofReal_ne_top
  have hgreen := integral_realCauchyAuxiliary_nonneg hφ hc hp hη
  have hfun : (fun ξ : ℝ => realCauchyAuxiliary φ p ((ξ : ℂ) + (η : ℂ) * I)) =
      (fun ξ : ℝ => ‖F ξ‖ ^ p - c * ‖U ξ‖ ^ p) := rfl
  rw [hfun] at hgreen
  have hsplit : (∫ ξ : ℝ, ‖F ξ‖ ^ p - c * ‖U ξ‖ ^ p) =
      (∫ ξ : ℝ, ‖F ξ‖ ^ p) - c * ∫ ξ : ℝ, ‖U ξ‖ ^ p := by
    simpa only [integral_const_mul] using! integral_sub hIF (hIU.const_mul c)
  rw [hsplit] at hgreen
  have hintegral : c * NU ^ p ≤ NF ^ p := by
    change c * (eLpNorm U (ENNReal.ofReal p) volume).toReal ^ p ≤
      (eLpNorm F (ENNReal.ofReal p) volume).toReal ^ p
    rw [finite_eLpNorm_rpow_eq_integral hp0 hU, finite_eLpNorm_rpow_eq_integral hp0 hF]
    exact sub_nonneg.1 hgreen
  have hNF : 0 ≤ NF := ENNReal.toReal_nonneg
  have hNU : 0 ≤ NU := ENNReal.toReal_nonneg
  have hNV : 0 ≤ NV := ENNReal.toReal_nonneg
  have hpower : c ^ (2 / p) * NU ^ 2 ≤ NF ^ 2 := by
    have h := Real.rpow_le_rpow (mul_nonneg hc0 (Real.rpow_nonneg hNU _)) hintegral
      (div_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hp0.le)
    rw [Real.mul_rpow hc0 (Real.rpow_nonneg hNU _), ← Real.rpow_mul hNU,
      ← Real.rpow_mul hNF] at h
    have he : p * (2 / p) = (2 : ℝ) := by field_simp [hp0.ne']
    simpa only [he, Real.rpow_two] using h
  have hminkowski : NF ^ 2 ≤ NU ^ 2 + NV ^ 2 := by
    simpa only [NF, NU, NV, U, V] using! eLpNorm_toReal_complex_sq_le_re_im hp hF
  have hDineq : rieszBookDenominator p * NU ^ 2 ≤ NV ^ 2 := by
    change (c ^ (2 / p) - 1) * NU ^ 2 ≤ NV ^ 2
    nlinarith [hpower, hminkowski]
  have hD : 0 < rieszBookDenominator p := (rieszBookDenominator_bounds hp).1
  have hB : 0 ≤ B := Real.rpow_nonneg hD.le _
  have hBsq : B ^ 2 = (rieszBookDenominator p)⁻¹ := by
    dsimp only [B]
    rw [← Real.rpow_two, ← Real.rpow_mul hD.le]
    norm_num [Real.rpow_neg_one]
  have hsq : NU ^ 2 ≤ (B * NV) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hDineq (inv_nonneg.mpr hD.le)
    simpa only [mul_pow, hBsq, ← mul_assoc, inv_mul_cancel₀ hD.ne', one_mul] using! h
  have hUNV : NU ≤ B * NV := (sq_le_sq₀ hNU (mul_nonneg hB hNV)).1 hsq
  have hvextended : eLpNorm V (ENNReal.ofReal p) volume ≤ eLpNorm φ (ENNReal.ofReal p) volume := by
    simpa only [V, F, realCauchyFunction_eq_integral] using!
      realCauchyIntegral_im_eLpNorm_le hφ hc hp hη
  have hvreal : NV ≤ Nφ := ENNReal.toReal_mono hφp.eLpNorm_ne_top hvextended
  exact hUNV.trans (mul_le_mul_of_nonneg_left hvreal hB)

/-- The same actual real slice bound in the extended norm form needed by
native Fatou. Input and output finiteness are established first. -/
theorem realCauchyFunction_re_slice_eLpNorm_le {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {p : ℝ} (hp : 2 ≤ p)
    {η : ℝ} (hη : 0 < η) :
    eLpNorm (fun ξ : ℝ => (realCauchyFunction φ ((ξ : ℂ) + (η : ℂ) * I)).re)
      (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((rieszBookDenominator p) ^ (-(1 / 2 : ℝ))) *
        eLpNorm φ (ENNReal.ofReal p) volume := by
  have hF := realCauchyFunction_slice_memLp hφ hc hp hη
  have hU : MemLp (fun ξ : ℝ => (realCauchyFunction φ ((ξ : ℂ) + (η : ℂ) * I)).re)
      (ENNReal.ofReal p) volume := by simpa using! hF.re
  have hφp : MemLp φ (ENNReal.ofReal p) volume := hφ.memLp_of_hasCompactSupport hc
  have hB : 0 ≤ (rieszBookDenominator p) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (rieszBookDenominator_bounds hp).1.le _
  rw [← ENNReal.ofReal_toReal hU.eLpNorm_ne_top,
    ← ENNReal.ofReal_toReal hφp.eLpNorm_ne_top, ← ENNReal.ofReal_mul hB]
  exact ENNReal.ofReal_le_ofReal (realCauchyFunction_re_slice_norm_le hφ hc hp hη)

end LowDimensionalTopology.Geometry.Quasiconformal
