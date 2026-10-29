module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertScaledDisc
public import LowDimensionalTopology.External.LiZhongQC.Ch03.S15_Distortion

/-!
# Differentiating the finite inverse-norm disc potential

The derivative follows by the chain rule from the radial profile and the
ordinary derivative of a norm power. Its Wirtinger coefficient agrees
with the explicit boundary integral and has the corresponding limit as
the disc radius tends to infinity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem hasFDerivAt_scaled_inverseNorm {R : ℝ} {a : ℂ} (ha : a ≠ 0) :
    HasFDerivAt (fun b : ℂ => R / ‖b‖)
      ((-R * (‖a‖ ^ 3)⁻¹) • innerSL ℝ a) a := by
  have hc : (-1 : ℝ) * ‖a‖ ^ ((-1 : ℝ) - 2) = -(‖a‖ ^ 3)⁻¹ := by
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  have h := (LiZhongQC.s15_ra_hasFDerivAt_norm_rpow ha (-1)).const_smul R
  convert! h using 1
  · funext b
    simp only [Real.rpow_neg_one, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  · rw [hc, smul_smul]
    congr 1
    ring

/-- The full real derivative of the finite disc potential, obtained by
scaling to its fixed radial profile. -/
theorem hasFDerivAt_inverseNormDiscPotential {R : ℝ} {a : ℂ} (ha : a ≠ 0)
    (haR : ‖a‖ < R) :
    HasFDerivAt (inverseNormDiscPotential R)
      (((-R * (‖a‖ ^ 3)⁻¹) • innerSL ℝ a).smulRight
        (inverseNormUnitPoleRadialDensity (R / ‖a‖))) a := by
  have hscaled : 1 < R / ‖a‖ := (one_lt_div (norm_pos_iff.mpr ha)).mpr haR
  have hp := (hasDerivAt_inverseNormUnitPoleDiscPotential hscaled).hasFDerivAt.comp a
    (hasFDerivAt_scaled_inverseNorm (R := R) ha)
  have hd : HasFDerivAt
      (fun b : ℂ => inverseNormUnitPoleDiscPotential (R / ‖b‖))
      (((-R * (‖a‖ ^ 3)⁻¹) • innerSL ℝ a).smulRight
        (inverseNormUnitPoleRadialDensity (R / ‖a‖))) a := by
    convert! hp using 1
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds ha] with b hb
  exact inverseNormDiscPotential_eq_profile hb R

/-- The normalized real angular integral equals the radial density times
the radius. -/
theorem integral_inverseNormBoundaryFactor_eq_density (r : ℝ) :
    ((∫ θ in (0 : ℝ)..(2 * Real.pi), inverseNormBoundaryFactor r θ) : ℂ) =
      (r : ℂ) * inverseNormUnitPoleRadialDensity r := by
  rw [inverseNormUnitPoleRadialDensity_eq_fullCircle, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [inverseNormBoundaryFactor, inverseNormKernel, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv]

/-- The finite disc potential has exactly the coefficient obtained from
its boundary after rescaling. -/
theorem dz_inverseNormDiscPotential {R : ℝ} {a : ℂ} (ha : a ≠ 0) (haR : ‖a‖ < R) :
    LiZhongQC.dz (inverseNormDiscPotential R) a = inverseNormBoundaryCoefficient a R := by
  have hd := hasFDerivAt_inverseNormDiscPotential ha haR
  have hdz : LiZhongQC.dz (inverseNormDiscPotential R) a =
      (((-R * (‖a‖ ^ 3)⁻¹ : ℝ) : ℂ) * conj a / 2) *
        inverseNormUnitPoleRadialDensity (R / ‖a‖) := by
    rw [LiZhongQC.dz, hd.fderiv]
    apply Complex.ext <;>
      simp [ContinuousLinearMap.smulRight_apply, smul_apply,
        innerSL_apply_apply, Complex.inner, Complex.real_smul, div_eq_mul_inv,
        Complex.mul_re, Complex.mul_im] <;> ring
  have hρ : (‖a‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)
  have hn : a * conj a = (‖a‖ : ℂ) ^ 2 := by
    simpa only [Complex.ofReal_pow] using Complex.mul_conj' a
  have hconj : conj a = (‖a‖ : ℂ) ^ 2 / a := by
    apply (eq_div_iff ha).mpr
    simpa only [mul_comm] using hn
  have hscalar : (((-R * (‖a‖ ^ 3)⁻¹ : ℝ) : ℂ) * conj a / 2) =
      -(1 / (2 * a)) * ((R / ‖a‖ : ℝ) : ℂ) := by
    rw [hconj]
    push_cast
    field_simp [ha, hρ]
  rw [hdz, hscalar, inverseNormBoundaryCoefficient,
    integral_inverseNormBoundaryFactor_eq_density]
  ring

/-- At every nonzero second pole, the finite-disc Wirtinger derivative
tends to the rational inverse-distance coefficient. -/
theorem tendsto_dz_inverseNormDiscPotential {a : ℂ} (ha : a ≠ 0) :
    Tendsto (fun R : ℝ => LiZhongQC.dz (inverseNormDiscPotential R) a)
      atTop (𝓝 (-(Real.pi : ℂ) / a)) := by
  have heq : (fun R : ℝ => LiZhongQC.dz (inverseNormDiscPotential R) a) =ᶠ[atTop]
      inverseNormBoundaryCoefficient a := by
    filter_upwards [eventually_gt_atTop ‖a‖] with R hR
    exact dz_inverseNormDiscPotential ha hR
  exact (Filter.tendsto_congr' heq).mpr (tendsto_inverseNormBoundaryCoefficient ha)

end LowDimensionalTopology.Geometry.Quasiconformal
