/-
The norm-integrability transfer adapts Wu Xiaobin's Li-Zhong-QC-formalization,
commit 1c0d5473c020b66ed5106331a38a61536760b9b2, under Apache 2.0.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchyIntegral
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.GreenPolar
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Polar coordinates for the angular-strip Cauchy integral

Absolute integrability is transferred from the actual area integral before
changing the order of integration. The evaluation-point factor remains in
the joint integrand, including at the normalization points.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MeasureTheory Set Filter Complex
open scoped UpperHalfPlane ComplexConjugate ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- The radius-Jacobian integrand of the zero-extended normalized coefficient. -/
def firstCauchyJacobian (θ : Width) (z : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) * (infinitesimalZeroExtension θ (Complex.polarCoord.symm p) *
    Quasiconformal.firstVariationKernel z (Complex.polarCoord.symm p))

/-- The rational radial factor at a fixed angle. -/
def cauchyRayKernel (z : ℂ) (t r : ℝ) : ℂ :=
  (z - 1) * Complex.exp ((t : ℂ) * Complex.I) /
    ((Complex.polarCoord.symm (r, t) - 1) * (Complex.polarCoord.symm (r, t) - z))

/-- The angular and radial factors with the evaluation point retained. -/
def firstCauchyPolarIntegrand (θ : Width) (z : ℂ) (p : ℝ × ℝ) : ℂ :=
  -(Complex.I * z / 2) * (angularDensity θ p.2 : ℂ) * cauchyRayKernel z p.2 p.1

private theorem continuous_polarChart :
    Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
  have he : (fun p : ℝ × ℝ => Complex.polarCoord.symm p) =
      fun p : ℝ × ℝ => (p.1 : ℂ) *
        ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) := by
    funext p
    exact Complex.polarCoord_symm_apply p
  rw [he]
  fun_prop

/-- The actual polar Jacobian integrand is absolutely integrable on its full chart. -/
theorem integrableOn_firstCauchyJacobian (θ : Width) (z : ℂ) :
    IntegrableOn (firstCauchyJacobian θ z)
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) (volume : Measure (ℝ × ℝ)) := by
  have hm : Measurable (fun ζ : ℂ => infinitesimalZeroExtension θ ζ *
      Quasiconformal.firstVariationKernel z ζ) :=
    (measurable_infinitesimalZeroExtension θ).mul (LiZhongQC.ahK_measurable z)
  have hi := integrable_infinitesimalZeroExtension_mul_firstVariationKernel θ z
  refine ⟨((Complex.continuous_ofReal.comp continuous_fst).measurable.mul
    (hm.comp continuous_polarChart.measurable)).aestronglyMeasurable.restrict, ?_⟩
  have hkey : (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ‖firstCauchyJacobian θ z p‖ₑ) =
      ∫⁻ ζ : ℂ, ‖infinitesimalZeroExtension θ ζ *
        Quasiconformal.firstVariationKernel z ζ‖ₑ := by
    rw [← Complex.lintegral_comp_polarCoord_symm
      (fun ζ : ℂ => ‖infinitesimalZeroExtension θ ζ *
        Quasiconformal.firstVariationKernel z ζ‖ₑ)]
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    simp only [firstCauchyJacobian, enorm_mul, smul_eq_mul]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp.1]
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm, hkey]
  exact hi.2

private theorem arg_polarChart {r t : ℝ} (hr : 0 < r)
    (ht : t ∈ Ioo (-Real.pi) Real.pi) :
    Complex.arg (Complex.polarCoord.symm (r, t)) = t := by
  rw [Complex.polarCoord_symm_apply]
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
    (Complex.arg_mul_cos_add_sin_mul_I hr ⟨ht.1, ht.2.le⟩)

/-- Cancelling the positive radial Jacobian gives the literal radial kernel. -/
theorem firstCauchyJacobian_eq_polarIntegrand (θ : Width) (z : ℂ) {r t : ℝ}
    (hr : 0 < r) (ht : t ∈ Ioo (-Real.pi) Real.pi) :
    firstCauchyJacobian θ z (r, t) = firstCauchyPolarIntegrand θ z (r, t) := by
  classical
  let ζ : ℂ := Complex.polarCoord.symm (r, t)
  let u : ℂ := Complex.exp ((t : ℂ) * Complex.I)
  have harg : Complex.arg ζ = t := arg_polarChart hr ht
  change (r : ℂ) * (infinitesimalZeroExtension θ ζ *
      (z * (z - 1) / (ζ * (ζ - 1) * (ζ - z)))) =
    -(Complex.I * z / 2) * (angularDensity θ t : ℂ) *
      ((z - 1) * u / ((ζ - 1) * (ζ - z)))
  by_cases hstrip : t ∈ interval θ
  · have hζim : 0 < ζ.im := im_pos_of_arg_mem_interval θ (by simpa only [harg] using hstrip)
    have hζ1 : ζ - 1 ≠ 0 := by
      intro h
      have he : ζ = 1 := sub_eq_zero.mp h
      simp [he] at hζim
    by_cases hζz : ζ - z = 0
    · simp only [hζz, mul_zero, div_zero]
    have hu : u ≠ 0 := Complex.exp_ne_zero _
    have hru : ζ = (r : ℂ) * u := by
      simp only [ζ, u, Complex.polarCoord_symm_apply, Complex.exp_mul_I,
        Complex.ofReal_cos, Complex.ofReal_sin]
    have huconj : conj u = u⁻¹ := by
      apply (mul_left_cancel₀ hu)
      rw [mul_inv_cancel₀ hu, Complex.mul_conj']
      simp only [u, Complex.norm_exp_ofReal_mul_I, one_pow, Complex.ofReal_one]
    have hconj : conj ζ = (r : ℂ) * u⁻¹ := by
      rw [hru, map_mul, Complex.conj_ofReal, huconj]
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hθ0 : ((θ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr θ.property.1.ne'
    have hden1 : (r : ℂ) * u - 1 ≠ 0 := by simpa only [← hru] using hζ1
    have hdenz : (r : ℂ) * u - z ≠ 0 := by simpa only [← hru] using hζz
    simp only [infinitesimalZeroExtension, harg, ite_eq_left hstrip, angularDensity,
      infinitesimalScale, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [hconj, hru]
    field_simp [hr0, hθ0, hu, hden1, hdenz]
    ring
  · simp only [infinitesimalZeroExtension, harg, ite_eq_right hstrip,
      angularDensity, Complex.ofReal_zero, mul_zero, zero_mul]

private theorem positive_polarDomain_subset :
    Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi ⊆
      Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := by
  intro p hp
  exact ⟨hp.1, lt_trans (neg_lt_zero.mpr Real.pi_pos) hp.2.1, hp.2.2⟩

/-- The cancelled angular-radial integrand has genuine joint absolute integrability. -/
theorem integrableOn_firstCauchyPolarIntegrand (θ : Width) (z : ℂ) :
    IntegrableOn (firstCauchyPolarIntegrand θ z)
      (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi) (volume : Measure (ℝ × ℝ)) := by
  have hi := IntegrableOn.mono_set (integrableOn_firstCauchyJacobian θ z)
    positive_polarDomain_subset
  refine hi.congr_fun ?_ (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  exact firstCauchyJacobian_eq_polarIntegrand θ z hp.1
    (positive_polarDomain_subset hp).2

/-- Almost every actual angular slice has an integrable radial integrand. -/
theorem ae_integrableOn_firstCauchyPolarIntegrand (θ : Width) (z : ℂ) :
    ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)),
      IntegrableOn (fun r : ℝ => firstCauchyPolarIntegrand θ z (r, t))
        (Ioi (0 : ℝ)) (volume : Measure ℝ) := by
  have hp := integrableOn_firstCauchyPolarIntegrand θ z
  change Integrable _ ((volume : Measure (ℝ × ℝ)).restrict
    (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi)) at hp
  rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict] at hp
  exact hp.prod_left_ae

/-- The original area integral equals its actual angle-then-radius polar integral. -/
theorem firstCauchyTerm_eq_polarIntegral (θ : Width) (z : ℂ) :
    firstCauchyTerm θ z = -(1 / (Real.pi : ℂ)) *
      ∫ t in Ioo (0 : ℝ) Real.pi, ∫ r in Ioi (0 : ℝ),
        firstCauchyPolarIntegrand θ z (r, t) := by
  have hd : (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      firstCauchyJacobian θ z p) =
      ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
        firstCauchyJacobian θ z p := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_Ioi.prod measurableSet_Ioo) positive_polarDomain_subset
    intro p hp
    have ht : p.2 ≤ 0 := by
      by_contra h
      exact hp.2 ⟨hp.1.1, lt_of_not_ge h, hp.1.2.2⟩
    have hnot : p.2 ∉ interval θ := by
      intro h
      have hl : 0 < p.2 := lt_of_lt_of_le (sub_pos.mpr θ.property.2) h.1
      exact hl.not_ge ht
    have harg : Complex.arg (Complex.polarCoord.symm p) = p.2 := by
      rcases p with ⟨r, t⟩
      exact arg_polarChart hp.1.1 hp.1.2
    have hcoeff : infinitesimalZeroExtension θ (Complex.polarCoord.symm p) = 0 := by
      unfold infinitesimalZeroExtension
      apply ite_eq_right
      intro hm
      exact hnot (harg ▸ hm)
    change (p.1 : ℂ) * (infinitesimalZeroExtension θ (Complex.polarCoord.symm p) *
      Quasiconformal.firstVariationKernel z (Complex.polarCoord.symm p)) = 0
    rw [hcoeff, zero_mul, mul_zero]
  have hp := integrableOn_firstCauchyPolarIntegrand θ z
  change Integrable _ ((volume : Measure (ℝ × ℝ)).restrict
    (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi)) at hp
  rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict] at hp
  have hpolar : (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
      firstCauchyPolarIntegrand θ z p) =
      ∫ t in Ioo (0 : ℝ) Real.pi, ∫ r in Ioi (0 : ℝ),
        firstCauchyPolarIntegrand θ z (r, t) := by
    rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict]
    exact integral_prod_symm _ hp
  unfold firstCauchyTerm LiZhongQC.ahVar
  rw [← Complex.integral_comp_polarCoord_symm
    (fun ζ : ℂ => infinitesimalZeroExtension θ ζ * LiZhongQC.ahKer z ζ)]
  simp only [Complex.real_smul]
  change -(1 / (Real.pi : ℂ)) *
    (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, firstCauchyJacobian θ z p) = _
  rw [hd, ← hpolar]
  congr 1
  apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hpmem
  exact firstCauchyJacobian_eq_polarIntegrand θ z hpmem.1
    (positive_polarDomain_subset hpmem).2

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
