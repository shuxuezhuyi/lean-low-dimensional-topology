module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchyPolar
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The radial logarithm calculation for an angular-strip Cauchy integral

A difference of two principal logarithms has the radial rational kernel as
its derivative. Its endpoints determine the jump across the single pole ray.
Actual radial integrability is supplied by the joint area-integrability proof.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MeasureTheory Set Filter Complex
open scoped Topology ENNReal ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)

private theorem arg_neg_eq_of_arg_pos {z : ℂ} (hz : 0 < Complex.arg z) :
    Complex.arg (-z) = Complex.arg z - Real.pi := by
  apply Complex.arg_neg_eq_arg_sub_pi_iff.mpr
  have him : 0 ≤ z.im := Complex.arg_nonneg_iff.mp hz.le
  by_cases hip : 0 < z.im
  · exact Or.inl hip
  · have hi0 : z.im = 0 := le_antisymm (le_of_not_gt hip) him
    have hre : z.re < 0 := by
      by_contra h
      have harg : Complex.arg z = 0 :=
        Complex.arg_eq_zero_iff.mpr ⟨le_of_not_gt h, hi0⟩
      rw [harg] at hz
      exact (lt_irrefl (0 : ℝ)) hz
    exact Or.inr ⟨hi0, hre⟩

private theorem log_neg_eq_of_arg_pos {z : ℂ} (hz : 0 < Complex.arg z) :
    Complex.log (-z) = Complex.log z - (Real.pi : ℂ) * Complex.I := by
  simp only [Complex.log, norm_neg, arg_neg_eq_of_arg_pos hz, Complex.ofReal_sub]
  ring

private theorem ray_negative_phase_logs {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) Real.pi) :
    let a : ℂ := Complex.exp (-((t : ℂ) * Complex.I))
    Complex.log a = -((t : ℂ) * Complex.I) ∧
      Complex.arg a = -t ∧
      Complex.log (-a) = ((Real.pi - t : ℝ) : ℂ) * Complex.I := by
  let a : ℂ := Complex.exp (-((t : ℂ) * Complex.I))
  have hlog : Complex.log a = -((t : ℂ) * Complex.I) := by
    apply Complex.log_exp
    · simpa using (neg_lt_neg ht.2)
    · have h : -t ≤ Real.pi := by linarith [Real.pi_pos, ht.1]
      simpa using h
  have harg : Complex.arg a = -t := by
    simpa [Complex.log_im] using congrArg Complex.im hlog
  have him : a.im < 0 := Complex.arg_neg_iff.mp (by rw [harg]; linarith [ht.1])
  have hargneg : Complex.arg (-a) = Real.pi - t := by
    rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg him, harg]
    ring
  have hn : ‖a‖ = 1 := by
    dsimp only [a]
    rw [Complex.norm_exp]
    simp
  refine ⟨hlog, harg, ?_⟩
  change (Real.log ‖-a‖ : ℂ) + (Complex.arg (-a) : ℂ) * Complex.I = _
  rw [norm_neg, hn, Real.log_one, Complex.ofReal_zero, zero_add, hargneg]

private theorem shifted_ray_mem_slitPlane {c : ℂ} (hc : -c ∈ Complex.slitPlane)
    {r : ℝ} (hr : 0 ≤ r) : (r : ℂ) - c ∈ Complex.slitPlane := by
  rcases Complex.mem_slitPlane_iff.mp hc with hre | him
  · apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.neg_re] at hre
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  · apply Complex.mem_slitPlane_iff.mpr
    right
    simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.neg_im] using him

private theorem cauchyRay_log_data {z : ℂ} {t : ℝ} (hz : z ≠ 0)
    (ht : t ∈ Ioo (0 : ℝ) Real.pi) (hzt : Complex.arg z ≠ t) :
    ∃ F : ℝ → ℂ,
      (∀ r ∈ Ici (0 : ℝ), HasDerivAt F (cauchyRayKernel z t r) r) ∧
      Tendsto F atTop (𝓝 0) ∧
      F 0 = Complex.log z -
        (if t < Complex.arg z then (2 * (Real.pi : ℂ)) * Complex.I else 0) := by
  let u : ℂ := Complex.exp ((t : ℂ) * Complex.I)
  let a : ℂ := Complex.exp (-((t : ℂ) * Complex.I))
  let b : ℂ := z * a
  let F : ℝ → ℂ := fun r => Complex.log ((r : ℂ) - b) - Complex.log ((r : ℂ) - a)
  have hu : u ≠ 0 := Complex.exp_ne_zero _
  have ha : a ≠ 0 := Complex.exp_ne_zero _
  have hb : b ≠ 0 := mul_ne_zero hz ha
  have hainv : a = u⁻¹ := Complex.exp_neg _
  have hua : u * a = 1 := by rw [hainv, mul_inv_cancel₀ hu]
  have hbu : b * u = z := by
    dsimp [b]
    calc z * a * u = z * (u * a) := by ring
      _ = z := by rw [hua, mul_one]
  obtain ⟨hloga, harga, hlognega⟩ := ray_negative_phase_logs ht
  have hlogu : Complex.log u = (t : ℂ) * Complex.I := by
    apply Complex.log_exp
    · have h : -Real.pi < t := lt_trans (neg_lt_zero.mpr Real.pi_pos) ht.1
      simpa using h
    · simpa using ht.2.le
  have hargu : Complex.arg u = t := by
    simpa [Complex.log_im] using congrArg Complex.im hlogu
  have hane : -a ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    have hai : a.im < 0 := Complex.arg_neg_iff.mp (by rw [harga]; linarith [ht.1])
    simpa only [Complex.neg_im, neg_ne_zero] using hai.ne
  have hbne : -b ∈ Complex.slitPlane := by
    by_cases hbi : b.im = 0
    · have hbr0 : b.re ≠ 0 := by
        intro hr0
        exact hb (Complex.ext hr0 hbi)
      have hbr : b.re < 0 := by
        by_contra h
        have hbrp : 0 < b.re := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hbr0)
        have hbreal : b = (b.re : ℂ) := Complex.ext rfl (by simpa using hbi)
        apply hzt
        rw [← hbu, hbreal, Complex.arg_real_mul _ hbrp, hargu]
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hbr))
    · exact Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using hbi))
  have hder : ∀ r ∈ Ici (0 : ℝ), HasDerivAt F (cauchyRayKernel z t r) r := by
    intro r hr
    have hsa := shifted_ray_mem_slitPlane hane hr
    have hsb := shifted_ray_mem_slitPlane hbne hr
    have hxa : HasDerivAt (fun x : ℝ => (x : ℂ) - a) 1 r := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := r)).sub_const a
    have hxb : HasDerivAt (fun x : ℝ => (x : ℂ) - b) 1 r := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := r)).sub_const b
    apply ((hxb.clog_real hsb).sub (hxa.clog_real hsa)).congr_deriv
    have hc : Complex.polarCoord.symm (r, t) = (r : ℂ) * u := by
      simp only [u, Complex.polarCoord_symm_apply, Complex.exp_mul_I,
        Complex.ofReal_cos, Complex.ofReal_sin]
    have hea : (r : ℂ) * u - 1 = u * ((r : ℂ) - a) := by
      calc (r : ℂ) * u - 1 = (r : ℂ) * u - u * a := by rw [hua]
        _ = _ := by ring
    have heb : (r : ℂ) * u - z = u * ((r : ℂ) - b) := by
      calc (r : ℂ) * u - z = (r : ℂ) * u - u * b := by rw [mul_comm u b, hbu]
        _ = _ := by ring
    have ha0 : (r : ℂ) - a ≠ 0 := Complex.slitPlane_ne_zero hsa
    have hb0 : (r : ℂ) - b ≠ 0 := Complex.slitPlane_ne_zero hsb
    have hda : (r : ℂ) * u - 1 ≠ 0 := by rw [hea]; exact mul_ne_zero hu ha0
    have hdb : (r : ℂ) * u - z ≠ 0 := by rw [heb]; exact mul_ne_zero hu hb0
    have ha0' : (r : ℂ) - u⁻¹ ≠ 0 := by simpa only [hainv] using ha0
    have hb0' : (r : ℂ) - z * u⁻¹ ≠ 0 := by simpa only [b, hainv] using hb0
    change 1 / ((r : ℂ) - b) - 1 / ((r : ℂ) - a) = cauchyRayKernel z t r
    simp only [b, hainv, cauchyRayKernel, hc]
    field_simp [hu, ha0', hb0', hda, hdb]
    ring
  have hinv : Tendsto (fun r : ℝ => (r : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_inv, Complex.ofReal_zero, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp tendsto_inv_atTop_zero
  have hloglim (c : ℂ) : Tendsto (fun r : ℝ => Complex.log (1 - c / (r : ℂ)))
      atTop (𝓝 0) := by
    have hc : Tendsto (fun r : ℝ => c / (r : ℂ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul c
    have hone : Tendsto (fun r : ℝ => 1 - c / (r : ℂ)) atTop (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds.sub hc)
    simpa only [Complex.log_one] using hone.clog Complex.one_mem_slitPlane
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h := (hloglim b).sub (hloglim a)
    simp only [sub_zero] at h
    apply Tendsto.congr' ?_ h
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with r hr
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hscale (c : ℂ) : (r : ℂ) * (1 - c / (r : ℂ)) = (r : ℂ) - c := by
      field_simp [hr0]
    have hsubne (c : ℂ) (hc : -c ∈ Complex.slitPlane) : 1 - c / (r : ℂ) ≠ 0 := by
      intro hc0
      have hn := Complex.slitPlane_ne_zero (shifted_ray_mem_slitPlane hc hr.le)
      apply hn
      rw [← hscale c, hc0, mul_zero]
    have hlb := Complex.log_ofReal_mul hr (hsubne b hbne)
    have hla := Complex.log_ofReal_mul hr (hsubne a hane)
    rw [hscale b] at hlb
    rw [hscale a] at hla
    dsimp [F]
    rw [hlb, hla]
    ring
  have hzero : F 0 = Complex.log z -
      (if t < Complex.arg z then (2 * (Real.pi : ℂ)) * Complex.I else 0) := by
    simp only [F, Complex.ofReal_zero, zero_sub]
    by_cases hangle : t < Complex.arg z
    · have hargpos : 0 < Complex.arg z := ht.1.trans hangle
      have hargnegz := arg_neg_eq_of_arg_pos hargpos
      have hsum : Complex.arg (-z) + Complex.arg a ∈ Ioc (-Real.pi) Real.pi := by
        rw [hargnegz, harga]
        constructor <;> linarith [Complex.arg_le_pi z, ht.1, Real.pi_pos]
      have hm := Complex.log_mul (neg_ne_zero.mpr hz) ha hsum
      have he : (-z) * a = -b := by dsimp [b]; ring
      rw [he] at hm
      rw [hm, log_neg_eq_of_arg_pos hargpos, hloga, hlognega, ite_eq_left hangle]
      simp only [Complex.ofReal_sub]
      ring
    · have hangle' : Complex.arg z < t := lt_of_le_of_ne (le_of_not_gt hangle) hzt
      have hargnega : Complex.arg (-a) = Real.pi - t := by
        have h := congrArg Complex.im hlognega
        simpa [Complex.log_im] using h
      have hsum : Complex.arg z + Complex.arg (-a) ∈ Ioc (-Real.pi) Real.pi := by
        rw [hargnega]
        constructor <;> linarith [Complex.neg_pi_lt_arg z, ht.2]
      have hm := Complex.log_mul hz (neg_ne_zero.mpr ha) hsum
      have he : z * (-a) = -b := by dsimp [b]; ring
      rw [he] at hm
      rw [hm, ite_eq_right hangle]
      ring
  exact ⟨F, hder, hlim, hzero⟩

private theorem integral_cauchyRayKernel_eq_of_integrable {z : ℂ} {t : ℝ}
    (hz : z ≠ 0) (ht : t ∈ Ioo (0 : ℝ) Real.pi) (hzt : Complex.arg z ≠ t)
    (hi : IntegrableOn (cauchyRayKernel z t) (Ioi (0 : ℝ)) (volume : Measure ℝ)) :
    (∫ r in Ioi (0 : ℝ), cauchyRayKernel z t r) =
      (if t < Complex.arg z then (2 * (Real.pi : ℂ)) * Complex.I else 0) - Complex.log z := by
  obtain ⟨F, hd, hlim, hzero⟩ := cauchyRay_log_data hz ht hzt
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hi hlim, hzero]
  ring

/-- The actual weighted radial integral has the logarithmic jump formula at almost every angle. -/
theorem ae_integral_firstCauchyPolarIntegrand_eq {z : ℂ} (hz : z ≠ 0) (θ : Width) :
    ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)),
      (∫ r in Ioi (0 : ℝ), firstCauchyPolarIntegrand θ z (r, t)) =
        -(Complex.I * z / 2) * (angularDensity θ t : ℂ) *
          ((if t < Complex.arg z then (2 * (Real.pi : ℂ)) * Complex.I else 0) -
            Complex.log z) := by
  classical
  have hne : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)), t ≠ Complex.arg z :=
    ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
  filter_upwards [ae_integrableOn_firstCauchyPolarIntegrand θ z, hne,
    ae_restrict_mem measurableSet_Ioo] with t hi htne ht
  by_cases hs : t ∈ interval θ
  · let c : ℂ := -(Complex.I * z / 2) * (1 / (2 * (θ : ℝ)) : ℝ)
    have hθ : (θ : ℝ) ≠ 0 := θ.property.1.ne'
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (mul_ne_zero Complex.I_ne_zero hz)
        (by norm_num)))
        (Complex.ofReal_ne_zero.mpr (one_div_ne_zero (mul_ne_zero (by norm_num) hθ)))
    have hfun : (fun r : ℝ => firstCauchyPolarIntegrand θ z (r, t)) =
        fun r : ℝ => c * cauchyRayKernel z t r := by
      funext r
      simp only [firstCauchyPolarIntegrand, angularDensity, ite_eq_left hs, c]
    have hic : Integrable (fun r : ℝ => c * cauchyRayKernel z t r)
        ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))) := by
      rw [← hfun]
      exact hi
    have hir : IntegrableOn (cauchyRayKernel z t) (Ioi (0 : ℝ))
        (volume : Measure ℝ) :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) (cauchyRayKernel z t)).mp hic
    have hv := integral_cauchyRayKernel_eq_of_integrable hz ht htne.symm hir
    rw [hfun, integral_const_mul, hv]
    simp only [c, angularDensity, ite_eq_left hs]
  · simp only [firstCauchyPolarIntegrand, angularDensity, ite_eq_right hs,
      Complex.ofReal_zero, mul_zero, zero_mul, integral_zero]

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
