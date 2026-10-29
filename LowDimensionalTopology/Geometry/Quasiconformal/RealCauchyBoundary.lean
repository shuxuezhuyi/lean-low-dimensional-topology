module

public import LowDimensionalTopology.Geometry.Quasiconformal.RealCauchyHolomorphic
public import LowDimensionalTopology.Geometry.Quasiconformal.RealHilbertPrincipalValue
public import LowDimensionalTopology.Geometry.Quasiconformal.RealHilbertComponents
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The real Cauchy boundary limit

Pairing the real Cauchy kernel and applying dominated
convergence to the removable quotient times t^2/(t^2+eta^2). This proves
the boundary limit of the regularized Cauchy real part to the original
positive1/pi principal-value transform. No Hilbert norm bound or Poisson
boundary theorem is assumed.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

private def realHilbertPairedRealKernel (φ : ℝ → ℝ) (ξ t : ℝ) : ℝ :=
  (realHilbertPairedKernel (fun x => (φ x : ℂ)) ξ t).re

private def realCauchyPairWeight (t η : ℝ) : ℝ := t ^ 2 / (t ^ 2 + η ^ 2)

private theorem realHilbertPairedRealKernel_of_ne (φ : ℝ → ℝ) (ξ : ℝ)
    {t : ℝ} (ht : t ≠ 0) :
    realHilbertPairedRealKernel φ ξ t = t⁻¹ * (φ (ξ + t) - φ (ξ - t)) := by
  change Complex.reCLM (realHilbertPairedKernel (fun x => (φ x : ℂ)) ξ t) = _
  rw [realHilbertPairedKernel_of_ne _ ξ ht, map_smul]
  simp only [Complex.reCLM_apply, Complex.sub_re, Complex.ofReal_re, smul_eq_mul]

private theorem realCauchy_re_eq_weighted_pair {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (ξ : ℝ)
    {η : ℝ} (hη : 0 < η) :
    (realCauchyFunction φ ((ξ : ℂ) + (η : ℂ) * I)).re =
      (1 / Real.pi) * ∫ t in Ioi (0 : ℝ),
        realHilbertPairedRealKernel φ ξ t * realCauchyPairWeight t η := by
  let g : ℝ → ℝ := fun x => φ x * (x - ξ) / ((x - ξ) ^ 2 + η ^ 2)
  let K : ℝ → ℝ := fun t => φ (ξ + t) * t / (t ^ 2 + η ^ 2)
  have hden (x : ℝ) : (x - ξ) ^ 2 + η ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hgcont : Continuous g :=
    (hφ.continuous.mul (continuous_id.sub continuous_const)).div
      (((continuous_id.sub continuous_const).pow 2).add continuous_const) hden
  have hgcompact : HasCompactSupport g := by
    rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
    exact hc.mono fun x hx => by simp [g, hx]
  have hg : Integrable g (volume : Measure ℝ) := hgcont.integrable_of_hasCompactSupport hgcompact
  have hK : Integrable K (volume : Measure ℝ) := by
    simpa only [g, K, add_sub_cancel_left] using! hg.comp_add_left ξ
  have hshift : (∫ x : ℝ, g x) = ∫ t : ℝ, K t := by
    rw [← integral_add_left_eq_self g ξ]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by simp only [g, K, add_sub_cancel_left]
  have hreflect : (∫ t in Iic (0 : ℝ), K t) = ∫ t in Ioi (0 : ℝ), K (-t) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi (0 : ℝ) K).symm
  have hneg : IntegrableOn (fun t : ℝ => K (-t)) (Ioi (0 : ℝ)) := hK.comp_neg.integrableOn
  have hpos : IntegrableOn K (Ioi (0 : ℝ)) := hK.integrableOn
  have hkernel (t : ℝ) (ht : 0 < t) :
      K (-t) + K t = realHilbertPairedRealKernel φ ξ t * realCauchyPairWeight t η := by
    rw [realHilbertPairedRealKernel_of_ne φ ξ (ne_of_gt ht)]
    have hden0 : t ^ 2 + η ^ 2 ≠ 0 :=
      ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos ht) (sq_nonneg η))
    simp only [K, realCauchyPairWeight, neg_sq, sub_eq_add_neg]
    field_simp [ne_of_gt ht, hden0]
    ring
  have hpair : (∫ t : ℝ, K t) = ∫ t in Ioi (0 : ℝ),
      realHilbertPairedRealKernel φ ξ t * realCauchyPairWeight t η := by
    calc
      _ = (∫ t in Iic (0 : ℝ), K t) + ∫ t in Ioi (0 : ℝ), K t :=
        (intervalIntegral.integral_Iic_add_Ioi hK.integrableOn hpos).symm
      _ = ∫ t in Ioi (0 : ℝ), K (-t) + K t := by
        rw [hreflect]
        simpa using! (integral_add hneg hpos).symm
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact hkernel t ht
  rw [realCauchyFunction_eq_integral, (realCauchyIntegral_re_im hφ.continuous hc ξ hη).1]
  change (1 / Real.pi) * (∫ x : ℝ, g x) = _
  rw [hshift, hpair]

/-- The regularized real Cauchy part converges to the real part of the
ACTUAL original complex-codomain Hilbert transform of the real test. -/
theorem tendsto_realCauchy_re {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (ξ : ℝ) :
    Tendsto (fun η : ℝ => (realCauchyFunction φ ((ξ : ℂ) + (η : ℂ) * I)).re)
      (𝓝[>] (0 : ℝ)) (𝓝 ((realHilbertTransform (fun x => (φ x : ℂ)) ξ).re)) := by
  have hcast : ContDiff ℝ 1 (fun x => (φ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have hcCast : HasCompactSupport (fun x => (φ x : ℂ)) :=
    hc.comp_left (g := fun x : ℝ => (x : ℂ)) rfl
  have hQ := integrable_realHilbertPairedKernel hcast hcCast ξ
  have hfun : realHilbertPairedRealKernel φ ξ =
      (fun t : ℝ => (realHilbertPairedKernel (fun x => (φ x : ℂ)) ξ t).re) := rfl
  have hQr : Integrable (realHilbertPairedRealKernel φ ξ) (volume : Measure ℝ) := by
    rw [hfun]
    simpa only [RCLike.re_eq_complex_re] using! hQ.re
  have hQrcont : Continuous (realHilbertPairedRealKernel φ ξ) := by
    rw [hfun]
    exact Complex.continuous_re.comp (continuous_realHilbertPairedKernel hcast ξ)
  have hQon := hQ.integrableOn (s := Ioi (0 : ℝ))
  have hHpaired := (realHilbert_principalValue_and_eq_paired hcast hcCast ξ).2
  have hscale (w : ℂ) : (1 / (Real.pi : ℂ)) * w = (1 / Real.pi : ℝ) • w := by
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
  have hHre : (realHilbertTransform (fun x => (φ x : ℂ)) ξ).re =
      (1 / Real.pi) * ∫ t in Ioi (0 : ℝ), realHilbertPairedRealKernel φ ξ t := by
    rw [hHpaired, hscale]
    change Complex.reCLM ((1 / Real.pi : ℝ) •
      (∫ t in Ioi (0 : ℝ), realHilbertPairedKernel (fun x => (φ x : ℂ)) ξ t)) = _
    rw [map_smul, ← Complex.reCLM.integral_comp_comm hQon]
    simp only [smul_eq_mul, Complex.reCLM_apply, realHilbertPairedRealKernel]
  have hmeas (η : ℝ) : AEStronglyMeasurable
      (fun t : ℝ => realHilbertPairedRealKernel φ ξ t * realCauchyPairWeight t η)
      (volume.restrict (Ioi (0 : ℝ))) := by
    simpa only [realCauchyPairWeight] using!
      (hQrcont.measurable.mul ((continuous_id.pow 2).measurable.div
        (((continuous_id.pow 2).add continuous_const).measurable))).aestronglyMeasurable
  have hbound (η : ℝ) : ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      ‖realHilbertPairedRealKernel φ ξ t * realCauchyPairWeight t η‖ ≤
        ‖realHilbertPairedRealKernel φ ξ t‖ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hden : 0 < t ^ 2 + η ^ 2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_pos ht) (sq_nonneg η)
    have hw0 : 0 ≤ realCauchyPairWeight t η := div_nonneg (sq_nonneg t) hden.le
    have hw1 : realCauchyPairWeight t η ≤ 1 :=
      (div_le_one hden).2 (le_add_of_nonneg_right (sq_nonneg η))
    rw [norm_mul, Real.norm_of_nonneg hw0]
    exact mul_le_of_le_one_right (norm_nonneg _) hw1
  have hweight (t : ℝ) (ht : 0 < t) :
      Tendsto (realCauchyPairWeight t) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hweightfun : realCauchyPairWeight t =
        (fun η : ℝ => t ^ 2 / (t ^ 2 + η ^ 2)) := rfl
    rw [hweightfun]
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ht)
    have hcont : ContinuousAt (fun η : ℝ => t ^ 2 / (t ^ 2 + η ^ 2)) 0 :=
      continuousAt_const.div (continuousAt_const.add (continuousAt_id.pow 2)) (by simpa using ht2)
    simpa [ht2] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hpoint : ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun η : ℝ => realHilbertPairedRealKernel φ ξ t * realCauchyPairWeight t η)
        (𝓝[>] (0 : ℝ)) (𝓝 (realHilbertPairedRealKernel φ ξ t)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hconst : Tendsto (fun _ : ℝ => realHilbertPairedRealKernel φ ξ t)
        (𝓝[>] (0 : ℝ)) (𝓝 (realHilbertPairedRealKernel φ ξ t)) := tendsto_const_nhds
    simpa only [mul_one] using hconst.mul (hweight t ht)
  have hlim : Tendsto (fun η : ℝ => (1 / Real.pi) *
      ∫ t in Ioi (0 : ℝ), realHilbertPairedRealKernel φ ξ t * realCauchyPairWeight t η)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((1 / Real.pi) * ∫ t in Ioi (0 : ℝ), realHilbertPairedRealKernel φ ξ t)) := by
    have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ))) (fun t : ℝ => ‖realHilbertPairedRealKernel φ ξ t‖)
      (Eventually.of_forall hmeas) (Eventually.of_forall hbound) hQr.integrableOn.norm hpoint
    exact tendsto_const_nhds.mul h
  rw [hHre]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact (realCauchy_re_eq_weighted_pair hφ hc ξ hη).symm

/-- The same boundary limit in the literal complex codomain of the original
principal value. Reality is supplied by the actual proved PV identity. -/
theorem tendsto_realCauchy_re_ofReal {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (ξ : ℝ) :
    Tendsto (fun η : ℝ => ((realCauchyFunction φ ((ξ : ℂ) + (η : ℂ) * I)).re : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (realHilbertTransform (fun x => (φ x : ℂ)) ξ)) := by
  have h := Complex.continuous_ofReal.tendsto _ |>.comp (tendsto_realCauchy_re hφ hc ξ)
  have hvalue : ((realHilbertTransform (fun x => (φ x : ℂ)) ξ).re : ℂ) =
      realHilbertTransform (fun x => (φ x : ℂ)) ξ := by
    apply Complex.ext
    · rfl
    · change (0 : ℝ) = (realHilbertTransform (fun x => (φ x : ℂ)) ξ).im
      exact (realHilbertTransform_ofReal_im_eq_zero hφ hc ξ).symm
  simpa only [hvalue, Function.comp_def] using! h

end LowDimensionalTopology.Geometry.Quasiconformal
