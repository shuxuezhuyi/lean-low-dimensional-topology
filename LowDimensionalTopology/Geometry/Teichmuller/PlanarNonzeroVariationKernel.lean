module

public import LowDimensionalTopology.Geometry.Teichmuller.PlanarCoefficientVariation
public import LowDimensionalTopology.Geometry.Quasiconformal.NormalBeltramiInverse
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# The full-plane first-variation kernel at an arbitrary coefficient

The actual canonical normalized solution supplies both the genuine Beltrami
PDE and the proved quasiconformal area formula. Its Jacobian cancels the actual
coefficient transport weight. This identifies the transported zero-base first
variation with the literal nonzero-base integral and proves absolute
integrability, for every original full-plane coefficient and every direction.
The locally uniform parameter conclusions use the same actual canonical family.

The analytic PDE and area formula reuse Wu Xiaobin's LiZhongQC development;
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology LiZhongQC
open scoped ENNReal ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.PlanarCoefficientTransport

private theorem integrable_jacobian_mul
    (e : ℂ ≃ₜ ℂ) {K : ℝ} (he : IsKQC e univ K)
    {G : ℂ → ℂ} (hG : Integrable G (volume : Measure ℂ)) :
    Integrable (fun z => (jacobian e z : ℂ) * G (e z)) (volume : Measure ℂ) := by
  have hmap : Integrable G (Measure.map e
      (volume.withDensity (fun z => ENNReal.ofReal (jacobian e z)))) := by
    rw [Quasiconformal.quasiconformal_homeomorph_map_jacobian e he]
    exact hG
  have hpull := hmap.comp_measurable e.continuous.measurable
  have hJ : Measurable (fun z => ENNReal.ofReal (jacobian e z)) :=
    (((measurable_dz e).norm.pow_const 2).sub
      ((measurable_dzbar e).norm.pow_const 2)).ennreal_ofReal
  have hfinite : ∀ᵐ z : ℂ ∂volume, ENNReal.ofReal (jacobian e z) < ∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hweighted :=
    (integrable_withDensity_iff_integrable_smul' hJ hfinite).1 hpull
  have hpos : ∀ᵐ z : ℂ ∂volume, 0 < jacobian e z := by
    simpa only [Measure.restrict_univ] using thm9_6_cor2_jacobian_pos he
  apply hweighted.congr
  filter_upwards [hpos] with z hz
  exact (congrArg (fun r : ℝ => r • G (e z))
    (ENNReal.toReal_ofReal hz.le)).trans Complex.real_smul

/-- The same actual canonical map satisfies its original coefficient PDE. -/
theorem normalizedMap_beltrami_ae (ν : MeasurableBeltramiBall) :
    ∀ᵐ z : ℂ ∂volume,
      dzbar (normalizedMap ν) z = ν.val z * dz (normalizedMap ν) z := by
  have hpde := abW_ae_dilatation
    (MeasurableBeltramiBall.normalizedSolution_spec ν).2.1
  rw [Measure.restrict_univ] at hpde
  filter_upwards [hpde, (MeasurableBeltramiBall.normalizedSolution_spec ν).1.2.2.2.2]
    with z hz hν
  exact hz.1.trans (by rw [hν])

/-- The literal Jacobian cancels the actual coefficient denominator and phase. -/
theorem jacobian_mul_derivativeWeight_ae (ν : MeasurableBeltramiBall) :
    ∀ᵐ z : ℂ ∂volume,
      (jacobian (normalizedMap ν) z : ℂ) * derivativeWeight ν z =
        dz (normalizedMap ν) z ^ 2 := by
  filter_upwards [normalizedMap_beltrami_ae ν, coefficientDenominator_lower_ae ν,
    norm_derivativePhase_ae ν] with z hpde hden hphase
  have hd : coefficientDenominator ν z ≠ 0 :=
    norm_pos_iff.mp ((one_sub_norm_sq_pos ν).trans_le hden)
  have hp : dz (normalizedMap ν) z ≠ 0 := by
    intro he
    have hz : ‖derivativePhase ν z‖ = 0 := by simp [derivativePhase, he]
    linarith
  have hpc : conj (dz (normalizedMap ν) z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr hp
  have hJ : (jacobian (normalizedMap ν) z : ℂ) =
      coefficientDenominator ν z *
        (dz (normalizedMap ν) z * conj (dz (normalizedMap ν) z)) := by
    have h1 : dz (normalizedMap ν) z * conj (dz (normalizedMap ν) z) =
        ((‖dz (normalizedMap ν) z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.sq_norm]
    have h2 : dzbar (normalizedMap ν) z * conj (dzbar (normalizedMap ν) z) =
        ((‖dzbar (normalizedMap ν) z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.sq_norm]
    have hraw : (jacobian (normalizedMap ν) z : ℂ) =
        dz (normalizedMap ν) z * conj (dz (normalizedMap ν) z) -
          dzbar (normalizedMap ν) z * conj (dzbar (normalizedMap ν) z) := by
      exact (Complex.ofReal_sub (‖dz (normalizedMap ν) z‖ ^ 2)
        (‖dzbar (normalizedMap ν) z‖ ^ 2)).trans
          (congrArg₂ (fun a b : ℂ => a - b) h1.symm h2.symm)
    rw [hraw, hpde, map_mul]
    unfold coefficientDenominator
    ring
  rw [hJ]
  unfold derivativeWeight derivativePhase
  simp only [div_eq_mul_inv]
  calc
    _ = (coefficientDenominator ν z * (coefficientDenominator ν z)⁻¹) *
        (conj (dz (normalizedMap ν) z) * (conj (dz (normalizedMap ν) z))⁻¹) *
        (dz (normalizedMap ν) z * dz (normalizedMap ν) z) := by ring
    _ = dz (normalizedMap ν) z ^ 2 := by
      rw [mul_inv_cancel₀ hd, mul_inv_cancel₀ hpc, one_mul, one_mul, pow_two]

/-- The actual transported class evaluated along the same forward map. -/
theorem ambientDerivative_forward_coe_ae (ν : MeasurableBeltramiBall) (η : Ambient) :
    ∀ᵐ z : ℂ ∂volume,
      ambientDerivative ν η (normalizedMap ν z) = derivativeWeight ν z * η z := by
  filter_upwards [(normalizedEquiv_quasiMeasurePreserving ν).ae
    (ambientDerivative_weighted_coe_ae ν η)] with z hz
  simpa only [normalizedEquiv, Homeomorph.coe_toEquiv, Homeomorph.coe_symm_toEquiv,
    Homeomorph.symm_apply_apply] using hz

/-- The original normalized nonzero-base integrand, on the full plane. -/
def nonzeroVariationIntegrand (ν : MeasurableBeltramiBall) (η : Ambient) (w z : ℂ) : ℂ :=
  η z * normalizedMap ν w * (normalizedMap ν w - 1) * dz (normalizedMap ν) z ^ 2 /
    (normalizedMap ν z * (normalizedMap ν z - 1) *
      (normalizedMap ν z - normalizedMap ν w))

private theorem nonzero_integrand_eq_weighted_ae
    (ν : MeasurableBeltramiBall) (η : Ambient) (w : ℂ) :
    (fun z => (jacobian (normalizedMap ν) z : ℂ) *
      (ambientDerivative ν η (normalizedMap ν z) *
        Quasiconformal.firstVariationKernel (normalizedMap ν w) (normalizedMap ν z)))
      =ᵐ[volume] nonzeroVariationIntegrand ν η w := by
  filter_upwards [ambientDerivative_forward_coe_ae ν η,
    jacobian_mul_derivativeWeight_ae ν] with z ht hJ
  calc
    _ = ((jacobian (normalizedMap ν) z : ℂ) * derivativeWeight ν z) * η z *
        Quasiconformal.firstVariationKernel (normalizedMap ν w) (normalizedMap ν z) := by
      rw [ht]
      ring
    _ = dz (normalizedMap ν) z ^ 2 * η z *
        Quasiconformal.firstVariationKernel (normalizedMap ν w) (normalizedMap ν z) := by rw [hJ]
    _ = nonzeroVariationIntegrand ν η w z := by
      unfold nonzeroVariationIntegrand Quasiconformal.firstVariationKernel
      simp only [div_eq_mul_inv]
      ring

/-- Absolute integrability holds for every original coefficient, every bounded
coefficient direction, and every evaluation point, with no support condition. -/
theorem nonzeroVariationIntegrand_integrable
    (ν : MeasurableBeltramiBall) (η : Ambient) (w : ℂ) :
    Integrable (nonzeroVariationIntegrand ν η w) (volume : Measure ℂ) := by
  have hG : Integrable (fun ζ => ambientDerivative ν η ζ *
      Quasiconformal.firstVariationKernel (normalizedMap ν w) ζ) (volume : Measure ℂ) :=
    (ah_ker_integrable (normalizedMap ν w)).bdd_mul
      (Lp.aestronglyMeasurable (ambientDerivative ν η))
      (lpInfinity_norm_ae_le (ambientDerivative ν η))
  exact (integrable_jacobian_mul (normalizedMap ν)
    (MeasurableBeltramiBall.normalizedSolution_spec ν).2.1 hG).congr
      (nonzero_integrand_eq_weighted_ae ν η w)

/-- The transported first variation is exactly the original full-plane integral. -/
theorem firstVariation_transport_eq_integral
    (ν : MeasurableBeltramiBall) (η : Ambient) (w : ℂ) :
    Quasiconformal.firstVariation (ambientDerivative ν η) (normalizedMap ν w) =
      -(1 / (Real.pi : ℂ)) * ∫ z,
        η z * normalizedMap ν w * (normalizedMap ν w - 1) * dz (normalizedMap ν) z ^ 2 /
          (normalizedMap ν z * (normalizedMap ν z - 1) *
            (normalizedMap ν z - normalizedMap ν w)) := by
  obtain ⟨hfh, fx, fy, hfd, hfb⟩ :=
    (MeasurableBeltramiBall.normalizedSolution_spec ν).2.2.2
  have hc := sp_c_change_of_variables (MeasurableBeltramiBall.norm_lt_one ν)
    isOpen_univ (MeasurableBeltramiSpace.isBeltramiCoeff ν.val).2 hfh hfd hfb
    (fun ζ => ambientDerivative ν η ζ *
      Quasiconformal.firstVariationKernel (normalizedMap ν w) ζ)
  simp only [(MeasurableBeltramiBall.normalizedSolution_spec ν).1.2.1,
    Measure.restrict_univ] at hc
  unfold Quasiconformal.firstVariation
  apply congrArg (fun c : ℂ => -(1 / (Real.pi : ℂ)) * c)
  exact hc.trans (integral_congr_ae (nonzero_integrand_eq_weighted_ae ν η w))

/-- The original full nonzero-base kernel is the locally uniform derivative of
any complex norm-differentiable family of actual canonical normalized maps. -/
theorem normalizedSolution_complex_parameter_integral_firstVariation
    (μ : ℂ → MeasurableBeltramiBall) {t₀ : ℂ} {η : Ambient}
    (hμ : HasDerivAt (fun t => (μ t).val) η t₀) :
    TendstoLocallyUniformly
      (fun t w => (normalizedMap (μ (t₀ + t)) w - normalizedMap (μ t₀) w) / t)
      (fun w => -(1 / (Real.pi : ℂ)) * ∫ z,
        η z * normalizedMap (μ t₀) w * (normalizedMap (μ t₀) w - 1) *
            dz (normalizedMap (μ t₀)) z ^ 2 /
          (normalizedMap (μ t₀) z * (normalizedMap (μ t₀) z - 1) *
            (normalizedMap (μ t₀) z - normalizedMap (μ t₀) w))) (𝓝[≠] (0 : ℂ)) := by
  exact (normalizedSolution_complex_parameter_firstVariation μ hμ).congr_right
    (firstVariation_transport_eq_integral (μ t₀) η)

/-- The identical full-plane formula and locally uniform limit hold for every
real norm-differentiable family, with the same original coefficient derivative. -/
theorem normalizedSolution_real_parameter_integral_firstVariation
    (μ : ℝ → MeasurableBeltramiBall) {t₀ : ℝ} {η : Ambient}
    (hμ : HasDerivAt (fun t => (μ t).val) η t₀) :
    TendstoLocallyUniformly
      (fun t w => (normalizedMap (μ (t₀ + t)) w - normalizedMap (μ t₀) w) / (t : ℂ))
      (fun w => -(1 / (Real.pi : ℂ)) * ∫ z,
        η z * normalizedMap (μ t₀) w * (normalizedMap (μ t₀) w - 1) *
            dz (normalizedMap (μ t₀)) z ^ 2 /
          (normalizedMap (μ t₀) z * (normalizedMap (μ t₀) z - 1) *
            (normalizedMap (μ t₀) z - normalizedMap (μ t₀) w))) (𝓝[≠] (0 : ℝ)) := by
  exact (normalizedSolution_real_parameter_firstVariation μ hμ).congr_right
    (firstVariation_transport_eq_integral (μ t₀) η)

end LowDimensionalTopology.Geometry.Teichmuller.PlanarCoefficientTransport
