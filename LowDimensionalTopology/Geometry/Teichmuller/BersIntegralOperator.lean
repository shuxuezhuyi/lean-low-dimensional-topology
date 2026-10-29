module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedBersTarget
public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The actual Bers integral as a bounded complex linear operator

The coefficient is the original compatible L-infinity almost-everywhere class.
Its planar representative enters the literal integral kernel. Absolute kernel
integrability and the exact kernel-area integral prove a uniform weighted norm
bound; the integral identities prove actual complex linearity.

The analytic kernel formulas are from Wu Xiaobin's Li-Zhong-QC-formalization,
commit `1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0),
`S36_Hamilton.lean`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

open LiZhongQC

/-- The actual finite kernel constant, without needing a separately simplified
formula for the area of the complex unit ball. -/
def kernelConstant : ℝ :=
  ‖(6 / Real.pi : ℂ)‖ * (volume (Metric.ball (0 : ℂ) 1)).toReal / 4

theorem kernelConstant_nonneg : 0 ≤ kernelConstant := by
  unfold kernelConstant
  positivity

private theorem fourthKernel_integrable {z : ℂ} (hz : z ∈ lowerHalf) :
    IntegrableOn (fun ζ : ℂ => 1 / (ζ - z) ^ 4) upperHalf := by
  have he : (fun ζ : ℂ => 1 / ((ζ - z) ^ 3 * (ζ - z))) =
      fun ζ : ℂ => 1 / (ζ - z) ^ 4 := by
    funext ζ
    congr 1
  have h := h36p_kernel_L1 hz hz
  rw [he] at h
  refine ⟨h.1.continuousOn.aestronglyMeasurable isOpen_upperHalf.measurableSet, ?_⟩
  simpa only [phiArea, HasFiniteIntegral, ofReal_norm] using h.2

private theorem fourthKernel_norm_integrable {z : ℂ} (hz : z ∈ lowerHalf) :
    IntegrableOn (fun ζ : ℂ => ‖ζ - z‖⁻¹ ^ 4) upperHalf := by
  unfold IntegrableOn
  simpa only [one_div, norm_inv, norm_pow, inv_pow] using
    (fourthKernel_integrable hz).norm

private theorem fourthKernel_norm_integral {z : ℂ} (hz : z ∈ lowerHalf) :
    (∫ ζ in upperHalf, ‖ζ - z‖⁻¹ ^ 4) =
      (volume (Metric.ball (0 : ℂ) 1)).toReal * (4 * z.im ^ 2)⁻¹ := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ζ => by positivity)
    (fourthKernel_norm_integrable hz).aestronglyMeasurable,
    h36p_c_kernel_area hz, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]

/-- Every genuinely bounded measurable input gives an absolutely integrable
fourth kernel on the upper half-plane. -/
theorem fourthKernel_mul_integrable {κ : ℂ → ℂ}
    (hm : AEStronglyMeasurable κ (volume.restrict upperHalf))
    {M : ℝ} (hb : ∀ᵐ ζ ∂(volume.restrict upperHalf), ‖κ ζ‖ ≤ M)
    {z : ℂ} (hz : z ∈ lowerHalf) :
    IntegrableOn (fun ζ : ℂ => κ ζ / (ζ - z) ^ 4) upperHalf := by
  unfold IntegrableOn
  simpa only [div_eq_mul_inv, one_div, one_mul] using
    (fourthKernel_integrable hz).bdd_mul hm hb

/-- The literal integral has a uniform square-height bound depending only on
the actual a.e. bound of the coefficient. -/
theorem bersDerivative_weighted_bound {κ : ℂ → ℂ}
    {M : ℝ} (hb : ∀ᵐ ζ ∂(volume.restrict upperHalf), ‖κ ζ‖ ≤ M)
    {z : ℂ} (hz : z ∈ lowerHalf) :
    ‖bersDerivative κ z‖ * z.im ^ 2 ≤ kernelConstant * M := by
  have hbound : ∀ᵐ ζ ∂(volume.restrict upperHalf),
      ‖κ ζ / (ζ - z) ^ 4‖ ≤ M * (‖ζ - z‖⁻¹ ^ 4) := by
    filter_upwards [hb] with ζ hζ
    rw [norm_div, norm_pow]
    calc
      ‖κ ζ‖ / ‖ζ - z‖ ^ 4 ≤ M / ‖ζ - z‖ ^ 4 :=
        div_le_div_of_nonneg_right hζ (by positivity)
      _ = M * (‖ζ - z‖⁻¹ ^ 4) := by rw [div_eq_mul_inv, inv_pow]
  have hi := norm_integral_le_of_norm_le
    ((fourthKernel_norm_integrable hz).const_mul M) hbound
  rw [integral_const_mul, fourthKernel_norm_integral hz] at hi
  have hy : z.im ≠ 0 := ne_of_lt (show z.im < 0 from hz)
  calc
    ‖bersDerivative κ z‖ * z.im ^ 2 =
        (‖(6 / Real.pi : ℂ)‖ * ‖∫ ζ in upperHalf, κ ζ / (ζ - z) ^ 4‖) * z.im ^ 2 := by
      rw [bersDerivative, norm_mul, norm_neg]
    _ ≤ (‖(6 / Real.pi : ℂ)‖ *
        (M * ((volume (Metric.ball (0 : ℂ) 1)).toReal * (4 * z.im ^ 2)⁻¹))) * z.im ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hi (norm_nonneg _)) (sq_nonneg _)
    _ = kernelConstant * M := by
      unfold kernelConstant
      field_simp [hy]

/-- Representative changes on a null set preserve the actual kernel integral. -/
theorem bersDerivative_congr_ae {κ η : ℂ → ℂ}
    (h : κ =ᵐ[volume.restrict upperHalf] η) (z : ℂ) :
    bersDerivative κ z = bersDerivative η z := by
  unfold bersDerivative
  apply congrArg (fun a : ℂ => -(6 / Real.pi : ℂ) * a)
  exact integral_congr_ae (h.mono fun ζ hζ => congrArg (fun a : ℂ => a / (ζ - z) ^ 4) hζ)

private theorem bersDerivative_add {κ η : ℂ → ℂ}
    (hκ : AEStronglyMeasurable κ (volume.restrict upperHalf))
    (hη : AEStronglyMeasurable η (volume.restrict upperHalf))
    {M N : ℝ} (hM : ∀ᵐ ζ ∂(volume.restrict upperHalf), ‖κ ζ‖ ≤ M)
    (hN : ∀ᵐ ζ ∂(volume.restrict upperHalf), ‖η ζ‖ ≤ N)
    {z : ℂ} (hz : z ∈ lowerHalf) :
    bersDerivative (fun ζ => κ ζ + η ζ) z = bersDerivative κ z + bersDerivative η z := by
  unfold bersDerivative
  have he : (fun ζ => (κ ζ + η ζ) / (ζ - z) ^ 4) =
      fun ζ => κ ζ / (ζ - z) ^ 4 + η ζ / (ζ - z) ^ 4 := by
    funext ζ
    ring
  rw [he, integral_add (fourthKernel_mul_integrable hκ hM hz)
    (fourthKernel_mul_integrable hη hN hz)]
  ring

private theorem bersDerivative_const_mul (c : ℂ) (κ : ℂ → ℂ) (z : ℂ) :
    bersDerivative (fun ζ => c * κ ζ) z = c * bersDerivative κ z := by
  unfold bersDerivative
  have he : (fun ζ => c * κ ζ / (ζ - z) ^ 4) =
      fun ζ => c * (κ ζ / (ζ - z) ^ 4) := by
    funext ζ
    ring
  rw [he, integral_const_mul]
  ring

/-- The genuine pointwise fourth-kernel operator in the weighted norm space. -/
def integralValue {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (μ : GammaMeasurableBeltrami.Space Γ) : Target :=
  encode (bersDerivative (GammaMeasurableBeltrami.planeRepresentative μ.val))
    ⟨kernelConstant * ‖μ‖, fun _ hz => bersDerivative_weighted_bound
      (GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff μ.val).2 hz⟩

@[simp] theorem integralValue_apply {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (μ : GammaMeasurableBeltrami.Space Γ) (z : Lower) :
    integralValue μ z =
      bersDerivative (GammaMeasurableBeltrami.planeRepresentative μ.val) z * weight z := rfl

/-- The actual ambient a.e. addition law transports to the planar representatives. -/
theorem planeRepresentative_add_ae {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (μ ν : GammaMeasurableBeltrami.Space Γ) :
    GammaMeasurableBeltrami.planeRepresentative (μ + ν).val =ᵐ[volume.restrict upperHalf]
      fun ζ => GammaMeasurableBeltrami.planeRepresentative μ.val ζ +
        GammaMeasurableBeltrami.planeRepresentative ν.val ζ := by
  have hadd : (μ + ν).val = μ.val + ν.val :=
    AddMemClass.coe_add (GammaMeasurableBeltrami.compatibleClosedSubmodule Γ) μ ν
  apply GammaMeasurableBeltrami.ae_plane_iff.2
  filter_upwards [Lp.coeFn_add μ.val ν.val] with z hz
  simpa only [GammaMeasurableBeltrami.planeRepresentative_coe, hadd, Pi.add_apply] using hz

private def integralLinearMap (Γ : Subgroup GammaMeasurableBeltrami.Deck) :
    GammaMeasurableBeltrami.Space Γ →ₗ[ℂ] Target where
  toFun := integralValue
  map_add' μ ν := by
    apply lp.ext
    funext z
    simp only [lp.coeFn_add, Pi.add_apply]
    change integralValue (μ + ν) z = integralValue μ z + integralValue ν z
    rw [integralValue_apply, integralValue_apply, integralValue_apply,
      bersDerivative_congr_ae (planeRepresentative_add_ae μ ν),
      bersDerivative_add
        (GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff μ.val).1
        (GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff ν.val).1
        (GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff μ.val).2
        (GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff ν.val).2 z.property]
    ring
  map_smul' c μ := by
    apply lp.ext
    funext z
    simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    change integralValue (c • μ) z = c * integralValue μ z
    have hsmul : (c • μ).val = c • μ.val :=
      SetLike.val_smul (GammaMeasurableBeltrami.compatibleClosedSubmodule Γ) c μ
    have hae : GammaMeasurableBeltrami.planeRepresentative (c • μ.val)
        =ᵐ[volume.restrict upperHalf]
        (fun ζ => c * GammaMeasurableBeltrami.planeRepresentative μ.val ζ) := by
      filter_upwards [GammaMeasurableBeltrami.planeRepresentative_smul_ae c μ.val]
        with ζ hζ
      simpa only [Pi.smul_apply, smul_eq_mul] using hζ
    rw [integralValue_apply, integralValue_apply, hsmul,
      bersDerivative_congr_ae hae, bersDerivative_const_mul]
    ring

/-- The fourth-kernel formula defines an actual bounded complex linear map on
all compatible measurable directions, with their original L-infinity norm. -/
@[no_expose] def integralOperator (Γ : Subgroup GammaMeasurableBeltrami.Deck) :
    GammaMeasurableBeltrami.Space Γ →L[ℂ] Target :=
  (integralLinearMap Γ).mkContinuous kernelConstant fun μ => by
    change ‖integralValue μ‖ ≤ kernelConstant * ‖μ‖
    apply lp.norm_le_of_forall_le (mul_nonneg kernelConstant_nonneg (norm_nonneg μ))
    intro z
    have hbound := bersDerivative_weighted_bound
      (GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff μ.val).2 z.property
    rw [ClosedSubmodule.norm_coe μ] at hbound
    simpa only [integralValue_apply, norm_mul, weight, Complex.norm_real,
      Real.norm_eq_abs, abs_sq] using hbound

@[simp] theorem integralOperator_apply {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (μ : GammaMeasurableBeltrami.Space Γ) (z : Lower) :
    integralOperator Γ μ z =
      bersDerivative (GammaMeasurableBeltrami.planeRepresentative μ.val) z * weight z := by
  simp only [integralOperator, LinearMap.mkContinuous_apply, integralLinearMap]
  exact integralValue_apply μ z

/-- Its actual linear kernel is detected pointwise on the original lower half-plane. -/
theorem integralOperator_eq_zero_iff {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (μ : GammaMeasurableBeltrami.Space Γ) :
    integralOperator Γ μ = 0 ↔
      ∀ z ∈ lowerHalf,
        bersDerivative (GammaMeasurableBeltrami.planeRepresentative μ.val) z = 0 := by
  constructor
  · intro h z hz
    have he := congrArg (fun f : Target => f ⟨z, hz⟩) h
    change bersDerivative (GammaMeasurableBeltrami.planeRepresentative μ.val) z *
      weight ⟨z, hz⟩ = 0 at he
    exact (mul_eq_zero.mp he).resolve_right (weight_ne_zero ⟨z, hz⟩)
  · intro h
    apply lp.ext
    funext z
    change bersDerivative (GammaMeasurableBeltrami.planeRepresentative μ.val) z * weight z = 0
    rw [h z z.property, zero_mul]

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
