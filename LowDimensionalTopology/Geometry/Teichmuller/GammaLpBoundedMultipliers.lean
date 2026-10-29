module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaLpOperators
public import LowDimensionalTopology.Geometry.Teichmuller.MeasurableBeltrami

/-!
# Bounded measurable multipliers on the actual coefficient L-infinity space

Multiplication by a fixed actual measurable coefficient is complex-linear and
bounded in the existing hyperbolic essential supremum norm. Both measurability
and its quantitative bound are proved hypotheses about that literal function;
no operator, norm, or derivative is supplied as additional data.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

/-- The literal product is an actual L-infinity coefficient. -/
theorem boundedMultiply_memLp (a : ℍ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℍ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) (μ : Ambient) :
    MemLp (fun z => a z * μ z) (⊤ : ℝ≥0∞) volume := by
  apply memLp_top_of_bound (ha.mul (Lp.aestronglyMeasurable μ)) (C * ‖μ‖)
  filter_upwards [hbound, lpInfinity_norm_ae_le μ] with z haz hμz
  change ‖a z * μ z‖ ≤ C * ‖μ‖
  rw [norm_mul]
  exact mul_le_mul haz hμz (norm_nonneg _) hC

/-- The actual almost-everywhere class of multiplication by the given function. -/
def boundedMultiplyValue (a : ℍ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℍ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) (μ : Ambient) : Ambient :=
  (boundedMultiply_memLp a ha hC hbound μ).toLp (fun z => a z * μ z)

theorem boundedMultiplyValue_coe_ae (a : ℍ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℍ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) (μ : Ambient) :
    boundedMultiplyValue a ha hC hbound μ =ᵐ[volume] fun z => a z * μ z :=
  (boundedMultiply_memLp a ha hC hbound μ).coeFn_toLp

/-- Multiplication by the literal coefficient is linear on the actual classes. -/
def boundedMultiplyLinear (a : ℍ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℍ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) :
    Ambient →ₗ[ℂ] Ambient where
  toFun := boundedMultiplyValue a ha hC hbound
  map_add' μ ν := by
    apply Lp.ext
    filter_upwards [boundedMultiplyValue_coe_ae a ha hC hbound (μ + ν),
      boundedMultiplyValue_coe_ae a ha hC hbound μ,
      boundedMultiplyValue_coe_ae a ha hC hbound ν,
      Lp.coeFn_add μ ν,
      Lp.coeFn_add (boundedMultiplyValue a ha hC hbound μ)
        (boundedMultiplyValue a ha hC hbound ν)] with z hsum hμ hν hin hout
    simp only [Pi.add_apply] at hin hout
    rw [hsum, hout, hin, hμ, hν]
    exact mul_add _ _ _
  map_smul' c μ := by
    apply Lp.ext
    filter_upwards [boundedMultiplyValue_coe_ae a ha hC hbound (c • μ),
      boundedMultiplyValue_coe_ae a ha hC hbound μ, Lp.coeFn_smul c μ,
      Lp.coeFn_smul c (boundedMultiplyValue a ha hC hbound μ)] with z hsmul hμ hin hout
    simp only [Pi.smul_apply, smul_eq_mul] at hin hout
    change boundedMultiplyValue a ha hC hbound (c • μ) z =
      (c • boundedMultiplyValue a ha hC hbound μ) z
    rw [hsmul, hout, hin, hμ]
    ring

/-- The quantitative norm estimate uses the unchanged essential norm. -/
theorem norm_boundedMultiplyValue_le (a : ℍ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℍ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) (μ : Ambient) :
    ‖boundedMultiplyValue a ha hC hbound μ‖ ≤ C * ‖μ‖ := by
  apply lpInfinity_norm_le_of_ae_bound _ (mul_nonneg hC (norm_nonneg μ))
  filter_upwards [boundedMultiplyValue_coe_ae a ha hC hbound μ,
    hbound, lpInfinity_norm_ae_le μ] with z hz haz hμz
  rw [hz, norm_mul]
  exact mul_le_mul haz hμz (norm_nonneg _) hC

/-- The actual bounded multiplier as a continuous complex-linear map. -/
def boundedMultiply (a : ℍ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℍ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) :
    Ambient →L[ℂ] Ambient :=
  (boundedMultiplyLinear a ha hC hbound).mkContinuous C
    (norm_boundedMultiplyValue_le a ha hC hbound)

@[simp] theorem boundedMultiply_apply (a : ℍ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℍ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) (μ : Ambient) :
    boundedMultiply a ha hC hbound μ = boundedMultiplyValue a ha hC hbound μ := rfl

theorem boundedMultiply_coe_ae (a : ℍ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℍ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) (μ : Ambient) :
    boundedMultiply a ha hC hbound μ =ᵐ[volume] fun z => a z * μ z :=
  boundedMultiplyValue_coe_ae a ha hC hbound μ

theorem norm_boundedMultiply_le (a : ℍ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℍ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) (μ : Ambient) :
    ‖boundedMultiply a ha hC hbound μ‖ ≤ C * ‖μ‖ :=
  norm_boundedMultiplyValue_le a ha hC hbound μ

/-- Altering the multiplier on a null set leaves the actual class operator unchanged. -/
theorem boundedMultiply_congr_ae (a b : ℍ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℍ))
    (hb : AEStronglyMeasurable b (volume : Measure ℍ))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) (hbound' : ∀ᵐ z ∂volume, ‖b z‖ ≤ D)
    (hab : a =ᵐ[volume] b) (μ : Ambient) :
    boundedMultiply a ha hC hbound μ = boundedMultiply b hb hD hbound' μ := by
  apply Lp.ext
  filter_upwards [boundedMultiply_coe_ae a ha hC hbound μ,
    boundedMultiply_coe_ae b hb hD hbound' μ, hab] with z haz hbz heq
  rw [haz, hbz, heq]

end LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
