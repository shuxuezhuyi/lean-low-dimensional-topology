module

public import LowDimensionalTopology.Geometry.Teichmuller.MeasurableBeltrami
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Full planar coefficient composition and bounded multiplication

The ambient space is the entire original planar L-infinity space of genuine
almost-everywhere classes. A fixed null-set-preserving measurable map acts by
actual composition; its essential norm bound requires no area preservation.
Both directions of an actual measurable equivalence give an isometry.
Multiplication uses a literal measurable function and its proved essential bound.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.PlanarCoefficientTransport

/-- The unchanged full planar measurable coefficient Banach space. -/
abbrev Ambient := MeasurableBeltramiSpace

/-- The actual representative pulled back by a quasi-measure-preserving map is bounded. -/
theorem quasiPullback_memLp (f : ℂ → ℂ)
    (hf : QuasiMeasurePreserving f volume volume) (μ : Ambient) :
    MemLp (fun z => μ (f z)) (⊤ : ℝ≥0∞) volume := by
  have hm : AEStronglyMeasurable (fun z : ℂ => μ (f z)) (volume : Measure ℂ) :=
    (Lp.aestronglyMeasurable μ).comp_quasiMeasurePreserving hf
  have hb : ∀ᵐ z : ℂ ∂volume, ‖μ (f z)‖ ≤ ‖μ‖ := by
    filter_upwards [hf.ae (lpInfinity_norm_ae_le μ)] with z hz
    exact hz
  exact memLp_top_of_bound hm ‖μ‖ hb

/-- Pull back the existing almost-everywhere class by actual composition. -/
def quasiPullbackValue (f : ℂ → ℂ)
    (hf : QuasiMeasurePreserving f volume volume) (μ : Ambient) : Ambient :=
  (quasiPullback_memLp f hf μ).toLp (fun z => μ (f z))

theorem quasiPullbackValue_coe_ae (f : ℂ → ℂ)
    (hf : QuasiMeasurePreserving f volume volume) (μ : Ambient) :
    quasiPullbackValue f hf μ =ᵐ[volume] fun z => μ (f z) :=
  (quasiPullback_memLp f hf μ).coeFn_toLp

/-- The pullback is linear on the actual coefficient classes. -/
def quasiPullbackLinear (f : ℂ → ℂ)
    (hf : QuasiMeasurePreserving f volume volume) : Ambient →ₗ[ℂ] Ambient where
  toFun := quasiPullbackValue f hf
  map_add' μ ν := by
    apply Lp.ext
    filter_upwards [quasiPullbackValue_coe_ae f hf (μ + ν),
      quasiPullbackValue_coe_ae f hf μ, quasiPullbackValue_coe_ae f hf ν,
      hf.ae (Lp.coeFn_add μ ν),
      Lp.coeFn_add (quasiPullbackValue f hf μ) (quasiPullbackValue f hf ν)]
      with z hsum hμ hν hin hout
    simp only [Pi.add_apply] at hin hout
    rw [hsum, hout, hin, hμ, hν]
  map_smul' c μ := by
    apply Lp.ext
    filter_upwards [quasiPullbackValue_coe_ae f hf (c • μ),
      quasiPullbackValue_coe_ae f hf μ, hf.ae (Lp.coeFn_smul c μ),
      Lp.coeFn_smul c (quasiPullbackValue f hf μ)] with z hsmul hμ hin hout
    simp only [Pi.smul_apply, smul_eq_mul] at hin hout
    change quasiPullbackValue f hf (c • μ) z = (c • quasiPullbackValue f hf μ) z
    rw [hsmul, hout, hin, hμ]

/-- Quasi-measure-preserving composition cannot increase the essential supremum. -/
theorem norm_quasiPullbackValue_le (f : ℂ → ℂ)
    (hf : QuasiMeasurePreserving f volume volume) (μ : Ambient) :
    ‖quasiPullbackValue f hf μ‖ ≤ ‖μ‖ := by
  apply lpInfinity_norm_le_of_ae_bound _ (norm_nonneg μ)
  filter_upwards [quasiPullbackValue_coe_ae f hf μ,
    hf.ae (lpInfinity_norm_ae_le μ)] with z hz hb
  rw [hz]
  exact hb

/-- Pullback as a bounded complex-linear map in the original planar L-infinity norm. -/
def quasiPullback (f : ℂ → ℂ) (hf : QuasiMeasurePreserving f volume volume) :
    Ambient →L[ℂ] Ambient :=
  (quasiPullbackLinear f hf).mkContinuous 1 fun μ => by
    simp only [quasiPullbackLinear, LinearMap.coe_mk, AddHom.coe_mk, one_mul]
    exact norm_quasiPullbackValue_le f hf μ

@[simp] theorem quasiPullback_apply (f : ℂ → ℂ)
    (hf : QuasiMeasurePreserving f volume volume) (μ : Ambient) :
    quasiPullback f hf μ = quasiPullbackValue f hf μ := rfl

theorem quasiPullback_coe_ae (f : ℂ → ℂ)
    (hf : QuasiMeasurePreserving f volume volume) (μ : Ambient) :
    quasiPullback f hf μ =ᵐ[volume] fun z => μ (f z) :=
  quasiPullbackValue_coe_ae f hf μ

theorem norm_quasiPullback_le (f : ℂ → ℂ)
    (hf : QuasiMeasurePreserving f volume volume) (μ : Ambient) :
    ‖quasiPullback f hf μ‖ ≤ ‖μ‖ :=
  norm_quasiPullbackValue_le f hf μ

/-- Inverse measurable maps cancel on the genuine almost-everywhere classes. -/
theorem quasiPullback_symm_apply (e : ℂ ≃ ℂ)
    (he : QuasiMeasurePreserving e volume volume)
    (hinv : QuasiMeasurePreserving e.symm volume volume) (μ : Ambient) :
    quasiPullback e.symm hinv (quasiPullback e he μ) = μ := by
  apply Lp.ext
  filter_upwards [quasiPullback_coe_ae e.symm hinv (quasiPullback e he μ),
    hinv.ae (quasiPullback_coe_ae e he μ)] with z houter hinner
  rw [houter, hinner, e.apply_symm_apply]

/-- The other inverse identity uses the same actual functions. -/
theorem quasiPullback_apply_symm (e : ℂ ≃ ℂ)
    (he : QuasiMeasurePreserving e volume volume)
    (hinv : QuasiMeasurePreserving e.symm volume volume) (μ : Ambient) :
    quasiPullback e he (quasiPullback e.symm hinv μ) = μ := by
  apply Lp.ext
  filter_upwards [quasiPullback_coe_ae e he (quasiPullback e.symm hinv μ),
    he.ae (quasiPullback_coe_ae e.symm hinv μ)] with z houter hinner
  rw [houter, hinner, e.symm_apply_apply]

/-- A measure-class equivalence induces a genuine continuous complex-linear equivalence. -/
def quasiPullbackEquiv (e : ℂ ≃ ℂ)
    (he : QuasiMeasurePreserving e volume volume)
    (hinv : QuasiMeasurePreserving e.symm volume volume) : Ambient ≃L[ℂ] Ambient where
  toLinearEquiv :=
    { (quasiPullback e he).toLinearMap with
      invFun := quasiPullback e.symm hinv
      left_inv := quasiPullback_symm_apply e he hinv
      right_inv := quasiPullback_apply_symm e he hinv }
  continuous_toFun := (quasiPullback e he).continuous
  continuous_invFun := (quasiPullback e.symm hinv).continuous

/-- Both null-set-preserving directions give equality of the original essential norms. -/
theorem norm_quasiPullback_eq (e : ℂ ≃ ℂ)
    (he : QuasiMeasurePreserving e volume volume)
    (hinv : QuasiMeasurePreserving e.symm volume volume) (μ : Ambient) :
    ‖quasiPullback e he μ‖ = ‖μ‖ := by
  apply le_antisymm (norm_quasiPullback_le e he μ)
  calc
    ‖μ‖ = ‖quasiPullback e.symm hinv (quasiPullback e he μ)‖ := by
      rw [quasiPullback_symm_apply]
    _ ≤ ‖quasiPullback e he μ‖ := norm_quasiPullback_le e.symm hinv _

/-- The literal product is an actual L-infinity coefficient. -/
theorem boundedMultiply_memLp (a : ℂ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℂ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) (μ : Ambient) :
    MemLp (fun z => a z * μ z) (⊤ : ℝ≥0∞) volume := by
  apply memLp_top_of_bound (ha.mul (Lp.aestronglyMeasurable μ)) (C * ‖μ‖)
  filter_upwards [hbound, lpInfinity_norm_ae_le μ] with z haz hμz
  change ‖a z * μ z‖ ≤ C * ‖μ‖
  rw [norm_mul]
  exact mul_le_mul haz hμz (norm_nonneg _) hC

/-- The actual almost-everywhere class of multiplication by the given function. -/
def boundedMultiplyValue (a : ℂ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℂ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) (μ : Ambient) : Ambient :=
  (boundedMultiply_memLp a ha hC hbound μ).toLp (fun z => a z * μ z)

theorem boundedMultiplyValue_coe_ae (a : ℂ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℂ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) (μ : Ambient) :
    boundedMultiplyValue a ha hC hbound μ =ᵐ[volume] fun z => a z * μ z :=
  (boundedMultiply_memLp a ha hC hbound μ).coeFn_toLp

/-- Multiplication by the literal coefficient is linear on the actual classes. -/
def boundedMultiplyLinear (a : ℂ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℂ))
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
    exact mul_left_comm _ _ _

/-- The quantitative norm estimate uses the unchanged essential norm. -/
theorem norm_boundedMultiplyValue_le (a : ℂ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℂ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) (μ : Ambient) :
    ‖boundedMultiplyValue a ha hC hbound μ‖ ≤ C * ‖μ‖ := by
  apply lpInfinity_norm_le_of_ae_bound _ (mul_nonneg hC (norm_nonneg μ))
  filter_upwards [boundedMultiplyValue_coe_ae a ha hC hbound μ,
    hbound, lpInfinity_norm_ae_le μ] with z hz haz hμz
  rw [hz, norm_mul]
  exact mul_le_mul haz hμz (norm_nonneg _) hC

/-- The actual bounded multiplier as a continuous complex-linear map. -/
def boundedMultiply (a : ℂ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℂ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) :
    Ambient →L[ℂ] Ambient :=
  (boundedMultiplyLinear a ha hC hbound).mkContinuous C
    (norm_boundedMultiplyValue_le a ha hC hbound)

@[simp] theorem boundedMultiply_apply (a : ℂ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℂ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) (μ : Ambient) :
    boundedMultiply a ha hC hbound μ = boundedMultiplyValue a ha hC hbound μ := rfl

theorem boundedMultiply_coe_ae (a : ℂ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℂ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) (μ : Ambient) :
    boundedMultiply a ha hC hbound μ =ᵐ[volume] fun z => a z * μ z :=
  boundedMultiplyValue_coe_ae a ha hC hbound μ

theorem norm_boundedMultiply_le (a : ℂ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℂ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) (μ : Ambient) :
    ‖boundedMultiply a ha hC hbound μ‖ ≤ C * ‖μ‖ :=
  norm_boundedMultiplyValue_le a ha hC hbound μ

end LowDimensionalTopology.Geometry.Teichmuller.PlanarCoefficientTransport
