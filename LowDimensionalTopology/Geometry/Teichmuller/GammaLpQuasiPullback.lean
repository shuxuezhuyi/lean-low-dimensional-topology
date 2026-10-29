module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaLpOperators
public import LowDimensionalTopology.Geometry.Teichmuller.MeasurableBeltrami
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Quasi-measure-preserving pullback on the actual coefficient L-infinity space

Composition with a null-set-preserving measurable map is a genuine bounded
complex-linear map on the existing hyperbolic L-infinity classes. The norm
bound uses essential bounds and does not require finite area or preservation
of area. A measurable equivalence preserving the measure class in both
directions gives a linear isometry in the same original norm.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

/-- The actual representative pulled back by a quasi-measure-preserving map is bounded. -/
theorem quasiPullback_memLp (f : ℍ → ℍ)
    (hf : QuasiMeasurePreserving f volume volume) (μ : Ambient) :
    MemLp (fun z => μ (f z)) (⊤ : ℝ≥0∞) volume := by
  have hm : AEStronglyMeasurable (fun z : ℍ => μ (f z)) (volume : Measure ℍ) :=
    (Lp.aestronglyMeasurable μ).comp_quasiMeasurePreserving hf
  have hb : ∀ᵐ z : ℍ ∂volume, ‖μ (f z)‖ ≤ ‖μ‖ := by
    filter_upwards [hf.ae (lpInfinity_norm_ae_le μ)] with z hz
    exact hz
  exact memLp_top_of_bound hm ‖μ‖ hb

/-- Pull back the existing almost-everywhere class by actual composition. -/
def quasiPullbackValue (f : ℍ → ℍ)
    (hf : QuasiMeasurePreserving f volume volume) (μ : Ambient) : Ambient :=
  (quasiPullback_memLp f hf μ).toLp (fun z => μ (f z))

theorem quasiPullbackValue_coe_ae (f : ℍ → ℍ)
    (hf : QuasiMeasurePreserving f volume volume) (μ : Ambient) :
    quasiPullbackValue f hf μ =ᵐ[volume] fun z => μ (f z) :=
  (quasiPullback_memLp f hf μ).coeFn_toLp

/-- The pullback is linear on the actual coefficient classes. -/
def quasiPullbackLinear (f : ℍ → ℍ)
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
theorem norm_quasiPullbackValue_le (f : ℍ → ℍ)
    (hf : QuasiMeasurePreserving f volume volume) (μ : Ambient) :
    ‖quasiPullbackValue f hf μ‖ ≤ ‖μ‖ := by
  apply lpInfinity_norm_le_of_ae_bound _ (norm_nonneg μ)
  filter_upwards [quasiPullbackValue_coe_ae f hf μ,
    hf.ae (lpInfinity_norm_ae_le μ)] with z hz hb
  rw [hz]
  exact hb

/-- Pullback as a bounded complex-linear map in the original hyperbolic L-infinity norm. -/
def quasiPullback (f : ℍ → ℍ) (hf : QuasiMeasurePreserving f volume volume) :
    Ambient →L[ℂ] Ambient :=
  (quasiPullbackLinear f hf).mkContinuous 1 fun μ => by
    simp only [quasiPullbackLinear, LinearMap.coe_mk, AddHom.coe_mk, one_mul]
    exact norm_quasiPullbackValue_le f hf μ

@[simp] theorem quasiPullback_apply (f : ℍ → ℍ)
    (hf : QuasiMeasurePreserving f volume volume) (μ : Ambient) :
    quasiPullback f hf μ = quasiPullbackValue f hf μ := rfl

theorem quasiPullback_coe_ae (f : ℍ → ℍ)
    (hf : QuasiMeasurePreserving f volume volume) (μ : Ambient) :
    quasiPullback f hf μ =ᵐ[volume] fun z => μ (f z) :=
  quasiPullbackValue_coe_ae f hf μ

theorem norm_quasiPullback_le (f : ℍ → ℍ)
    (hf : QuasiMeasurePreserving f volume volume) (μ : Ambient) :
    ‖quasiPullback f hf μ‖ ≤ ‖μ‖ :=
  norm_quasiPullbackValue_le f hf μ

/-- The identity has its original action on every actual coefficient class. -/
theorem quasiPullback_id (μ : Ambient) : quasiPullback id (.id volume) μ = μ := by
  apply Lp.ext
  exact quasiPullback_coe_ae id (.id volume) μ

/-- Pullback composition retains the literal order of composition of functions. -/
theorem quasiPullback_comp (f g : ℍ → ℍ)
    (hf : QuasiMeasurePreserving f volume volume)
    (hg : QuasiMeasurePreserving g volume volume) (μ : Ambient) :
    quasiPullback f hf (quasiPullback g hg μ) =
      quasiPullback (g ∘ f) (hg.comp hf) μ := by
  apply Lp.ext
  filter_upwards [quasiPullback_coe_ae f hf (quasiPullback g hg μ),
    hf.ae (quasiPullback_coe_ae g hg μ),
    quasiPullback_coe_ae (g ∘ f) (hg.comp hf) μ] with z houter hinner hcomp
  rw [houter, hinner, hcomp]
  rfl

/-- Inverse measurable maps cancel on the genuine almost-everywhere classes. -/
theorem quasiPullback_symm_apply (e : ℍ ≃ ℍ)
    (he : QuasiMeasurePreserving e volume volume)
    (hinv : QuasiMeasurePreserving e.symm volume volume) (μ : Ambient) :
    quasiPullback e.symm hinv (quasiPullback e he μ) = μ := by
  apply Lp.ext
  filter_upwards [quasiPullback_coe_ae e.symm hinv (quasiPullback e he μ),
    hinv.ae (quasiPullback_coe_ae e he μ)] with z houter hinner
  rw [houter, hinner, e.apply_symm_apply]

/-- The other inverse identity uses the same actual functions. -/
theorem quasiPullback_apply_symm (e : ℍ ≃ ℍ)
    (he : QuasiMeasurePreserving e volume volume)
    (hinv : QuasiMeasurePreserving e.symm volume volume) (μ : Ambient) :
    quasiPullback e he (quasiPullback e.symm hinv μ) = μ := by
  apply Lp.ext
  filter_upwards [quasiPullback_coe_ae e he (quasiPullback e.symm hinv μ),
    he.ae (quasiPullback_coe_ae e.symm hinv μ)] with z houter hinner
  rw [houter, hinner, e.symm_apply_apply]

/-- A measure-class equivalence induces a genuine continuous complex-linear equivalence. -/
def quasiPullbackEquiv (e : ℍ ≃ ℍ)
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
theorem norm_quasiPullback_eq (e : ℍ ≃ ℍ)
    (he : QuasiMeasurePreserving e volume volume)
    (hinv : QuasiMeasurePreserving e.symm volume volume) (μ : Ambient) :
    ‖quasiPullback e he μ‖ = ‖μ‖ := by
  apply le_antisymm (norm_quasiPullback_le e he μ)
  calc
    ‖μ‖ = ‖quasiPullback e.symm hinv (quasiPullback e he μ)‖ := by
      rw [quasiPullback_symm_apply]
    _ ≤ ‖quasiPullback e he μ‖ := norm_quasiPullback_le e.symm hinv _

end LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
