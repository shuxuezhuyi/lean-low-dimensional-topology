module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.Tactic.FieldSimp

/-!
# Weighted measurable quadratic coefficients and genuine Beltrami classes

The conjugate square-height map retains every measurable automorphic input,
its actual essential norm, and its coefficient almost everywhere. No
holomorphy or subunit restriction is imposed on the original function.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter MeasureTheory
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.MeasurableQuadratic

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck} (f : ℍ → ℂ)

/-- The literal weighted quadratic coefficient. -/
def weightedValue (z : ℍ) : ℂ := (z.im : ℂ) ^ 2 * f z

/-- The conjugate weighted coefficient in the Beltrami tensor convention. -/
def beltramiValue : ℍ → ℂ := star (weightedValue f)

/-- The original weighted essential norm for Euclidean half-plane area. -/
def weightedEssNorm : ℝ := (eLpNorm (weightedValue f) ⊤ flatMeasure).toReal

theorem beltramiValue_apply (z : ℍ) :
    beltramiValue f z = (z.im : ℂ) ^ 2 * conj (f z) := by
  change conj ((z.im : ℂ) ^ 2 * f z) = _
  rw [map_mul, map_pow, Complex.conj_ofReal]

theorem norm_beltramiValue (z : ℍ) :
    ‖beltramiValue f z‖ = ‖f z‖ * z.im ^ 2 := by
  rw [beltramiValue_apply, norm_mul, norm_pow, Complex.norm_conj,
    Complex.norm_of_nonneg z.im_pos.le]
  ring

theorem beltramiValue_aestronglyMeasurable
    (hf : AEStronglyMeasurable f flatMeasure) :
    AEStronglyMeasurable (beltramiValue f) flatMeasure := by
  have hc := (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow 2
  have hw : AEStronglyMeasurable (weightedValue f) flatMeasure := hc.aestronglyMeasurable.mul hf
  exact hw.star

theorem beltramiValue_memLp (hf : AEStronglyMeasurable f flatMeasure)
    (hb : ∃ M : ℝ, ∀ᵐ z ∂flatMeasure, ‖f z‖ * z.im ^ 2 ≤ M) :
    MemLp (beltramiValue f) ⊤ (volume : Measure ℍ) := by
  obtain ⟨M, hM⟩ := hb
  apply memLp_top_of_bound
    ((beltramiValue_aestronglyMeasurable f hf).mono_ac
      (withDensity_absolutelyContinuous flatMeasure hyperbolicDensity)) M
  exact ae_hyperbolic_iff.mpr (hM.mono fun z hz => by
    simpa only [norm_beltramiValue] using hz)

theorem beltramiValue_compatible
    (ha : ∀ γ ∈ Γ, ∀ z : ℍ, f (γ • z) / denominator γ z ^ 4 = f z)
    (γ : Deck) (hγ : γ ∈ Γ) (z : ℍ) :
    beltramiValue f z = phase γ z * beltramiValue f (γ • z) := by
  have hd := denominator_ne_zero γ z
  have hcd : conj (denominator γ z) ≠ 0 := by
    intro h
    apply hd
    simpa only [Complex.conj_conj, map_zero] using congrArg conj h
  have hval := (div_eq_iff (pow_ne_zero 4 hd)).mp (ha γ hγ z)
  have him : (γ • z : ℍ).im = z.im / Complex.normSq (denominator γ z) := by
    simp [MulAction.compHom_smul_def, UpperHalfPlane.im_smul_eq_div_normSq,
      Matrix.SpecialLinearGroup.det_mapGL, UpperHalfPlane.denom, denominator]
  have himc : ((γ • z : ℍ).im : ℂ) =
      (z.im : ℂ) / (denominator γ z * conj (denominator γ z)) := by
    rw [Complex.mul_conj]
    exact_mod_cast him
  rw [beltramiValue_apply, beltramiValue_apply, phase, himc, hval]
  simp only [map_mul, map_pow]
  field_simp [hd, hcd]

variable (hf : AEStronglyMeasurable f flatMeasure)
    (ha : ∀ γ ∈ Γ, ∀ z : ℍ, f (γ • z) / denominator γ z ^ 4 = f z)
    (hb : ∃ M : ℝ, ∀ᵐ z ∂flatMeasure, ‖f z‖ * z.im ^ 2 ≤ M)

/-- Every original measurable weighted-bounded automorphic coefficient gives
its actual compatible L-infinity class. -/
def toBeltrami : Space Γ := by
  let μ : Ambient := (beltramiValue_memLp f hf hb).toLp (beltramiValue f)
  refine ⟨μ, (mem_compatibleSubmodule_iff μ).mpr ?_⟩
  intro γ hγ
  have hμ : μ =ᵐ[volume] beltramiValue f := (beltramiValue_memLp f hf hb).coeFn_toLp
  have hcomp := (measurePreserving_deck γ).quasiMeasurePreserving.ae_eq_comp hμ
  filter_upwards [hμ, hcomp] with z hz hγz
  change μ (γ • z) = beltramiValue f (γ • z) at hγz
  rw [hz, hγz]
  exact beltramiValue_compatible f ha γ hγ z

theorem toBeltrami_coe_ae :
    (toBeltrami f hf ha hb).val =ᵐ[volume] beltramiValue f :=
  (beltramiValue_memLp f hf hb).coeFn_toLp

/-- The inverse square-height formula recovers the entire original input
almost everywhere for the actual Euclidean area. -/
theorem toBeltrami_reconstruct_ae :
    (fun z : ℍ => ((z.im : ℂ) ^ 2)⁻¹ *
      conj ((toBeltrami f hf ha hb).val z)) =ᵐ[flatMeasure] f := by
  filter_upwards [ae_hyperbolic_iff.mp (toBeltrami_coe_ae f hf ha hb)] with z hz
  rw [hz, beltramiValue_apply, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj]
  rw [← mul_assoc, inv_mul_cancel₀
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr z.im_ne_zero)), one_mul]

private theorem essSup_volume_eq_flat (g : ℍ → ℂ) :
    eLpNormEssSup g (volume : Measure ℍ) = eLpNormEssSup g flatMeasure :=
  le_antisymm
    (eLpNormEssSup_mono_measure g
      (withDensity_absolutelyContinuous flatMeasure hyperbolicDensity))
    (eLpNormEssSup_mono_measure g flat_absolutelyContinuous_hyperbolic)

/-- The class norm is exactly the original weighted essential norm. -/
theorem norm_toBeltrami : ‖toBeltrami f hf ha hb‖ = weightedEssNorm f := by
  change ‖(beltramiValue_memLp f hf hb).toLp (beltramiValue f)‖ = _
  rw [Lp.norm_toLp]
  unfold weightedEssNorm
  congr 1
  rw [eLpNorm_exponent_top (beltramiValue_memLp f hf hb).aestronglyMeasurable, essSup_volume_eq_flat]
  rw [← eLpNorm_exponent_top (beltramiValue_aestronglyMeasurable f hf)]
  change eLpNorm (star (weightedValue f)) ⊤ flatMeasure = _
  exact eLpNorm_star

/-- Exactly the original almost-everywhere coefficient equality is identified. -/
theorem toBeltrami_eq_iff (g : ℍ → ℂ) (hg : AEStronglyMeasurable g flatMeasure)
    (hga : ∀ γ ∈ Γ, ∀ z : ℍ, g (γ • z) / denominator γ z ^ 4 = g z)
    (hgb : ∃ M : ℝ, ∀ᵐ z ∂flatMeasure, ‖g z‖ * z.im ^ 2 ≤ M) :
    toBeltrami f hf ha hb = toBeltrami g hg hga hgb ↔ f =ᵐ[flatMeasure] g := by
  constructor
  · intro he
    have hr := toBeltrami_reconstruct_ae f hf ha hb
    rw [he] at hr
    exact hr.symm.trans (toBeltrami_reconstruct_ae g hg hga hgb)
  · intro he
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [toBeltrami_coe_ae f hf ha hb, toBeltrami_coe_ae g hg hga hgb,
      ae_hyperbolic_iff.mpr he] with z hzf hzg hfg
    rw [hzf, hzg, beltramiValue_apply, beltramiValue_apply, hfg]

end LowDimensionalTopology.Geometry.Teichmuller.MeasurableQuadratic
