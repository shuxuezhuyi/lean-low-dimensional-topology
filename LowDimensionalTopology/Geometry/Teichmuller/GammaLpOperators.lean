module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.Tactic.Ring

/-!
# Actual weighted deck pullbacks on hyperbolic L-infinity

The measure is the invariant hyperbolic area measure already defined on the
upper half-plane. Deck pullback is measure-preserving composition followed by
multiplication by the actual unit-modulus Beltrami phase. Every operator is a
complex linear isometry on genuine almost-everywhere classes.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped ENNReal ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

abbrev Ambient := Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure ℍ)

abbrev Deck := Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The literal denominator in the real Möbius formula. -/
def denominator (γ : Deck) (z : ℍ) : ℂ := (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)

theorem denominator_ne_zero (γ : Deck) (z : ℍ) : denominator γ z ≠ 0 := by
  change (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) ≠ 0
  apply UpperHalfPlane.linear_ne_zero (cd := fun j => γ 1 j) z
  intro hz
  have hc : γ 1 0 = 0 := by simpa only [Pi.zero_apply] using congrFun hz (0 : Fin 2)
  have hd : γ 1 1 = 0 := by simpa only [Pi.zero_apply] using congrFun hz (1 : Fin 2)
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe γ
  have hfalse : (0 : ℝ) = 1 := by
    simpa only [hc, hd, mul_zero, sub_self] using hdet
  exact zero_ne_one hfalse

/-- The actual phase in the invariant measurable Beltrami tensor law. -/
def phase (γ : Deck) (z : ℍ) : ℂ :=
  denominator γ z ^ 2 / conj (denominator γ z ^ 2)

theorem norm_phase (γ : Deck) (z : ℍ) : ‖phase γ z‖ = 1 := by
  rw [phase, norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr (pow_ne_zero 2 (denominator_ne_zero γ z)))]

theorem continuous_phase (γ : Deck) : Continuous (phase γ) := by
  have hd : Continuous (denominator γ) :=
    (continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const
  apply (hd.pow 2).div (Complex.continuous_conj.comp (hd.pow 2))
  intro z hz
  change conj (denominator γ z ^ 2) = 0 at hz
  have hc := congrArg (fun w : ℂ => conj w) hz
  apply pow_ne_zero 2 (denominator_ne_zero γ z)
  simpa only [Complex.conj_conj, map_zero] using hc

theorem measurePreserving_deck (γ : Deck) :
    MeasurePreserving (fun z : ℍ => γ • z) volume volume := by
  change MeasurePreserving
    (fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ γ) • z) volume volume
  exact measurePreserving_smul (Matrix.SpecialLinearGroup.mapGL ℝ γ) volume

/-- Multiplication by an actually measurable unit-modulus function preserves L-infinity membership. -/
theorem unitMultiply_memLp (a : ℍ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℍ)) (hu : ∀ z, ‖a z‖ = 1)
    (f : Ambient) : MemLp (fun z => a z * f z) (⊤ : ℝ≥0∞) volume := by
  apply (Lp.memLp f).of_le_mul (c := (1 : ℝ)) (ha.mul (Lp.aestronglyMeasurable f))
  exact Eventually.of_forall (fun z => by
    change ‖a z * f z‖ ≤ 1 * ‖f z‖
    rw [norm_mul, hu z, one_mul])

/-- The genuine L-infinity class of the pointwise product with a unit-modulus function. -/
def unitMultiply (a : ℍ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℍ)) (hu : ∀ z, ‖a z‖ = 1)
    (f : Ambient) : Ambient :=
  (unitMultiply_memLp a ha hu f).toLp (fun z => a z * f z)

/-- The class product agrees almost everywhere with its actual pointwise representative. -/
theorem unitMultiply_coe_ae (a : ℍ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℍ)) (hu : ∀ z, ‖a z‖ = 1)
    (f : Ambient) : unitMultiply a ha hu f =ᵐ[volume] fun z => a z * f z :=
  (unitMultiply_memLp a ha hu f).coeFn_toLp

/-- Multiplication by an actual unit-modulus coefficient is a complex linear isometry. -/
def unitMultiplyIsometry (a : ℍ → ℂ)
    (ha : AEStronglyMeasurable a (volume : Measure ℍ)) (hu : ∀ z, ‖a z‖ = 1) :
    Ambient →ₗᵢ[ℂ] Ambient where
  toFun := unitMultiply a ha hu
  map_add' f g := by
    apply Lp.ext
    filter_upwards [unitMultiply_coe_ae a ha hu (f + g),
      unitMultiply_coe_ae a ha hu f, unitMultiply_coe_ae a ha hu g,
      Lp.coeFn_add f g,
      Lp.coeFn_add (unitMultiply a ha hu f) (unitMultiply a ha hu g)] with z hfg hf hg hadd hout
    change (f + g) z = f z + g z at hadd
    change (unitMultiply a ha hu f + unitMultiply a ha hu g) z =
      unitMultiply a ha hu f z + unitMultiply a ha hu g z at hout
    rw [hfg, hout, hadd, hf, hg]
    exact mul_add _ _ _
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [unitMultiply_coe_ae a ha hu (c • f),
      unitMultiply_coe_ae a ha hu f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (unitMultiply a ha hu f)] with z hcf hf hsmul hout
    change (c • f) z = c * f z at hsmul
    change (c • unitMultiply a ha hu f) z = c * unitMultiply a ha hu f z at hout
    change unitMultiply a ha hu (c • f) z = (c • unitMultiply a ha hu f) z
    rw [hcf, hout, hsmul, hf]
    ring
  norm_map' f := by
    change ‖unitMultiply a ha hu f‖ = ‖f‖
    have heq : ∀ᵐ z ∂(volume : Measure ℍ),
        ‖unitMultiply a ha hu f z‖ = ‖f z‖ := by
      filter_upwards [unitMultiply_coe_ae a ha hu f] with z hz
      rw [hz, norm_mul, hu z, one_mul]
    exact le_antisymm
      (Lp.norm_le_norm_of_ae_le (heq.mono fun _ h => h.le))
      (Lp.norm_le_norm_of_ae_le (heq.mono fun _ h => h.ge))

/-- The weighted actual deck pullback as a complex linear isometry. -/
def pullbackIsometry (γ : Deck) : Ambient →ₗᵢ[ℂ] Ambient :=
  (unitMultiplyIsometry (phase γ) (continuous_phase γ).aestronglyMeasurable
    (norm_phase γ)).comp
    (Lp.compMeasurePreservingₗᵢ ℂ (fun z : ℍ => γ • z) (measurePreserving_deck γ))

/-- The same operator in the continuous-linear-map interface used for closed kernels. -/
def pullback (γ : Deck) : Ambient →L[ℂ] Ambient :=
  (pullbackIsometry γ).toContinuousLinearMap

theorem pullback_coe_ae (γ : Deck) (μ : Ambient) :
    pullback γ μ =ᵐ[volume] fun z => phase γ z * μ (γ • z) := by
  have happly : pullback γ μ =
      unitMultiply (phase γ) (continuous_phase γ).aestronglyMeasurable (norm_phase γ)
        (Lp.compMeasurePreserving (fun z : ℍ => γ • z) (measurePreserving_deck γ) μ) := rfl
  rw [happly]
  filter_upwards [unitMultiply_coe_ae (phase γ) (continuous_phase γ).aestronglyMeasurable
    (norm_phase γ)
    (Lp.compMeasurePreserving (fun z : ℍ => γ • z) (measurePreserving_deck γ) μ),
    Lp.coeFn_compMeasurePreserving μ (measurePreserving_deck γ)] with z hz hμ
  rw [hz, hμ]
  rfl

theorem norm_pullback (γ : Deck) (μ : Ambient) : ‖pullback γ μ‖ = ‖μ‖ :=
  (pullbackIsometry γ).norm_map μ

end LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
