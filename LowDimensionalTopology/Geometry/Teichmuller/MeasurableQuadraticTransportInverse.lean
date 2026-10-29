module

public import LowDimensionalTopology.Geometry.Teichmuller.MeasurableQuadraticTransport
public import LowDimensionalTopology.Geometry.Teichmuller.GammaPointwiseRepresentative

/-!
# The inverse conjugate-height transport on the original half-plane

The original pointwise Beltrami representative gives an actual measurable
quadratic coefficient on H. Its weighted essential norm is the same original
L-infinity class norm. All formulas stay on H; no planar extension or new
coefficient carrier is constructed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter MeasureTheory
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.MeasurableQuadratic

open GammaMeasurableBeltrami

/-- The literal inverse of the conjugate square-height formula on H. -/
def inverseBeltramiValue (κ : ℍ → ℂ) (z : ℍ) : ℂ :=
  ((z.im : ℂ) ^ 2)⁻¹ * conj (κ z)

/-- The original J formula recovers the entire given representative at every point. -/
theorem beltramiValue_inverseBeltramiValue (κ : ℍ → ℂ) (z : ℍ) :
    beltramiValue (inverseBeltramiValue κ) z = κ z := by
  rw [beltramiValue_apply, inverseBeltramiValue]
  simp only [map_mul, map_inv₀, map_pow, Complex.conj_ofReal, Complex.conj_conj]
  rw [← mul_assoc, mul_inv_cancel₀
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr z.im_ne_zero)), one_mul]

private theorem inverseBeltramiValue_aestronglyMeasurable {κ : ℍ → ℂ}
    (hκ : AEStronglyMeasurable κ (volume : Measure ℍ)) :
    AEStronglyMeasurable (inverseBeltramiValue κ) flatMeasure := by
  have hw : Measurable (fun z : ℍ => ((z.im : ℂ) ^ 2)⁻¹) := by fun_prop
  exact hw.aestronglyMeasurable.mul
    ((hκ.mono_ac flat_absolutelyContinuous_hyperbolic).star)

private theorem inverseBeltramiValue_automorphic
    {Γ : Subgroup Deck} {κ : ℍ → ℂ}
    (ha : ∀ γ ∈ Γ, ∀ z : ℍ, κ z = phase γ z * κ (γ • z))
    (γ : Deck) (hγ : γ ∈ Γ) (z : ℍ) :
    inverseBeltramiValue κ (γ • z) / denominator γ z ^ 4 =
      inverseBeltramiValue κ z := by
  have hd := denominator_ne_zero γ z
  have hcd : conj (denominator γ z) ≠ 0 := by
    intro h
    apply hd
    simpa only [Complex.conj_conj, map_zero] using congrArg conj h
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_ne_zero
  have him : (γ • z : ℍ).im = z.im / Complex.normSq (denominator γ z) := by
    simp [MulAction.compHom_smul_def, UpperHalfPlane.im_smul_eq_div_normSq,
      Matrix.SpecialLinearGroup.det_mapGL, UpperHalfPlane.denom, denominator]
  have himc : ((γ • z : ℍ).im : ℂ) =
      (z.im : ℂ) / (denominator γ z * conj (denominator γ z)) := by
    rw [Complex.mul_conj]
    exact_mod_cast him
  have hcomp := congrArg conj (ha γ hγ z)
  simp only [phase, map_mul, map_div₀, map_pow, Complex.conj_conj] at hcomp
  simp only [inverseBeltramiValue]
  rw [himc, hcomp]
  field_simp [hd, hcd, hy]

/-- A given bounded pointwise compatible representative supplies the original
flat measurability, pointwise weight-minus-four law, unchanged weighted bound,
and the exact original J value, without any extra regularity assumption. -/
theorem inverseBeltramiValue_properties {Γ : Subgroup Deck} {κ : ℍ → ℂ}
    (hκ : AEStronglyMeasurable κ (volume : Measure ℍ))
    (ha : ∀ γ ∈ Γ, ∀ z : ℍ, κ z = phase γ z * κ (γ • z))
    {M : ℝ} (hb : ∀ z : ℍ, ‖κ z‖ ≤ M) :
    AEStronglyMeasurable (inverseBeltramiValue κ) flatMeasure ∧
      (∀ γ ∈ Γ, ∀ z : ℍ,
        inverseBeltramiValue κ (γ • z) / denominator γ z ^ 4 =
          inverseBeltramiValue κ z) ∧
      (∀ z : ℍ, ‖inverseBeltramiValue κ z‖ * z.im ^ 2 ≤ M) ∧
      ∀ z : ℍ, beltramiValue (inverseBeltramiValue κ) z = κ z := by
  refine ⟨inverseBeltramiValue_aestronglyMeasurable hκ, ?_, ?_,
    beltramiValue_inverseBeltramiValue κ⟩
  · exact inverseBeltramiValue_automorphic ha
  · intro z
    calc
      ‖inverseBeltramiValue κ z‖ * z.im ^ 2 =
          ‖beltramiValue (inverseBeltramiValue κ) z‖ :=
        (norm_beltramiValue (inverseBeltramiValue κ) z).symm
      _ = ‖κ z‖ := congrArg norm (beltramiValue_inverseBeltramiValue κ z)
      _ ≤ M := hb z

/-- Every original compatible L-infinity class has a genuine weighted
measurable automorphic preimage on H, with the exact original weighted norm.
The pointwise representative is constructed by the actual Fuchsian-group
lemma; representability is not a premise. -/
theorem exists_quadratic_preimage {Γ : Subgroup Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (μ : Space Γ) :
    ∃ f : ℍ → ℂ,
      ∃ hf : AEStronglyMeasurable f flatMeasure,
      ∃ ha : ∀ γ ∈ Γ, ∀ z : ℍ, f (γ • z) / denominator γ z ^ 4 = f z,
      ∃ hb : ∃ M : ℝ, ∀ᵐ z ∂flatMeasure, ‖f z‖ * z.im ^ 2 ≤ M,
        toBeltrami f hf ha hb = μ ∧ weightedEssNorm f = ‖μ.val‖ := by
  obtain ⟨κ, hκeq, hκmeas, hκauto, hκbound⟩ :=
    exists_pointwiseRepresentative hΓ μ
  have hprop := inverseBeltramiValue_properties hκmeas hκauto hκbound
  let f := inverseBeltramiValue κ
  have hf : AEStronglyMeasurable f flatMeasure := hprop.1
  have ha : ∀ γ ∈ Γ, ∀ z : ℍ, f (γ • z) / denominator γ z ^ 4 = f z := hprop.2.1
  have hb : ∃ M : ℝ, ∀ᵐ z ∂flatMeasure, ‖f z‖ * z.im ^ 2 ≤ M :=
    ⟨‖μ.val‖, Eventually.of_forall hprop.2.2.1⟩
  have hclass : toBeltrami f hf ha hb = μ := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [toBeltrami_coe_ae f hf ha hb, hκeq] with z hz hκz
    exact hz.trans ((hprop.2.2.2 z).trans hκz)
  refine ⟨f, hf, ha, hb, hclass, ?_⟩
  calc
    weightedEssNorm f = ‖toBeltrami f hf ha hb‖ := (norm_toBeltrami f hf ha hb).symm
    _ = ‖μ.val‖ := congrArg norm hclass

end LowDimensionalTopology.Geometry.Teichmuller.MeasurableQuadratic
