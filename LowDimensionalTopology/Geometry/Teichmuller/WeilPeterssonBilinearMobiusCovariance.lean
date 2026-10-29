module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSourceKernels
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCrossKernelCovariance
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSameHalfMobius
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicMovingKernelVariation
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedUniqueness
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Ordinary Cauchy change of variables for the original bilinear kernel

The concrete flat-area change of variables gives an ordinary Cauchy identity
with a correction constant in its evaluation point. Differentiating the
identity as a real map transports the actual inner principal value. The
lower outer evaluation then gives the bilinear kernel's tensor factors.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology
open scoped UpperHalfPlane ComplexConjugate ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open GammaMeasurableBeltrami LiZhongQC

private theorem mobius_height_cancel (f : ℍ → ℂ) (z : ℍ) :
    (hyperbolicDensity z).toReal • ((z.im : ℂ) ^ 2 * f z) = f z := by
  simp only [hyperbolicDensity, ENNReal.coe_toReal, NNReal.coe_pow,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk, Complex.real_smul]
  push_cast
  field_simp [z.im_ne_zero]

private theorem mobius_flat_integral_to_height (f : ℍ → ℂ) :
    (∫ z : ℍ, f z ∂flatArea) = ∫ z : ℍ, (z.im : ℂ) ^ 2 * f z ∂volume := by
  change _ = ∫ z : ℍ, (z.im : ℂ) ^ 2 * f z ∂(flatArea.withDensity hyperbolicDensity)
  rw [integral_withDensity_eq_integral_toReal_smul measurable_hyperbolicDensity
    (Eventually.of_forall fun z => by simp [hyperbolicDensity])]
  exact integral_congr_ae (Eventually.of_forall fun z => (mobius_height_cancel f z).symm)

private def mobius_flat_jacobian (γ : Deck) (z : ℍ) : ℂ :=
  ((denominator γ z * conj (denominator γ z)) ^ 2)⁻¹

private theorem mobius_height_square (γ : Deck) (z : ℍ) :
    ((γ • z : ℍ).im : ℂ) ^ 2 = (z.im : ℂ) ^ 2 * mobius_flat_jacobian γ z := by
  have him : (γ • z : ℍ).im = z.im / Complex.normSq (denominator γ z) := by
    simp [MulAction.compHom_smul_def, UpperHalfPlane.im_smul_eq_div_normSq,
      Matrix.SpecialLinearGroup.det_mapGL, UpperHalfPlane.denom, denominator]
  have hcomplex : ((γ • z : ℍ).im : ℂ) =
      (z.im : ℂ) / (denominator γ z * conj (denominator γ z)) := by
    rw [Complex.mul_conj]
    exact_mod_cast him
  rw [hcomplex]
  change ((z.im : ℂ) / (denominator γ z * conj (denominator γ z))) ^ 2 =
    (z.im : ℂ) ^ 2 / (denominator γ z * conj (denominator γ z)) ^ 2
  exact div_pow _ _ 2

private theorem mobius_flat_integral_comp (γ : Deck) (f : ℍ → ℂ) :
    (∫ z : ℍ, f z ∂flatArea) =
      ∫ z : ℍ, f (γ • z) * mobius_flat_jacobian γ z ∂flatArea := by
  calc
    _ = ∫ z : ℍ, (z.im : ℂ) ^ 2 * f z ∂volume := mobius_flat_integral_to_height f
    _ = ∫ z : ℍ, ((γ • z : ℍ).im : ℂ) ^ 2 * f (γ • z) ∂volume :=
      ((measurePreserving_deck γ).integral_comp
        (Homeomorph.smul γ).measurableEmbedding (fun z : ℍ => (z.im : ℂ) ^ 2 * f z)).symm
    _ = ∫ z : ℍ, (z.im : ℂ) ^ 2 *
        (f (γ • z) * mobius_flat_jacobian γ z) ∂volume := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        change ((γ • z : ℍ).im : ℂ) ^ 2 * f (γ • z) =
          (z.im : ℂ) ^ 2 * (f (γ • z) * mobius_flat_jacobian γ z)
        rw [mobius_height_square]
        ring
    _ = _ := (mobius_flat_integral_to_height _).symm

private theorem mobius_upperExtension_integral (f : ℍ → ℂ) :
    (∫ w : ℂ, upperExtension f w) = ∫ η : ℍ, f η ∂flatArea := by
  have he : upperHalf.indicator (upperExtension f) = upperExtension f := by
    funext w
    by_cases hw : w ∈ upperHalf
    · exact indicator_of_mem hw _
    · simp only [indicator_of_notMem hw, upperExtension, show ¬0 < w.im from hw, dite_false]
  calc
    _ = ∫ w : ℂ, upperHalf.indicator (upperExtension f) w := by rw [he]
    _ = ∫ w : ℂ in upperHalf, upperExtension f w := integral_indicator isOpen_upperHalf.measurableSet
    _ = ∫ η : ℍ, upperExtension f η ∂flatArea := by
      rw [← map_flat_coe]
      exact UpperHalfPlane.measurableEmbedding_coe.integral_map _
    _ = _ := integral_congr_ae (Eventually.of_forall fun η => by
      change upperExtension f (η : ℂ) = f η
      rw [upperExtension, dite_eq_left (show 0 < (η : ℂ).im from η.im_pos)])

private theorem mobius_cauchyT_to_flat (b : Ambient) (z ξ : ℍ) :
    cauchyT (innerInput (fun η => b η) z) ξ = -(1 / (Real.pi : ℂ)) *
      ∫ η : ℍ, b η * cauchySquare η (conj (z : ℂ)) / ((η : ℂ) - ξ) ∂flatArea := by
  have he : (fun w : ℂ => innerInput (fun η => b η) z w / (w - ξ)) =
      upperExtension (fun η : ℍ => b η * cauchySquare η (conj (z : ℂ)) / ((η : ℂ) - ξ)) := by
    funext w
    by_cases hw : 0 < w.im
    · simp only [innerInput, upperExtension, hw, dite_true]
    · simp only [innerInput, upperExtension, hw, dite_false, zero_div]
  rw [cauchyT, he, mobius_upperExtension_integral]

private theorem mobius_coefficient_smul_ae {Γ : Subgroup Deck}
    (b : Space Γ) (γ : Deck) (hγ : γ ∈ Γ) :
    ∀ᵐ η : ℍ ∂flatArea,
      b.val (γ • η : ℍ) = b.val η * conj (denominator γ η) ^ 2 / denominator γ η ^ 2 := by
  have h := (mem_compatibleSubmodule_iff b.val).1 b.property γ hγ
  filter_upwards [ae_hyperbolic_iff.mp h] with η hη
  have hd := denominator_ne_zero γ η
  have hdc : conj (denominator γ η) ≠ 0 := by
    intro he
    apply hd
    simpa only [Complex.conj_conj, map_zero] using congrArg conj he
  unfold phase at hη
  simp only [map_pow] at hη
  field_simp [hd, hdc] at hη ⊢
  linear_combination -hη

private theorem mobius_cauchyT_tensor_change {Γ : Subgroup Deck}
    (b : Space Γ) (γ : Deck) (hγ : γ ∈ Γ) (z ξ : ℍ)
    (hvalue : Integrable (fun η : ℍ =>
      b.val η * cauchySquare η (conj (z : ℂ)) / ((η : ℂ) - ξ)) flatArea)
    (hcorrection : γ 1 0 ≠ 0 → Integrable (fun η : ℍ =>
      b.val η * cauchySquare η (conj (z : ℂ)) / denominator γ η) flatArea) :
    cauchyT (innerInput (fun η => b.val η) (γ • z)) (γ • ξ : ℍ) =
      conj (denominator γ z) ^ 2 *
        (cauchyT (innerInput (fun η => b.val η) z) ξ +
          ((γ 1 0 : ℂ) / (Real.pi : ℂ)) *
            ∫ η : ℍ, b.val η * cauchySquare η (conj (z : ℂ)) / denominator γ η ∂flatArea) := by
  let f : ℍ → ℂ := fun η => b.val η * cauchySquare η (conj (z : ℂ))
  have hneqC : ∀ᵐ η : ℂ ∂Measure.map UpperHalfPlane.coe flatArea, η ≠ (ξ : ℂ) := by
    rw [map_flat_coe]
    exact ae_restrict_of_ae (volume.ae_ne (ξ : ℂ))
  have hneq : ∀ᵐ η : ℍ ∂flatArea, η ≠ ξ :=
    (ae_of_ae_map UpperHalfPlane.measurableEmbedding_coe.measurable.aemeasurable hneqC).mono
      fun η hη heq => hη (congrArg UpperHalfPlane.coe heq)
  have he : (fun η : ℍ =>
      b.val (γ • η : ℍ) * cauchySquare (γ • η : ℍ) (conj ((γ • z : ℍ) : ℂ)) /
        (((γ • η : ℍ) : ℂ) - (γ • ξ : ℍ)) * mobius_flat_jacobian γ η) =ᵐ[flatArea]
      fun η : ℍ => conj (denominator γ z) ^ 2 *
        (f η / ((η : ℂ) - ξ) - (γ 1 0 : ℂ) * (f η / denominator γ η)) := by
    filter_upwards [mobius_coefficient_smul_ae b γ hγ, hneq] with η hη hηξ
    have hsub : (η : ℂ) - ξ ≠ 0 := sub_ne_zero.mpr (UpperHalfPlane.coe_injective.ne hηξ)
    have hdη := denominator_ne_zero γ η
    have hdξ := denominator_ne_zero γ ξ
    have hdcη : conj (denominator γ η) ≠ 0 := by
      intro h
      apply hdη
      simpa only [Complex.conj_conj, map_zero] using congrArg conj h
    rw [hη, cauchySquare_lower_smul, upper_difference_smul]
    dsimp only [mobius_flat_jacobian, f]
    field_simp [hdη, hdξ, hdcη, hsub]
    unfold denominator
    ring
  rw [mobius_cauchyT_to_flat, mobius_cauchyT_to_flat]
  rw [mobius_flat_integral_comp γ]
  rw [integral_congr_ae he]
  by_cases hc : γ 1 0 = 0
  · simp only [hc, Complex.ofReal_zero, zero_mul, sub_zero, zero_div]
    rw [integral_const_mul]
    ring
  · rw [integral_const_mul, integral_sub hvalue ((hcorrection hc).const_mul _), integral_const_mul]
    ring


open Surfaces

private theorem mobius_actual_cauchy_flat_integrable
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z ξ : ℍ) :
    Integrable (fun η : ℍ => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η *
      cauchySquare η (conj (z : ℂ)) / ((η : ℂ) - ξ)) flatArea := by
  have h := (HarmonicFirstVariation.harmonicInnerInput_cauchyT_dz R p hp q z ξ).1
  have hu := h.mono_measure (Measure.restrict_le_self (s := upperHalf))
  rw [← map_flat_coe] at hu
  have hh := (UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff (μ := flatArea)).mp hu
  refine hh.congr (Eventually.of_forall fun η => ?_)
  change innerInput (fun w => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val w) z η /
    ((η : ℂ) - ξ) = (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η *
      cauchySquare η (conj (z : ℂ)) / ((η : ℂ) - ξ)
  rw [innerInput, upperExtension, dite_eq_left (show 0 < (η : ℂ).im from η.im_pos)]

private theorem mobius_actual_cauchy_correction_integrable
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ)
    (γ : Deck) (hc : γ 1 0 ≠ 0) :
    Integrable (fun η : ℍ => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η *
      cauchySquare η (conj (z : ℂ)) / denominator γ η) flatArea := by
  let r : ℝ := -(γ 1 1) / (γ 1 0)
  have h := HarmonicFirstVariation.harmonicInnerInput_cauchy_boundary_integrable R p hp q z r
  have hu := h.mono_measure (Measure.restrict_le_self (s := upperHalf))
  rw [← map_flat_coe] at hu
  have hh : Integrable (fun η : ℍ => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η *
      cauchySquare η (conj (z : ℂ)) / ((η : ℂ) - (r : ℂ))) flatArea := by
    have hflat := (UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff (μ := flatArea)).mp hu
    refine hflat.congr (Eventually.of_forall fun η => ?_)
    change innerInput (fun w => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val w) z η /
      ((η : ℂ) - (r : ℂ)) = (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η *
        cauchySquare η (conj (z : ℂ)) / ((η : ℂ) - (r : ℂ))
    rw [innerInput, upperExtension, dite_eq_left (show 0 < (η : ℂ).im from η.im_pos)]
  have hcC : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
  have hd (η : ℍ) : denominator γ η = (γ 1 0 : ℂ) * ((η : ℂ) - (r : ℂ)) := by
    dsimp only [denominator, r]
    push_cast
    field_simp [hcC] ; ring
  refine (hh.div_const (γ 1 0 : ℂ)).congr (Eventually.of_forall fun η => ?_)
  change ((NativeHarmonicBeltrami.ofQuadratic R p hp q).val η *
    cauchySquare η (conj (z : ℂ)) / ((η : ℂ) - (r : ℂ))) / (γ 1 0 : ℂ) =
      (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η *
        cauchySquare η (conj (z : ℂ)) / denominator γ η
  rw [div_div, hd]
  congr 1
  ring

/-- The original weighted Cauchy transform changes by its actual scalar
weight and a genuine boundary-pole correction constant in the evaluation
point. The affine branch is treated before dividing by the lower-left entry. -/
theorem harmonicInnerInput_cauchyT_deck
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (γ : Deck) (hγ : γ ∈ Γ) (z ξ : ℍ) :
    cauchyT (innerInput (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) (γ • z))
        (γ • ξ : ℍ) =
      conj (denominator γ z) ^ 2 *
        (cauchyT (innerInput (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) z) ξ +
          ((γ 1 0 : ℂ) / (Real.pi : ℂ)) *
            ∫ η : ℍ, (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η *
              cauchySquare η (conj (z : ℂ)) / denominator γ η ∂flatArea) := by
  apply mobius_cauchyT_tensor_change (NativeHarmonicBeltrami.ofQuadratic R p hp q) γ hγ z ξ
  · exact mobius_actual_cauchy_flat_integrable R hp q z ξ
  · exact mobius_actual_cauchy_correction_integrable R hp q z γ

/-- Differentiating the actual ordinary Cauchy identity gives the tensor
weight of the same radial principal value. The Cauchy transform is used
as a real differentiable map, without a holomorphy assumption. -/
theorem harmonicInnerInput_hilbertHSmooth_deck
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (γ : Deck) (hγ : γ ∈ Γ) (z ξ : ℍ) :
    hilbertHSmooth
        (innerInput (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) (γ • z))
        (γ • ξ : ℍ) =
      denominator γ ξ ^ 2 * conj (denominator γ z) ^ 2 *
        hilbertHSmooth
          (innerInput (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) z) ξ := by
  let f₀ : ℂ → ℂ := innerInput
    (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) z
  let f₁ : ℂ → ℂ := innerInput
    (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) (γ • z)
  let L : ℂ := conj (denominator γ z) ^ 2
  let J : ℂ := ((γ 1 0 : ℂ) / (Real.pi : ℂ)) *
    ∫ η : ℍ, (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η *
      cauchySquare η (conj (z : ℂ)) / denominator γ η ∂flatArea
  have h₀D : DifferentiableAt ℝ (cauchyT f₀) (ξ : ℂ) :=
    (HarmonicFirstVariation.harmonicInnerInput_cauchyT_dz R p hp q z ξ).2.1
  have h₀H : dz (cauchyT f₀) ξ = hilbertHSmooth f₀ ξ :=
    (HarmonicFirstVariation.harmonicInnerInput_cauchyT_dz R p hp q z ξ).2.2
  have h₁D : DifferentiableAt ℝ (cauchyT f₁) ((γ • ξ : ℍ) : ℂ) :=
    (HarmonicFirstVariation.harmonicInnerInput_cauchyT_dz R p hp q (γ • z) (γ • ξ : ℍ)).2.1
  have h₁H : dz (cauchyT f₁) (γ • ξ : ℍ) = hilbertHSmooth f₁ (γ • ξ : ℍ) :=
    (HarmonicFirstVariation.harmonicInnerInput_cauchyT_dz R p hp q (γ • z) (γ • ξ : ℍ)).2.2
  have hM : HasDerivAt (utm_b_mob γ) (1 / denominator γ ξ ^ 2) (ξ : ℂ) :=
    utm_b_hasDerivAt_mob γ (denominator_ne_zero γ ξ)
  have hscale : HasDerivAt (fun v : ℂ => L * (v + J)) L (cauchyT f₀ ξ) := by
    have h : HasDerivAt (fun v : ℂ => L * v + L * J) L (cauchyT f₀ ξ) :=
      (hasDerivAt_const_mul L).add_const (L * J)
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun v => mul_add L v J)
  have hgerm : (cauchyT f₁ ∘ utm_b_mob γ) =ᶠ[𝓝 (ξ : ℂ)]
      ((fun v : ℂ => L * (v + J)) ∘ cauchyT f₀) := by
    filter_upwards [isOpen_upperHalf.mem_nhds ξ.im_pos] with w hw
    change cauchyT f₁ (utm_b_mob γ w) = L * (cauchyT f₀ w + J)
    rw [utm_b_mob_smul γ (show 0 < w.im from hw)]
    exact harmonicInnerInput_cauchyT_deck R hp q γ hγ z ⟨w, hw⟩
  have hleft := (eq6_4 (g := cauchyT f₁) hM.differentiableAt (by
    simpa only [utm_b_mob_coe] using h₁D)).1
  have hright := (eq6_5 h₀D hscale.differentiableAt).1
  have he : hilbertHSmooth f₁ (γ • ξ : ℍ) * (1 / denominator γ ξ ^ 2) =
      L * hilbertHSmooth f₀ ξ := by
    calc
      _ = dz (cauchyT f₁ ∘ utm_b_mob γ) ξ := by
        simpa only [utm_b_mob_coe, h₁H, hM.deriv] using hleft.symm
      _ = dz ((fun v : ℂ => L * (v + J)) ∘ cauchyT f₀) ξ := by
        simp only [dz, hgerm.fderiv_eq (𝕜 := ℝ)]
      _ = _ := by simpa only [hscale.deriv, h₀H] using hright
  change hilbertHSmooth f₁ (γ • ξ : ℍ) =
    denominator γ ξ ^ 2 * L * hilbertHSmooth f₀ ξ
  calc
    _ = (hilbertHSmooth f₁ (γ • ξ : ℍ) * (1 / denominator γ ξ ^ 2)) *
        denominator γ ξ ^ 2 := by field_simp [denominator_ne_zero γ ξ]
    _ = (L * hilbertHSmooth f₀ ξ) * denominator γ ξ ^ 2 :=
      congrArg (fun v : ℂ => v * denominator γ ξ ^ 2) he
    _ = _ := by ring

private theorem mobius_bilinear_to_flat (u v : ℍ → ℂ) (ζ z : ℍ) :
    bilinear u v ζ z = -(Real.pi : ℂ) *
      ∫ ξ : ℍ, u ξ * hilbertHSmooth (innerInput v z) ξ *
        cauchySquare ξ (conj (ζ : ℂ)) ∂flatArea := by
  let f : ℂ → ℂ := outerInput u v z
  have hs : tsupport f ⊆ {ξ : ℂ | 0 ≤ ξ.im} := by
    apply closure_minimal ?_ (isClosed_le continuous_const Complex.continuous_im)
    intro ξ hξ
    by_contra hn
    have hnot : ¬0 < ξ.im := fun h => hn h.le
    apply hξ
    simp only [f, outerInput, upperExtension, hnot, dite_false]
  have hgap : ∀ ξ ∈ tsupport f, ζ.im ≤ ‖ξ - conj (ζ : ℂ)‖ := by
    intro ξ hξ
    calc
      ζ.im ≤ ξ.im + ζ.im := le_add_of_nonneg_left (hs hξ)
      _ = (ξ - conj (ζ : ℂ)).im := by
        simp only [sub_im, conj_im, UpperHalfPlane.coe_im, sub_neg_eq_add]
      _ ≤ |(ξ - conj (ζ : ℂ)).im| := le_abs_self _
      _ ≤ ‖ξ - conj (ζ : ℂ)‖ := Complex.abs_im_le_norm _
  have hext : (fun ξ : ℂ => -(1 / (Real.pi : ℂ)) * f ξ / (ξ - conj (ζ : ℂ)) ^ 2) =
      upperExtension (fun ξ : ℍ => -(1 / (Real.pi : ℂ)) *
        (u ξ * hilbertHSmooth (innerInput v z) ξ * cauchySquare ξ (conj (ζ : ℂ)))) := by
    funext ξ
    by_cases hξ : 0 < ξ.im
    · simp only [f, outerInput, upperExtension, hξ, dite_true, cauchySquare]
      ring
    · simp only [f, outerInput, upperExtension, hξ, dite_false, mul_zero, zero_div]
  have hH : hilbertHSmooth f (conj (ζ : ℂ)) =
      -(1 / (Real.pi : ℂ)) *
        ∫ ξ : ℍ, u ξ * hilbertHSmooth (innerInput v z) ξ *
          cauchySquare ξ (conj (ζ : ℂ)) ∂flatArea := by
    rw [offsupp_hilbertHSmooth_eq_integral hgap ζ.im_pos, hext,
      mobius_upperExtension_integral, integral_const_mul]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold bilinear
  change (Real.pi : ℂ) ^ 2 * hilbertHSmooth f (conj (ζ : ℂ)) = _
  rw [hH]
  field_simp [hπ]

/-- The original bilinear kernel of two actual quadratic harmonic
coefficients has its two conjugate squared deck factors. Its inner
singularity is handled by differentiating a genuine Cauchy identity. -/
theorem bilinear_ofQuadratic_deck
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q₁ q₂ : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (γ : Deck) (hγ : γ ∈ Γ) (ζ z : ℍ) :
    bilinear
        (fun ξ => (NativeHarmonicBeltrami.ofQuadratic R p hp q₁).val ξ)
        (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q₂).val η) (γ • ζ) (γ • z) =
      conj (denominator γ ζ) ^ 2 * conj (denominator γ z) ^ 2 *
        bilinear
          (fun ξ => (NativeHarmonicBeltrami.ofQuadratic R p hp q₁).val ξ)
          (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q₂).val η) ζ z := by
  let b₁ := NativeHarmonicBeltrami.ofQuadratic R p hp q₁
  let b₂ := NativeHarmonicBeltrami.ofQuadratic R p hp q₂
  have he : (fun ξ : ℍ => b₁.val (γ • ξ : ℍ) *
      hilbertHSmooth (innerInput (fun η => b₂.val η) (γ • z)) (γ • ξ : ℍ) *
        cauchySquare (γ • ξ : ℍ) (conj ((γ • ζ : ℍ) : ℂ)) * mobius_flat_jacobian γ ξ) =ᵐ[flatArea]
      fun ξ : ℍ => (conj (denominator γ ζ) ^ 2 * conj (denominator γ z) ^ 2) *
        (b₁.val ξ * hilbertHSmooth (innerInput (fun η => b₂.val η) z) ξ *
          cauchySquare ξ (conj (ζ : ℂ))) := by
    filter_upwards [mobius_coefficient_smul_ae b₁ γ hγ] with ξ hξ
    rw [hξ, harmonicInnerInput_hilbertHSmooth_deck R hp q₂ γ hγ z ξ,
      cauchySquare_lower_smul]
    have hdc : conj (denominator γ ξ) ≠ 0 := by
      intro h
      apply denominator_ne_zero γ ξ
      simpa only [Complex.conj_conj, map_zero] using congrArg conj h
    dsimp only [mobius_flat_jacobian]
    field_simp [denominator_ne_zero γ ξ, hdc] ; ring
  rw [mobius_bilinear_to_flat, mobius_bilinear_to_flat,
    mobius_flat_integral_comp γ, integral_congr_ae he, integral_const_mul]
  ring

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree

/-- The same actual native bilinear kernel transforms covariantly under
an element of its actual deformed deck group. No covariance premise is
supplied for the principal value or for the final kernel. -/
theorem nativeWeilPetersson_bilinear_deck
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (u v : E) (γ : Deck) (hγ : γ ∈ deformedGroup hΓ ν) (ζ z : ℍ) :
    SourceKernel.bilinear
        (nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth ν P F hF u)
        (nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth ν P F hF v)
        (γ • ζ) (γ • z) =
      conj (denominator γ ζ) ^ 2 * conj (denominator γ z) ^ 2 *
        SourceKernel.bilinear
          (nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth ν P F hF u)
          (nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth ν P F hF v) ζ z := by
  let := C
  let bu := TH ν P F hF hsmooth ((K (β ν.val)).symm u)
  let bv := TH ν P F hF hsmooth ((K (β ν.val)).symm v)
  rcases (NativePetersson.mem_harmonicSubmodule_iff_exists_quadratic
    (deformedNativeSurface R hgenus hΓ hp ν) P (deformedTargetCover R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) F hF bu.val).mp bu.property with ⟨q₁, hq₁⟩
  rcases (NativePetersson.mem_harmonicSubmodule_iff_exists_quadratic
    (deformedNativeSurface R hgenus hΓ hp ν) P (deformedTargetCover R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) F hF bv.val).mp bv.property with ⟨q₂, hq₂⟩
  have h := SourceKernel.bilinear_ofQuadratic_deck
    (deformedNativeSurface R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) q₁ q₂ γ hγ ζ z
  rw [hq₁, hq₂] at h
  exact h

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
