module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonNativeRadialComparison

/-!
# Invariant truncations in the actual bilinear pairing
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Metric Filter MeasureTheory Topology
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open Surfaces LiZhongQC QuadraticBergman GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)

private def actualInvariantInnerValue (e : ℝ) (z ξ : ℍ) : ℂ :=
  -(1 / (Real.pi : ℂ)) * ∫ ρ : ℂ in actualInvariantExterior ξ e,
    innerInput (NativeHarmonicBeltrami.coefficient R p q) z ρ / (ρ - ξ) ^ 2

include hp in
private theorem actual_literal_input_measurable (z : ℍ) :
    Measurable (innerInput (NativeHarmonicBeltrami.coefficient R p q) z) := by
  have hmu := (NativeHarmonicBeltrami.coefficient_continuous R p hp q).measurable
  have hkernel : Measurable (fun η : ℍ => cauchySquare η (conj (z : ℂ))) := by
    unfold cauchySquare
    fun_prop
  have hcoe : Measurable (fun η : upperHalf => (⟨η.val, η.property⟩ : ℍ)) := by
    apply UpperHalfPlane.measurableEmbedding_coe.measurable_comp_iff.mp
    exact measurable_subtype_coe
  classical
  change Measurable (fun η : ℂ => if h : η ∈ upperHalf then
    NativeHarmonicBeltrami.coefficient R p q ⟨η, h⟩ * cauchySquare η (conj (z : ℂ)) else 0)
  exact ((hmu.mul hkernel).comp hcoe).dite measurable_const isOpen_upperHalf.measurableSet

include hp in
private theorem actualInvariantInnerValue_measurable (e : ℝ) (z : ℍ) :
    Measurable (actualInvariantInnerValue R p q e z) := by
  let G : ℍ × ℂ → ℂ := fun a =>
    innerInput (NativeHarmonicBeltrami.coefficient R p q) z a.2 / (a.2 - a.1) ^ 2
  let S : Set (ℍ × ℂ) := {a | e * ‖a.2 - conj (a.1 : ℂ)‖ < ‖a.2 - a.1‖}
  have hG : Measurable G :=
    ((actual_literal_input_measurable R p hp q z).comp measurable_snd).div (by fun_prop)
  have hS : MeasurableSet S := measurableSet_lt (by fun_prop) (by fun_prop)
  have hi := (hG.stronglyMeasurable.indicator hS).integral_prod_right'
    (ν := (volume : Measure ℂ))
  have heq : actualInvariantInnerValue R p q e z =
      fun ξ : ℍ => -(1 / (Real.pi : ℂ)) * ∫ ρ : ℂ, S.indicator G (ξ, ρ) := by
    funext ξ
    unfold actualInvariantInnerValue
    congr 1
    have hD : MeasurableSet (actualInvariantExterior ξ e) := by
      unfold actualInvariantExterior
      exact measurableSet_lt (by fun_prop) (by fun_prop)
    rw [← integral_indicator hD]
    apply integral_congr_ae
    exact Eventually.of_forall fun ρ => by
      simp only [actualInvariantExterior, S, G, indicator_apply, mem_ofPred_eq]
  rw [heq]
  exact (stronglyMeasurable_const.mul hi).measurable

private theorem actual_absolute_cross_pair_integrable (ζ z : ℍ) :
    Integrable (fun η : ℍ => ‖cauchySquare η (conj (ζ : ℂ))‖ *
      ‖cauchySquare η (conj (z : ℂ))‖) flatArea := by
  have hi := (cauchySquare_composition ζ z).1.norm
  change Integrable _ ((volume : Measure ℂ).restrict upperHalf) at hi
  rw [← map_flat_coe] at hi
  have hflat := UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff.mp hi
  refine hflat.congr (Eventually.of_forall fun η => ?_)
  have hc : cauchySquare (conj (η : ℂ)) ζ = conj (cauchySquare η (conj (ζ : ℂ))) := by
    simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
  change ‖cauchySquare (conj (η : ℂ)) ζ * cauchySquare η (conj (z : ℂ))‖ =
    ‖cauchySquare η (conj (ζ : ℂ))‖ * ‖cauchySquare η (conj (z : ℂ))‖
  rw [norm_mul, hc, Complex.norm_conj]

private def actualLimitOuterPair
    (u : HolomorphicQuadraticDifferential R.toRiemannAtlas) (ζ z η : ℍ) : ℂ :=
  NativeHarmonicBeltrami.coefficient R p u η * cauchySquare η (conj (ζ : ℂ)) *
    hilbertHSmooth (innerInput (NativeHarmonicBeltrami.coefficient R p q) z) η

include hp in
private theorem actualLimitOuterPair_integrable
    (u : HolomorphicQuadraticDifferential R.toRiemannAtlas) (ζ z : ℍ) :
    Integrable (actualLimitOuterPair R p q u ζ z) flatArea := by
  let f := innerInput (NativeHarmonicBeltrami.coefficient R p q) z
  let g := innerInput (NativeHarmonicBeltrami.coefficient R p u) ζ
  have hf : MemLp f 2 (volume : Measure ℂ) :=
    (memLp_congr_ae (actual_input_ae R p hp q z)).mp
      (innerInput_memLp_two (NativeHarmonicBeltrami.ofQuadratic R p hp q).val z)
  have hg : MemLp g 2 (volume : Measure ℂ) :=
    (memLp_congr_ae (actual_input_ae R p hp u ζ)).mp
      (innerInput_memLp_two (NativeHarmonicBeltrami.ofQuadratic R p hp u).val ζ)
  have hi : Integrable (fun η : ℂ => g η * hilbertH f η) (volume : Measure ℂ) :=
    hg.integrable_mul (hilbertH_memLp_two hf).1
  have hH := innerInput_ofQuadratic_hilbertHSmooth_eq_hilbertH_ae R hp q z
  rw [hilbertHSmooth_congr_ae (actual_input_ae R p hp q z),
    hilbertH_congr_ae (actual_input_ae R p hp q z)] at hH
  have hupper : IntegrableOn (fun η : ℂ => g η * hilbertHSmooth f η) upperHalf :=
    hi.integrableOn.congr (hH.mono fun η hη => by change _ * _ = _ * _; rw [hη])
  change Integrable _ ((volume : Measure ℂ).restrict upperHalf) at hupper
  rw [← map_flat_coe] at hupper
  have hflat := UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff.mp hupper
  exact hflat.congr (Eventually.of_forall fun η => by
    change innerInput (NativeHarmonicBeltrami.coefficient R p u) ζ η *
      hilbertHSmooth f η = actualLimitOuterPair R p q u ζ z η
    rw [actual_literal_input_value R p u ζ η]
    rfl)

/-- The exact original outer integrand after its positive invariant inner exclusion. -/
def actualInvariantOuterPair
    (u : HolomorphicQuadraticDifferential R.toRiemannAtlas) (e : ℝ) (ζ z η : ℍ) : ℂ :=
  NativeHarmonicBeltrami.coefficient R p u η * cauchySquare η (conj (ζ : ℂ)) *
    (-(1 / (Real.pi : ℂ)) * ∫ ρ : ℂ in actualInvariantExterior η e,
      innerInput (NativeHarmonicBeltrami.coefficient R p q) z ρ / (ρ - η) ^ 2)

include hp in
private theorem actualInvariantOuterPair_error_bound
    (u : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ z : ℍ, ∀ e : ℝ, 0 < e → e < 1 / 16 →
      Integrable (actualInvariantOuterPair R p q u e ζ z) flatArea ∧
      (∫ η : ℍ, ‖actualInvariantOuterPair R p q u e ζ z η -
          actualLimitOuterPair R p q u ζ z η‖ ∂flatArea) ≤
        C * e * ∫ η : ℍ, ‖cauchySquare η (conj (ζ : ℂ))‖ *
          ‖cauchySquare η (conj (z : ℂ))‖ ∂flatArea := by
  obtain ⟨Mu, hMu, hbu⟩ := uniformizedQuadratic_weightedBound R p hp u
  obtain ⟨Mq, hMq, hbq⟩ := uniformizedQuadratic_weightedBound R p hp q
  let C : ℝ := 4096 * Mu * Mq
  refine ⟨C, by dsimp only [C]; positivity, fun ζ z e he0 he16 => ?_⟩
  let W : ℍ → ℝ := fun η => ‖cauchySquare η (conj (ζ : ℂ))‖ *
    ‖cauchySquare η (conj (z : ℂ))‖
  have hW : Integrable W flatArea := actual_absolute_cross_pair_integrable ζ z
  have hlim := actualLimitOuterPair_integrable R p hp q u ζ z
  have hmu (η : ℍ) : ‖NativeHarmonicBeltrami.coefficient R p u η‖ ≤ Mu := by
    rw [NativeHarmonicBeltrami.norm_coefficient]
    exact hbu (η : ℂ) η.im_pos
  have hinner (η : ℍ) : ‖actualInvariantInnerValue R p q e z η -
      hilbertHSmooth (innerInput (NativeHarmonicBeltrami.coefficient R p q) z) η‖ ≤
      4096 * Mq * e * ‖cauchySquare η (conj (z : ℂ))‖ :=
    actual_invariant_error_bound R p hp q Mq hMq hbq η z he0 he16
  have hpoint (η : ℍ) : ‖actualInvariantOuterPair R p q u e ζ z η -
      actualLimitOuterPair R p q u ζ z η‖ ≤ (C * e) * W η := by
    have heq : actualInvariantOuterPair R p q u e ζ z η -
        actualLimitOuterPair R p q u ζ z η =
      (NativeHarmonicBeltrami.coefficient R p u η * cauchySquare η (conj (ζ : ℂ))) *
        (actualInvariantInnerValue R p q e z η -
          hilbertHSmooth (innerInput (NativeHarmonicBeltrami.coefficient R p q) z) η) := by
      unfold actualInvariantOuterPair actualLimitOuterPair actualInvariantInnerValue
      ring
    rw [heq, norm_mul, norm_mul]
    calc
      _ ≤ (Mu * ‖cauchySquare η (conj (ζ : ℂ))‖) *
          (4096 * Mq * e * ‖cauchySquare η (conj (z : ℂ))‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hmu η) (norm_nonneg _))
          (hinner η) (norm_nonneg _) (mul_nonneg hMu (norm_nonneg _))
      _ = _ := by dsimp only [C, W]; ring
  have hm : Measurable (actualInvariantOuterPair R p q u e ζ z) := by
    have hcoef := (NativeHarmonicBeltrami.coefficient_continuous R p hp u).measurable
    have hker : Measurable (fun η : ℍ => cauchySquare η (conj (ζ : ℂ))) := by
      unfold cauchySquare
      fun_prop
    exact (hcoef.mul hker).mul (actualInvariantInnerValue_measurable R p hp q e z)
  have hdiff : Integrable (fun η : ℍ => actualInvariantOuterPair R p q u e ζ z η -
      actualLimitOuterPair R p q u ζ z η) flatArea :=
    (hW.const_mul (C * e)).mono'
      (hm.aestronglyMeasurable.sub hlim.aestronglyMeasurable) (Eventually.of_forall hpoint)
  refine ⟨(hdiff.add hlim).congr (Eventually.of_forall fun η => sub_add_cancel _ _), ?_⟩
  calc
    _ ≤ ∫ η : ℍ, (C * e) * W η ∂flatArea :=
      integral_mono_ae hdiff.norm (hW.const_mul (C * e)) (Eventually.of_forall hpoint)
    _ = _ := integral_const_mul _ _

private theorem actual_bilinear_limitOuterPair
    (u : HolomorphicQuadraticDifferential R.toRiemannAtlas) (ζ z : ℍ) :
    bilinear (NativeHarmonicBeltrami.coefficient R p u)
      (NativeHarmonicBeltrami.coefficient R p q) ζ z =
      -(Real.pi : ℂ) * ∫ η : ℍ, actualLimitOuterPair R p q u ζ z η ∂flatArea := by
  let f := outerInput (NativeHarmonicBeltrami.coefficient R p u)
    (NativeHarmonicBeltrami.coefficient R p q) z
  let G : ℂ → ℂ := fun η => f η / (η - conj (ζ : ℂ)) ^ 2
  have hs : tsupport f ⊆ {η : ℂ | 0 ≤ η.im} := by
    apply closure_minimal ?_ (isClosed_le continuous_const Complex.continuous_im)
    intro η hη
    by_contra hn
    have hnot : ¬0 < η.im := fun h => hn h.le
    apply hη
    simp only [f, outerInput, upperExtension, hnot, dite_false]
  have hgap : ∀ η ∈ tsupport f, ζ.im ≤ ‖η - conj (ζ : ℂ)‖ := by
    intro η hη
    calc
      ζ.im ≤ η.im + ζ.im := le_add_of_nonneg_left (hs hη)
      _ = (η - conj (ζ : ℂ)).im := by
        simp only [sub_im, conj_im, UpperHalfPlane.coe_im, sub_neg_eq_add]
      _ ≤ |(η - conj (ζ : ℂ)).im| := le_abs_self _
      _ ≤ _ := Complex.abs_im_le_norm _
  have hzero : upperHalf.indicator G = G := by
    funext η
    by_cases hη : η ∈ upperHalf
    · exact indicator_of_mem hη G
    · rw [indicator_of_notMem hη]
      simp only [G, f, outerInput, upperExtension, show ¬0 < η.im from hη, dite_false, zero_div]
  have hplane : (∫ η : ℂ, G η) =
      ∫ η : ℍ, actualLimitOuterPair R p q u ζ z η ∂flatArea := by
    calc
      _ = ∫ η : ℂ, upperHalf.indicator G η := by rw [hzero]
      _ = ∫ η : ℂ in upperHalf, G η := integral_indicator isOpen_upperHalf.measurableSet
      _ = ∫ η : ℍ, G η ∂flatArea := by
        rw [← map_flat_coe]
        exact UpperHalfPlane.measurableEmbedding_coe.integral_map
          (μ := flatArea) G
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun η => by
          dsimp only [G, f, actualLimitOuterPair, outerInput, upperExtension]
          rw [dite_eq_left (show 0 < (η : ℂ).im from η.im_pos)]
          unfold cauchySquare
          ring
  have hH := offsupp_hilbertHSmooth_eq_integral hgap ζ.im_pos
  have hnorm : (∫ η : ℂ, -(1 / (Real.pi : ℂ)) * f η / (η - conj (ζ : ℂ)) ^ 2) =
      -(1 / (Real.pi : ℂ)) * ∫ η : ℍ, actualLimitOuterPair R p q u ζ z η ∂flatArea := by
    calc
      _ = -(1 / (Real.pi : ℂ)) * ∫ η : ℂ, G η := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun η => by dsimp only [G]; ring
      _ = _ := by rw [hplane]
  unfold bilinear
  change (Real.pi : ℂ) ^ 2 * hilbertHSmooth f (conj (ζ : ℂ)) = _
  rw [hH, hnorm]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hπ]

/-- The original bilinear kernel with the same positive invariant
exclusion in its inner integral and its nonsingular lower outer pairing. -/
def bilinearInvariantTruncation
    (u : HolomorphicQuadraticDifferential R.toRiemannAtlas) (e : ℝ) (ζ z : ℍ) : ℂ :=
  -(Real.pi : ℂ) * ∫ η : ℍ, actualInvariantOuterPair R p q u e ζ z η ∂flatArea

include hp in
/-- The positive invariant inner truncations converge in the actual
bilinear pairing. Their outer integrals are genuinely absolute, and the
error is bounded by the concrete integrable pair of cross kernels. -/
theorem bilinear_ofQuadratic_invariant_truncation_tendsto
    (u : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ z : ℍ,
      (∀ e : ℝ, 0 < e → e < 1 / 16 →
        Integrable (actualInvariantOuterPair R p q u e ζ z) flatArea ∧
        ‖bilinearInvariantTruncation R p q u e ζ z -
            bilinear (NativeHarmonicBeltrami.coefficient R p u)
              (NativeHarmonicBeltrami.coefficient R p q) ζ z‖ ≤
          C * e * ∫ η : ℍ, ‖cauchySquare η (conj (ζ : ℂ))‖ *
            ‖cauchySquare η (conj (z : ℂ))‖ ∂flatArea) ∧
      Tendsto (fun e : ℝ => bilinearInvariantTruncation R p q u e ζ z)
        (𝓝[>] (0 : ℝ))
        (𝓝 (bilinear (NativeHarmonicBeltrami.coefficient R p u)
          (NativeHarmonicBeltrami.coefficient R p q) ζ z)) := by
  obtain ⟨C, hC, hb⟩ := actualInvariantOuterPair_error_bound R p hp q u
  refine ⟨Real.pi * C, mul_nonneg Real.pi_pos.le hC, fun ζ z => ?_⟩
  have hlim := actualLimitOuterPair_integrable R p hp q u ζ z
  have hA (e : ℝ) (he0 : 0 < e) (he16 : e < 1 / 16) :
      Integrable (actualInvariantOuterPair R p q u e ζ z) flatArea ∧
      ‖bilinearInvariantTruncation R p q u e ζ z -
          bilinear (NativeHarmonicBeltrami.coefficient R p u)
            (NativeHarmonicBeltrami.coefficient R p q) ζ z‖ ≤
        (Real.pi * C) * e * ∫ η : ℍ, ‖cauchySquare η (conj (ζ : ℂ))‖ *
          ‖cauchySquare η (conj (z : ℂ))‖ ∂flatArea := by
    obtain ⟨hi, herror⟩ := hb ζ z e he0 he16
    refine ⟨hi, ?_⟩
    unfold bilinearInvariantTruncation
    rw [actual_bilinear_limitOuterPair R p q u ζ z, ← mul_sub, ← integral_sub hi hlim]
    calc
      _ = Real.pi * ‖∫ η : ℍ, actualInvariantOuterPair R p q u e ζ z η -
          actualLimitOuterPair R p q u ζ z η ∂flatArea‖ := by
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      _ ≤ Real.pi * ∫ η : ℍ, ‖actualInvariantOuterPair R p q u e ζ z η -
          actualLimitOuterPair R p q u ζ z η‖ ∂flatArea :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) Real.pi_pos.le
      _ ≤ Real.pi * (C * e * ∫ η : ℍ, ‖cauchySquare η (conj (ζ : ℂ))‖ *
          ‖cauchySquare η (conj (z : ℂ))‖ ∂flatArea) :=
        mul_le_mul_of_nonneg_left herror Real.pi_pos.le
      _ = _ := by ring
  refine ⟨hA, tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  have hbound : ∀ᶠ e in 𝓝[>] (0 : ℝ),
      ‖bilinearInvariantTruncation R p q u e ζ z -
          bilinear (NativeHarmonicBeltrami.coefficient R p u)
            (NativeHarmonicBeltrami.coefficient R p q) ζ z‖ ≤
        (Real.pi * C) * e * ∫ η : ℍ, ‖cauchySquare η (conj (ζ : ℂ))‖ *
          ‖cauchySquare η (conj (z : ℂ))‖ ∂flatArea := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 16)] with e he
    exact (hA e he.1 he.2).2
  have hezero : Tendsto (fun e : ℝ => e) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun _ : ℝ => Real.pi * C) (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi * C)) :=
    tendsto_const_nhds
  have hzero : Tendsto (fun e : ℝ => (Real.pi * C) * e *
      ∫ η : ℍ, ‖cauchySquare η (conj (ζ : ℂ))‖ * ‖cauchySquare η (conj (z : ℂ))‖ ∂flatArea)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (hc.mul hezero).mul_const
      (∫ η : ℍ, ‖cauchySquare η (conj (ζ : ℂ))‖ * ‖cauchySquare η (conj (z : ℂ))‖ ∂flatArea)
  exact squeeze_zero' (Eventually.of_forall fun _e => norm_nonneg _) hbound hzero

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
