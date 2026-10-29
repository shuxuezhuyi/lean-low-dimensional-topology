module

public import LowDimensionalTopology.Geometry.Teichmuller.PlanarCoefficientTranslation
public import LowDimensionalTopology.Geometry.Quasiconformal.BeltramiParameterDerivative
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Canonical first variation at every full-plane coefficient

The literal translated coefficient is in the original full planar coefficient
ball. Its canonical solution is the genuine composition by the fixed actual
normalized inverse. Consequently every norm-differentiable real or complex
coefficient family has locally uniform first variation at every base point.
The result is expressed by the existing zero-base first-variation integral
applied to the actual coefficient derivative transport. Identifying this with
the expanded nonzero-base integral kernel is a separate change-of-variables step.

The sharp scalar coefficient bound and normalized uniqueness reuse the
LiZhongQC source of Wu Xiaobin; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.PlanarCoefficientTransport

/-- The literal full-plane coefficient translation remains strictly subunit. -/
theorem norm_translation_lt_one (ν μ : MeasurableBeltramiBall) :
    ‖translation ν μ.val‖ < 1 := by
  let k := max ‖μ.val‖ ‖ν.val‖
  have hk0 : 0 ≤ k := (norm_nonneg μ.val).trans (le_max_left _ _)
  have hk1 : k < 1 := max_lt (MeasurableBeltramiBall.norm_lt_one μ)
    (MeasurableBeltramiBall.norm_lt_one ν)
  have hr0 : 0 ≤ 2 * k / (1 + k ^ 2) := by positivity
  have hr1 : 2 * k / (1 + k ^ 2) < 1 := by
    apply (div_lt_one (by positivity : 0 < 1 + k ^ 2)).2
    have hs := mul_pos (sub_pos.mpr hk1) (sub_pos.mpr hk1)
    nlinarith
  have hraw : ∀ᵐ z : ℂ ∂volume,
      ‖rawTranslation ν μ.val z‖ ≤ 2 * k / (1 + k ^ 2) := by
    filter_upwards [lpInfinity_norm_ae_le μ.val, lpInfinity_norm_ae_le ν.val]
      with z hm hn
    have hf := LiZhongQC.ahQ_pseudo_bound hk0 hk1
      (hm.trans (le_max_left _ _)) (hn.trans (le_max_right _ _))
    change ‖(μ.val z - ν.val z) / (1 - conj (ν.val z) * μ.val z) *
      derivativePhase ν z‖ ≤ 2 * k / (1 + k ^ 2)
    rw [norm_mul]
    calc
      _ ≤ (2 * k / (1 + k ^ 2)) * 1 :=
        mul_le_mul hf (norm_derivativePhase_le ν z) (norm_nonneg _) hr0
      _ = _ := mul_one _
  apply lt_of_le_of_lt _ hr1
  apply lpInfinity_norm_le_of_ae_bound _ hr0
  filter_upwards [translation_coe_ae ν μ.val (MeasurableBeltramiBall.norm_lt_one μ),
    (normalizedEquiv_symm_quasiMeasurePreserving ν).ae hraw] with z ht hb
  rw [ht]
  exact hb

/-- The actual translated class in the original measurable coefficient ball. -/
def translatedBall (ν μ : MeasurableBeltramiBall) : MeasurableBeltramiBall :=
  ⟨translation ν μ.val, by
    simpa only [Metric.mem_ball, dist_zero_right] using norm_translation_lt_one ν μ⟩

@[simp] theorem translatedBall_val (ν μ : MeasurableBeltramiBall) :
    (translatedBall ν μ).val = translation ν μ.val := rfl

/-- Uniqueness identifies the actual canonical map, including its normalization. -/
theorem normalizedSolution_translatedBall (ν μ : MeasurableBeltramiBall) :
    normalizedMap (translatedBall ν μ) =
      (normalizedMap ν).symm.trans (normalizedMap μ) := by
  exact Quasiconformal.normalized_beltrami_homeomorph_unique
    (MeasurableBeltramiBall.normalizedSolution_spec (translatedBall ν μ)).1
    (translation_normalized_composite ν μ)

/-- Evaluation at the same original normalized image cancels the same inverse. -/
theorem normalizedSolution_translatedBall_apply (ν μ : MeasurableBeltramiBall) (w : ℂ) :
    normalizedMap (translatedBall ν μ) (normalizedMap ν w) = normalizedMap μ w := by
  exact (congrArg (fun e : ℂ ≃ₜ ℂ => e (normalizedMap ν w))
    (normalizedSolution_translatedBall ν μ)).trans
      (congrArg (normalizedMap μ) ((normalizedMap ν).symm_apply_apply w))

private theorem locallyUniform_of_translation_slope
    {ι : Type*} {l : Filter ι} {a : ι → ℂ} (ha : Tendsto a l (𝓝 0))
    (ha0 : ∀ᶠ t in l, a t ≠ 0) (ν : MeasurableBeltramiBall)
    (δ : Ambient) (μ : ι → MeasurableBeltramiBall)
    (hT : Tendsto (fun t => (a t)⁻¹ • translation ν (μ t).val) l (𝓝 δ)) :
    TendstoLocallyUniformly
      (fun t w => (normalizedMap (μ t) w - normalizedMap ν w) / a t)
      (fun w => Quasiconformal.firstVariation δ (normalizedMap ν w)) l := by
  let τ : ι → MeasurableBeltramiBall := fun t => translatedBall ν (μ t)
  let ε : ι → Ambient := fun t => (a t)⁻¹ • (τ t).val - δ
  have hε : Tendsto ε l (𝓝 0) := by
    simpa only [ε, τ, translatedBall_val, sub_self] using hT.sub_const δ
  have hτ : ∀ᶠ t in l, (τ t).val = a t • (δ + ε t) := by
    filter_upwards [ha0] with t ht
    dsimp only [ε]
    rw [← add_sub_assoc, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ ht, one_smul]
  have hz := Quasiconformal.normalizedSolution_locallyUniform_differenceQuotient
    ha ha0 δ hε τ hτ
  have hc := hz.comp (normalizedMap ν) (normalizedMap ν).continuous
  apply hc.congr
  intro t w
  change (normalizedMap (translatedBall ν (μ t)) (normalizedMap ν w) -
    normalizedMap ν w) / a t = _
  rw [normalizedSolution_translatedBall_apply]

/-- At any complex parameter and any full-plane base coefficient, a genuine
norm derivative of the coefficient family gives locally uniform first variation. -/
theorem normalizedSolution_complex_parameter_firstVariation
    (μ : ℂ → MeasurableBeltramiBall) {t₀ : ℂ} {η : Ambient}
    (hμ : HasDerivAt (fun t => (μ t).val) η t₀) :
    TendstoLocallyUniformly
      (fun t w => (normalizedMap (μ (t₀ + t)) w - normalizedMap (μ t₀) w) / t)
      (fun w => Quasiconformal.firstVariation (ambientDerivative (μ t₀) η)
        (normalizedMap (μ t₀) w)) (𝓝[≠] (0 : ℂ)) := by
  let ν := μ t₀
  have hf : HasDerivAt (fun t => translation ν (μ t).val)
      (ambientDerivative ν η) t₀ :=
    (hasFDerivAt_translation ν).comp_hasDerivAt_of_eq t₀ hμ rfl
  have hslope : Tendsto (fun t : ℂ => t⁻¹ • translation ν (μ (t₀ + t)).val)
      (𝓝[≠] (0 : ℂ)) (𝓝 (ambientDerivative ν η)) := by
    have hs := hf.tendsto_slope_zero
    rw [show translation ν (μ t₀).val = 0 from translation_base ν] at hs
    simpa only [sub_zero] using hs
  apply locallyUniform_of_translation_slope
    (tendsto_id.mono_left nhdsWithin_le_nhds) _ ν (ambientDerivative ν η)
      (fun t => μ (t₀ + t)) hslope
  filter_upwards [self_mem_nhdsWithin] with t ht
  simpa only [id_eq, mem_compl_iff, mem_singleton_iff] using ht

/-- The same conclusion holds for any real norm-differentiable family; no
pointwise holomorphic representatives or complex parameter hypothesis is added. -/
theorem normalizedSolution_real_parameter_firstVariation
    (μ : ℝ → MeasurableBeltramiBall) {t₀ : ℝ} {η : Ambient}
    (hμ : HasDerivAt (fun t => (μ t).val) η t₀) :
    TendstoLocallyUniformly
      (fun t w => (normalizedMap (μ (t₀ + t)) w - normalizedMap (μ t₀) w) / (t : ℂ))
      (fun w => Quasiconformal.firstVariation (ambientDerivative (μ t₀) η)
        (normalizedMap (μ t₀) w)) (𝓝[≠] (0 : ℝ)) := by
  let ν := μ t₀
  have hf : HasDerivAt (fun t => translation ν (μ t).val)
      (ambientDerivative ν η) t₀ :=
    ((hasFDerivAt_translation ν).restrictScalars ℝ).comp_hasDerivAt_of_eq t₀ hμ rfl
  have hslope : Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • translation ν (μ (t₀ + t)).val)
      (𝓝[≠] (0 : ℝ)) (𝓝 (ambientDerivative ν η)) := by
    have hs := hf.tendsto_slope_zero
    rw [show translation ν (μ t₀).val = 0 from translation_base ν] at hs
    simpa only [sub_zero, RCLike.real_smul_eq_coe_smul (K := ℂ),
      RCLike.ofReal_inv, RCLike.ofReal_eq_complex_ofReal] using hs
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ha : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [Complex.ofReal_zero, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto 0).comp ht
  apply locallyUniform_of_translation_slope ha _ ν (ambientDerivative ν η)
    (fun t => μ (t₀ + t)) hslope
  filter_upwards [self_mem_nhdsWithin] with t ht0
  exact Complex.ofReal_ne_zero.mpr
    (by simpa only [mem_compl_iff, mem_singleton_iff] using ht0)

/-- Pointwise complex differentiability is a consequence of the proved local
uniform limit for the same original canonical family. -/
theorem normalizedSolution_complex_parameter_hasDerivAt
    (μ : ℂ → MeasurableBeltramiBall) {t₀ : ℂ} {η : Ambient}
    (hμ : HasDerivAt (fun t => (μ t).val) η t₀) (w : ℂ) :
    HasDerivAt (fun t => normalizedMap (μ t) w)
      (Quasiconformal.firstVariation (ambientDerivative (μ t₀) η)
        (normalizedMap (μ t₀) w)) t₀ := by
  have hlimit :=
    (normalizedSolution_complex_parameter_firstVariation μ hμ).tendstoLocallyUniformlyOn.tendsto_at
      (mem_univ w)
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hlimit

/-- The real derivative has the identical transported first-variation value. -/
theorem normalizedSolution_real_parameter_hasDerivAt
    (μ : ℝ → MeasurableBeltramiBall) {t₀ : ℝ} {η : Ambient}
    (hμ : HasDerivAt (fun t => (μ t).val) η t₀) (w : ℂ) :
    HasDerivAt (fun t => normalizedMap (μ t) w)
      (Quasiconformal.firstVariation (ambientDerivative (μ t₀) η)
        (normalizedMap (μ t₀) w)) t₀ := by
  have hlimit :=
    (normalizedSolution_real_parameter_firstVariation μ hμ).tendstoLocallyUniformlyOn.tendsto_at
      (mem_univ w)
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using hlimit

end LowDimensionalTopology.Geometry.Teichmuller.PlanarCoefficientTransport
