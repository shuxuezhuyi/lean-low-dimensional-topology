module

public import LowDimensionalTopology.Geometry.Teichmuller.PlanarCoefficientTransport
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Fréchet coefficient translation on the full planar L-infinity ball

This map uses the actual normalized plane solution at the given base class.
The literal fractional coefficient followed by its actual inverse pullback
has a uniform quadratic remainder in the original full-plane essential norm.
Thus arbitrary norm-differentiable parameter families can use the chain rule;
no pointwise holomorphic choice of representatives is required.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.PlanarCoefficientTransport

open NormalizedCoefficientTransport
  (fractionalRemainderConstant fractionalRemainderConstant_pos fractional_remainder_le)

/-- The fractional coefficient before the actual inverse pullback. -/
def rawTranslation (ν : MeasurableBeltramiBall) (μ : Ambient) (z : ℂ) : ℂ :=
  (μ z - ν.val z) / (1 - conj (ν.val z) * μ z) * derivativePhase ν z

theorem rawTranslation_aestronglyMeasurable (ν : MeasurableBeltramiBall) (μ : Ambient) :
    AEStronglyMeasurable (rawTranslation ν μ) (volume : Measure ℂ) := by
  have hm := Lp.aestronglyMeasurable μ
  have hn := Lp.aestronglyMeasurable ν.val
  exact ((hm.sub hn).div₀ (aestronglyMeasurable_const.sub
    ((Complex.continuous_conj.comp_aestronglyMeasurable hn).mul hm))).mul
      (derivativePhase_aestronglyMeasurable ν)

theorem rawTranslation_memLp (ν : MeasurableBeltramiBall) (μ : Ambient) (hμ : ‖μ‖ < 1) :
    MemLp (rawTranslation ν μ) (⊤ : ℝ≥0∞) volume := by
  let k := max ‖ν.val‖ ‖μ‖
  have hk0 : 0 ≤ k := (norm_nonneg ν.val).trans (le_max_left _ _)
  have hk1 : k < 1 := max_lt (MeasurableBeltramiBall.norm_lt_one ν) hμ
  apply memLp_top_of_bound (rawTranslation_aestronglyMeasurable ν μ)
    ((‖μ‖ + ‖ν.val‖) / (1 - k ^ 2))
  filter_upwards [lpInfinity_norm_ae_le μ, lpInfinity_norm_ae_le ν.val] with z hm hn
  exact LiZhongQC.ahT_frac_le hk0 hk1 (hm.trans (le_max_right _ _))
    (hn.trans (le_max_left _ _)) (norm_derivativePhase_le ν z)
    ((norm_sub_le _ _).trans (add_le_add hm hn))

/-- The actual class of the fractional coefficient. -/
def rawTranslationValue (ν : MeasurableBeltramiBall) (μ : Ambient) (hμ : ‖μ‖ < 1) : Ambient :=
  (rawTranslation_memLp ν μ hμ).toLp (rawTranslation ν μ)

theorem rawTranslationValue_coe_ae (ν : MeasurableBeltramiBall) (μ : Ambient) (hμ : ‖μ‖ < 1) :
    rawTranslationValue ν μ hμ =ᵐ[volume] rawTranslation ν μ :=
  (rawTranslation_memLp ν μ hμ).coeFn_toLp

/-- The literal normalized-QC translation on the coefficient ball, extended by zero. -/
def translation (ν : MeasurableBeltramiBall) (μ : Ambient) : Ambient := by
  classical
  exact if hμ : ‖μ‖ < 1 then
    quasiPullback (normalizedEquiv ν).symm
      (normalizedEquiv_symm_quasiMeasurePreserving ν) (rawTranslationValue ν μ hμ)
  else 0

theorem translation_coe_ae (ν : MeasurableBeltramiBall) (μ : Ambient) (hμ : ‖μ‖ < 1) :
    translation ν μ =ᵐ[volume]
      fun z => rawTranslation ν μ ((normalizedEquiv ν).symm z) := by
  rw [translation, dite_eq_left hμ]
  filter_upwards [quasiPullback_coe_ae (normalizedEquiv ν).symm
    (normalizedEquiv_symm_quasiMeasurePreserving ν) (rawTranslationValue ν μ hμ),
    (normalizedEquiv_symm_quasiMeasurePreserving ν).ae
      (rawTranslationValue_coe_ae ν μ hμ)] with z hp hr
  exact hp.trans hr

theorem translation_base (ν : MeasurableBeltramiBall) : translation ν ν.val = 0 := by
  apply Lp.ext
  filter_upwards [translation_coe_ae ν ν.val (MeasurableBeltramiBall.norm_lt_one ν),
    (Lp.coeFn_zero (E := ℂ) (p := (⊤ : ℝ≥0∞)) (μ := (volume : Measure ℂ)))]
      with z hz hzero
  simp only [Pi.zero_apply] at hzero
  rw [hzero]
  simpa only [rawTranslation, sub_self, zero_div, zero_mul] using hz

/-- This is the genuine coefficient of composition by the fixed actual inverse. -/
theorem translation_eq_ahQuot_ae (ν μ : MeasurableBeltramiBall) :
    translation ν μ.val =ᵐ[volume]
      LiZhongQC.ahQuot μ.val ν.val (normalizedMap ν) := by
  filter_upwards [translation_coe_ae ν μ.val (MeasurableBeltramiBall.norm_lt_one μ)]
    with z hz
  simpa only [LiZhongQC.ahQuot, invFunOn_normalizedMap ν, rawTranslation,
    derivativePhase, normalizedEquiv, Homeomorph.coe_symm_toEquiv] using hz

/-- The coefficient translation belongs to the actual normalized composite map,
not merely to an unrelated formal fractional expression. -/
theorem translation_normalized_composite (ν μ : MeasurableBeltramiBall) :
    LiZhongQC.IsNormalizedSolution
      ((normalizedMap μ) ∘ (normalizedMap ν).symm) (translation ν μ.val) := by
  let k := max ‖μ.val‖ ‖ν.val‖
  have hk0 : 0 ≤ k := (norm_nonneg μ.val).trans (le_max_left _ _)
  have hk1 : k < 1 := max_lt (MeasurableBeltramiBall.norm_lt_one μ)
    (MeasurableBeltramiBall.norm_lt_one ν)
  have hμ : LiZhongQC.IsBeltramiCoeff μ.val univ k := by
    refine ⟨(MeasurableBeltramiSpace.isBeltramiCoeff μ.val).1, ?_⟩
    filter_upwards [(MeasurableBeltramiSpace.isBeltramiCoeff μ.val).2] with z hz
    exact hz.trans (le_max_left _ _)
  have hν : LiZhongQC.IsBeltramiCoeff ν.val univ k := by
    refine ⟨(MeasurableBeltramiSpace.isBeltramiCoeff ν.val).1, ?_⟩
    filter_upwards [(MeasurableBeltramiSpace.isBeltramiCoeff ν.val).2] with z hz
    exact hz.trans (le_max_right _ _)
  have hc := (LiZhongQC.ah_quotient hk0 hk1 hμ hν
    (MeasurableBeltramiBall.normalizedSolution_spec μ).1
    (MeasurableBeltramiBall.normalizedSolution_spec ν).1).1
  rw [invFunOn_normalizedMap ν] at hc
  exact (Quasiconformal.isNormalizedSolution_congr_ae
    (translation_eq_ahQuot_ae ν μ)).2 hc

/-- A fixed scalar disk remains strictly inside the original coefficient ball. -/
def translationRadius (ν : MeasurableBeltramiBall) : ℝ := (1 - ‖ν.val‖) / 2

def translationLocalBound (ν : MeasurableBeltramiBall) : ℝ := (1 + ‖ν.val‖) / 2

theorem translationRadius_pos (ν : MeasurableBeltramiBall) : 0 < translationRadius ν := by
  have hν := MeasurableBeltramiBall.norm_lt_one ν
  unfold translationRadius
  linarith

theorem translationLocalBound_nonneg (ν : MeasurableBeltramiBall) : 0 ≤ translationLocalBound ν := by
  unfold translationLocalBound
  positivity

theorem translationLocalBound_lt_one (ν : MeasurableBeltramiBall) : translationLocalBound ν < 1 := by
  have hν := MeasurableBeltramiBall.norm_lt_one ν
  unfold translationLocalBound
  linarith

theorem norm_add_lt_translationLocalBound (ν : MeasurableBeltramiBall) (h : Ambient)
    (hh : ‖h‖ < translationRadius ν) :
    ‖ν.val + h‖ < translationLocalBound ν := by
  have hn := norm_add_le ν.val h
  unfold translationRadius at hh
  unfold translationLocalBound
  linarith

/-- A uniform quadratic bound in the actual L-infinity norm, for every Banach direction. -/
theorem translation_quadratic_remainder (ν : MeasurableBeltramiBall) (h : Ambient)
    (hh : ‖h‖ < translationRadius ν) :
    ‖translation ν (ν.val + h) - ambientDerivative ν h‖ ≤
      fractionalRemainderConstant (translationLocalBound ν) * ‖h‖ ^ 2 := by
  let μ : Ambient := ν.val + h
  let k := translationLocalBound ν
  have hk0 : 0 ≤ k := translationLocalBound_nonneg ν
  have hk1 : k < 1 := translationLocalBound_lt_one ν
  have hμk : ‖μ‖ < k := norm_add_lt_translationLocalBound ν h hh
  have hνk : ‖ν.val‖ ≤ k := by
    have hν := MeasurableBeltramiBall.norm_lt_one ν
    unfold k translationLocalBound
    linarith
  have hraw : ∀ᵐ z : ℂ ∂volume,
      ‖rawTranslation ν μ z - derivativeWeight ν z * h z‖ ≤
        fractionalRemainderConstant k * ‖h‖ ^ 2 := by
    filter_upwards [Lp.coeFn_add ν.val h, lpInfinity_norm_ae_le μ,
      lpInfinity_norm_ae_le ν.val, lpInfinity_norm_ae_le h] with z hadd hm hn hhz
    simp only [Pi.add_apply] at hadd
    have hdiff : μ z - ν.val z = h z := by rw [hadd]; ring
    have he := fractional_remainder_le hk0 hk1 (hm.trans hμk.le) (hn.trans hνk)
      (norm_derivativePhase_le ν z)
    have hlinear : (μ z - ν.val z) / (1 - conj (ν.val z) * ν.val z) *
        derivativePhase ν z = derivativeWeight ν z * h z := by
      rw [hdiff]
      unfold derivativeWeight coefficientDenominator
      ring
    rw [hlinear] at he
    apply he.trans
    rw [hdiff]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hhz 2) (fractionalRemainderConstant_pos hk0 hk1).le
  apply lpInfinity_norm_le_of_ae_bound _
    (mul_nonneg (fractionalRemainderConstant_pos hk0 hk1).le (sq_nonneg _))
  filter_upwards [Lp.coeFn_sub (translation ν μ) (ambientDerivative ν h),
    translation_coe_ae ν μ (hμk.trans hk1), ambientDerivative_weighted_coe_ae ν h,
    (normalizedEquiv_symm_quasiMeasurePreserving ν).ae hraw] with z hsub ht hd hb
  simp only [Pi.sub_apply] at hsub
  rw [hsub, ht, hd]
  exact hb

/-- The actual nonzero normalized coefficient translation has its true Banach derivative. -/
theorem hasFDerivAt_translation (ν : MeasurableBeltramiBall) :
    HasFDerivAt (translation ν) (ambientDerivative ν) ν.val := by
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  let C := fractionalRemainderConstant (translationLocalBound ν)
  have hC : 0 < C := fractionalRemainderConstant_pos
    (translationLocalBound_nonneg ν) (translationLocalBound_lt_one ν)
  have hr : 0 < min (translationRadius ν) (ε / C) :=
    lt_min (translationRadius_pos ν) (div_pos hε hC)
  filter_upwards [Metric.ball_mem_nhds (0 : Ambient) hr] with h hh
  have hn := mem_ball_zero_iff.mp hh
  have hsmall : ‖h‖ < translationRadius ν := hn.trans_le (min_le_left _ _)
  have hbound : C * ‖h‖ ≤ ε := by
    have hlt := (lt_div_iff₀ hC).mp (hn.trans_le (min_le_right _ _))
    nlinarith
  rw [translation_base, sub_zero]
  exact (translation_quadratic_remainder ν h hsmall).trans
    (by nlinarith [norm_nonneg h])

/-- Any complex norm-differentiable family uses the genuine full-space chain rule. -/
theorem hasFDerivAt_translation_comp {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ν : MeasurableBeltramiBall) {f : E → Ambient} {f' : E →L[ℂ] Ambient} {x : E}
    (hf : HasFDerivAt f f' x) (hx : f x = ν.val) :
    HasFDerivAt (translation ν ∘ f) ((ambientDerivative ν).comp f') x := by
  have ht := hasFDerivAt_translation ν
  rw [← hx] at ht
  exact ht.comp x hf

/-- Real norm-differentiable families are covered by restriction of scalars. -/
theorem hasFDerivAt_translation_comp_real {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : MeasurableBeltramiBall) {f : E → Ambient} {f' : E →L[ℝ] Ambient} {x : E}
    (hf : HasFDerivAt f f' x) (hx : f x = ν.val) :
    HasFDerivAt (translation ν ∘ f)
      (((ambientDerivative ν).restrictScalars ℝ).comp f') x := by
  have ht := (hasFDerivAt_translation ν).restrictScalars ℝ
  rw [← hx] at ht
  exact ht.comp x hf

end LowDimensionalTopology.Geometry.Teichmuller.PlanarCoefficientTransport
