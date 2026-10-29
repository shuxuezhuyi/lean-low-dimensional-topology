module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientTransport
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The genuine nonzero coefficient translation and its Banach derivative

The nonlinear map is the literal fractional coefficient formula followed by
the inverse of the actual normalized quasiconformal map. It acts on the
original hyperbolic L-infinity classes. A uniform quadratic remainder proves
its true Fréchet derivative at the original base coefficient, in every
direction of that same Banach space.

The scalar fractional estimate and quasiconformal composition formula reuse
Wu Xiaobin's LiZhongQC source, Apache-2.0, fixed upstream commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- The scalar remainder constant, with an intentionally nonoptimal positive bound. -/
def fractionalRemainderConstant (k : ℝ) : ℝ :=
  k / (1 - k ^ 2) ^ 2 + 1 / (1 - k ^ 2)

theorem fractionalRemainderConstant_pos {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) :
    0 < fractionalRemainderConstant k := by
  have hd : 0 < 1 - k ^ 2 := by nlinarith
  unfold fractionalRemainderConstant
  positivity

/-- The same complex fractional formula has a uniform quadratic remainder. -/
theorem fractional_remainder_le {a b ρ : ℂ} {k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (ha : ‖a‖ ≤ k) (hb : ‖b‖ ≤ k)
    (hρ : ‖ρ‖ ≤ 1) :
    ‖(a - b) / (1 - conj b * a) * ρ - (a - b) / (1 - conj b * b) * ρ‖ ≤
      fractionalRemainderConstant k * ‖a - b‖ ^ 2 := by
  by_cases hu : a - b = 0
  · simp only [hu, zero_div, zero_mul, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, le_refl]
  let s : ℂ := (‖a - b‖ : ℝ)
  have hs : s ≠ 0 := by
    dsimp only [s]
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu)
  have hns : ‖s‖ = ‖a - b‖ := by
    simp only [s, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hsm : s * ((a - b) / s) = a - b := by field_simp [hs]
  have hlinear : s * (((a - b) / s) / (1 - conj b * b) * ρ) =
      (a - b) / (1 - conj b * b) * ρ := by
    calc
      _ = (s * ((a - b) / s)) / (1 - conj b * b) * ρ := by ring
      _ = _ := by rw [hsm]
  have he := LiZhongQC.ahT_quot_second (m := (a - b) / s) (s := s) (C := 1)
    hk0 hk1 ha hb hρ (by rw [hns, one_mul])
    (by rw [hsm, sub_self, norm_zero]; positivity)
  simpa only [hlinear, hns, one_pow, mul_one, one_mul, fractionalRemainderConstant] using he

/-- The fractional coefficient before the actual inverse pullback. -/
def rawTranslation (ν : Ball Γ) (μ : Ambient) (z : ℍ) : ℂ :=
  (μ z - ν.val.val z) / (1 - conj (ν.val.val z) * μ z) * derivativePhase ν z

theorem rawTranslation_aestronglyMeasurable (ν : Ball Γ) (μ : Ambient) :
    AEStronglyMeasurable (rawTranslation ν μ) (volume : Measure ℍ) := by
  have hm := Lp.aestronglyMeasurable μ
  have hn := Lp.aestronglyMeasurable ν.val.val
  exact ((hm.sub hn).div₀ (aestronglyMeasurable_const.sub
    ((Complex.continuous_conj.comp_aestronglyMeasurable hn).mul hm))).mul
      (derivativePhase_aestronglyMeasurable ν)

theorem rawTranslation_memLp (ν : Ball Γ) (μ : Ambient) (hμ : ‖μ‖ < 1) :
    MemLp (rawTranslation ν μ) (⊤ : ℝ≥0∞) volume := by
  let k := max ‖ν.val.val‖ ‖μ‖
  have hk0 : 0 ≤ k := (norm_nonneg ν.val.val).trans (le_max_left _ _)
  have hk1 : k < 1 := max_lt (Ball.norm_lt_one ν) hμ
  apply memLp_top_of_bound (rawTranslation_aestronglyMeasurable ν μ)
    ((‖μ‖ + ‖ν.val.val‖) / (1 - k ^ 2))
  filter_upwards [lpInfinity_norm_ae_le μ, lpInfinity_norm_ae_le ν.val.val] with z hm hn
  exact LiZhongQC.ahT_frac_le hk0 hk1 (hm.trans (le_max_right _ _))
    (hn.trans (le_max_left _ _)) (norm_derivativePhase_le ν z)
    ((norm_sub_le _ _).trans (add_le_add hm hn))

/-- The actual class of the fractional coefficient. -/
def rawTranslationValue (ν : Ball Γ) (μ : Ambient) (hμ : ‖μ‖ < 1) : Ambient :=
  (rawTranslation_memLp ν μ hμ).toLp (rawTranslation ν μ)

theorem rawTranslationValue_coe_ae (ν : Ball Γ) (μ : Ambient) (hμ : ‖μ‖ < 1) :
    rawTranslationValue ν μ hμ =ᵐ[volume] rawTranslation ν μ :=
  (rawTranslation_memLp ν μ hμ).coeFn_toLp

/-- The literal normalized-QC translation on the coefficient ball, extended by zero. -/
def translation (ν : Ball Γ) (μ : Ambient) : Ambient := by
  classical
  exact if hμ : ‖μ‖ < 1 then
    quasiPullback (normalizedUpperEquiv ν).symm
      (normalizedUpperEquiv_symm_quasiMeasurePreserving ν) (rawTranslationValue ν μ hμ)
  else 0

theorem translation_coe_ae (ν : Ball Γ) (μ : Ambient) (hμ : ‖μ‖ < 1) :
    translation ν μ =ᵐ[volume]
      fun z => rawTranslation ν μ ((normalizedUpperEquiv ν).symm z) := by
  rw [translation, dite_eq_left hμ]
  filter_upwards [quasiPullback_coe_ae (normalizedUpperEquiv ν).symm
    (normalizedUpperEquiv_symm_quasiMeasurePreserving ν) (rawTranslationValue ν μ hμ),
    (normalizedUpperEquiv_symm_quasiMeasurePreserving ν).ae
      (rawTranslationValue_coe_ae ν μ hμ)] with z hp hr
  exact hp.trans hr

theorem translation_base (ν : Ball Γ) : translation ν ν.val.val = 0 := by
  apply Lp.ext
  filter_upwards [translation_coe_ae ν ν.val.val (Ball.norm_lt_one ν),
    (Lp.coeFn_zero (E := ℂ) (p := (⊤ : ℝ≥0∞)) (μ := (volume : Measure ℍ)))]
      with z hz hzero
  simp only [Pi.zero_apply] at hzero
  rw [hzero]
  simpa only [rawTranslation, sub_self, zero_div, zero_mul] using hz

/-- On every actual compatible coefficient ball, the fractional map is precisely
the coefficient of composition with the inverse normalized quasiconformal map. -/
theorem translation_eq_actual_composite_ae (ν μ : Ball Γ) :
    translation ν μ.val.val =ᵐ[volume] fun z : ℍ =>
      LiZhongQC.translatedBeltrami (planeRepresentative ν.val.val)
        (planeRepresentative μ.val.val) z := by
  obtain ⟨_, hν, _, _, _, _, _, _⟩ := normalizedMap_spec ν
  obtain ⟨_, hμ, _, _, _, _, _, _⟩ := normalizedMap_spec μ
  have hc := LiZhongQC.ahQ_comp_inv_dilatation hμ hν
  rw [Measure.restrict_univ] at hc
  have hsource : ∀ᵐ z : ℍ ∂volume,
      LiZhongQC.translatedBeltrami (planeRepresentative ν.val.val)
          (planeRepresentative μ.val.val) (normalizedUpperEquiv ν z) =
        rawTranslation ν μ.val.val z := by
    filter_upwards [ae_plane_iff.mp (ae_restrict_of_ae hc),
      normalizedMap_dilatation_ae ν, normalizedMap_dilatation_ae μ] with z hz hn hm
    change LiZhongQC.upperHalf.indicator
        (LiZhongQC.complexDilatation (normalizedMap μ ∘ normalizedInverse ν))
        (normalizedMap ν z) = rawTranslation ν μ.val.val z
    rw [indicator_of_mem (normalizedMap_mapsTo_upper ν z.im_pos), normalizedInverse, hz, hm, hn]
    rfl
  filter_upwards [translation_coe_ae ν μ.val.val (Ball.norm_lt_one μ),
    (normalizedUpperEquiv_symm_quasiMeasurePreserving ν).ae hsource] with z ht hs
  rw [(normalizedUpperEquiv ν).apply_symm_apply] at hs
  exact ht.trans hs.symm

/-- A fixed scalar disk remains strictly inside the original coefficient ball. -/
def translationRadius (ν : Ball Γ) : ℝ := (1 - ‖ν.val.val‖) / 2

def translationLocalBound (ν : Ball Γ) : ℝ := (1 + ‖ν.val.val‖) / 2

theorem translationRadius_pos (ν : Ball Γ) : 0 < translationRadius ν := by
  have hν : ‖ν.val.val‖ < 1 := by
    rw [ClosedSubmodule.norm_coe]
    exact Ball.norm_lt_one ν
  unfold translationRadius
  linarith

theorem translationLocalBound_nonneg (ν : Ball Γ) : 0 ≤ translationLocalBound ν := by
  unfold translationLocalBound
  positivity

theorem translationLocalBound_lt_one (ν : Ball Γ) : translationLocalBound ν < 1 := by
  have hν : ‖ν.val.val‖ < 1 := by
    rw [ClosedSubmodule.norm_coe]
    exact Ball.norm_lt_one ν
  unfold translationLocalBound
  linarith

theorem norm_add_lt_translationLocalBound (ν : Ball Γ) (h : Ambient)
    (hh : ‖h‖ < translationRadius ν) :
    ‖ν.val.val + h‖ < translationLocalBound ν := by
  have hn := norm_add_le ν.val.val h
  unfold translationRadius at hh
  unfold translationLocalBound
  linarith

/-- A uniform quadratic bound in the actual L-infinity norm, for every Banach direction. -/
theorem translation_quadratic_remainder (ν : Ball Γ) (h : Ambient)
    (hh : ‖h‖ < translationRadius ν) :
    ‖translation ν (ν.val.val + h) - ambientDerivative ν h‖ ≤
      fractionalRemainderConstant (translationLocalBound ν) * ‖h‖ ^ 2 := by
  let μ : Ambient := ν.val.val + h
  let k := translationLocalBound ν
  have hk0 : 0 ≤ k := translationLocalBound_nonneg ν
  have hk1 : k < 1 := translationLocalBound_lt_one ν
  have hμk : ‖μ‖ < k := norm_add_lt_translationLocalBound ν h hh
  have hνk : ‖ν.val.val‖ ≤ k := by
    have hν : ‖ν.val.val‖ < 1 := by
      rw [ClosedSubmodule.norm_coe]
      exact Ball.norm_lt_one ν
    unfold k translationLocalBound
    linarith
  have hraw : ∀ᵐ z : ℍ ∂volume,
      ‖rawTranslation ν μ z - derivativeWeight ν z * h z‖ ≤
        fractionalRemainderConstant k * ‖h‖ ^ 2 := by
    filter_upwards [Lp.coeFn_add ν.val.val h, lpInfinity_norm_ae_le μ,
      lpInfinity_norm_ae_le ν.val.val, lpInfinity_norm_ae_le h] with z hadd hm hn hhz
    simp only [Pi.add_apply] at hadd
    have hdiff : μ z - ν.val.val z = h z := by rw [hadd]; ring
    have he := fractional_remainder_le hk0 hk1 (hm.trans hμk.le) (hn.trans hνk)
      (norm_derivativePhase_le ν z)
    have hlinear : (μ z - ν.val.val z) / (1 - conj (ν.val.val z) * ν.val.val z) *
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
    (normalizedUpperEquiv_symm_quasiMeasurePreserving ν).ae hraw] with z hsub ht hd hb
  simp only [Pi.sub_apply] at hsub
  rw [hsub, ht, hd]
  exact hb

/-- The actual nonzero normalized coefficient translation has its true Banach derivative. -/
theorem hasFDerivAt_translation (ν : Ball Γ) :
    HasFDerivAt (translation ν) (ambientDerivative ν) ν.val.val := by
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

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
