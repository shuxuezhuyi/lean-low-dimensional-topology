module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeGammaCoefficientTransport

/-!
# The genuine coefficient translation is differentiable throughout its unit ball

The center of differentiation is arbitrary, while the normalized QC map that
changes the coefficient coordinates remains fixed. A literal scalar secant
identity and a uniform quadratic remainder prove the full Banach derivative
in the original essential norm. The compatible derivative is obtained from
the actual closed deck-law subspace, rather than supplied as a hypothesis.

The normalized map, phase and coefficient convention use Wu Xiaobin's
Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0).
See `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- A scalar center and every nearby argument share one strict subunit bound. -/
def translationJointBound (ν : Ball Γ) (μ : Ambient) : ℝ :=
  max ‖ν.val.val‖ ((1 + ‖μ‖) / 2)

def translationCenterRadius (μ : Ambient) : ℝ := (1 - ‖μ‖) / 2

private theorem translationJointBound_nonneg (ν : Ball Γ) (μ : Ambient) :
    0 ≤ translationJointBound ν μ :=
  (norm_nonneg ν.val.val).trans (le_max_left _ _)

private theorem translationJointBound_lt_one (ν : Ball Γ) (μ : Ambient) (hμ : ‖μ‖ < 1) :
    translationJointBound ν μ < 1 := by
  exact max_lt (Ball.norm_lt_one ν) (by linarith)

private theorem translationJointBound_gap_pos (ν : Ball Γ) (μ : Ambient) (hμ : ‖μ‖ < 1) :
    0 < 1 - translationJointBound ν μ ^ 2 := by
  have hk0 := translationJointBound_nonneg ν μ
  have hk1 := translationJointBound_lt_one ν μ hμ
  nlinarith

private theorem norm_translation_numerator_le {a : ℂ} {k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (ha : ‖a‖ ≤ k) :
    ‖1 - conj a * a‖ ≤ 2 := by
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖conj a * a‖ := norm_sub_le _ _
    _ = 1 + ‖a‖ ^ 2 := by rw [norm_one, norm_mul, Complex.norm_conj, pow_two]
    _ ≤ 1 + k ^ 2 := by
      have hsq : ‖a‖ ^ 2 ≤ k ^ 2 := by
        simpa only [pow_two] using mul_le_mul ha ha (norm_nonneg a) hk0
      linarith [hsq]
    _ ≤ 2 := by nlinarith

/-- The exact secant remainder for the fixed complex fractional map. -/
private theorem fractional_center_remainder_eq (a b c ρ : ℂ)
    (hb : 1 - conj a * b ≠ 0) (hc : 1 - conj a * c ≠ 0) :
    (c - a) / (1 - conj a * c) * ρ -
        (b - a) / (1 - conj a * b) * ρ -
        ((1 - conj a * a) / (1 - conj a * b) ^ 2 * ρ) * (c - b) =
      ((1 - conj a * a) * conj a * (c - b) ^ 2 * ρ) /
        ((1 - conj a * c) * (1 - conj a * b) ^ 2) := by
  generalize hbdef : (1 - conj a * b) = B at *
  generalize hcdef : (1 - conj a * c) = C at *
  field_simp [hb, hc]; rw [← hbdef, ← hcdef]; ring

/-- Uniform quadratic control at an arbitrary center of the scalar coefficient disk. -/
theorem fractional_center_remainder_le {a b c ρ : ℂ} {k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (ha : ‖a‖ ≤ k) (hb : ‖b‖ ≤ k)
    (hc : ‖c‖ ≤ k) (hρ : ‖ρ‖ ≤ 1) :
    ‖(c - a) / (1 - conj a * c) * ρ -
        (b - a) / (1 - conj a * b) * ρ -
        ((1 - conj a * a) / (1 - conj a * b) ^ 2 * ρ) * (c - b)‖ ≤
      (2 / (1 - k ^ 2) ^ 3) * ‖c - b‖ ^ 2 := by
  have hd : 0 < 1 - k ^ 2 := by nlinarith
  have hdb := LiZhongQC.ahT_denom_ge hk0 hb ha
  have hdc := LiZhongQC.ahT_denom_ge hk0 hc ha
  have hbn : 1 - conj a * b ≠ 0 := norm_pos_iff.mp (hd.trans_le hdb)
  have hcn : 1 - conj a * c ≠ 0 := norm_pos_iff.mp (hd.trans_le hdc)
  rw [fractional_center_remainder_eq a b c ρ hbn hcn]
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_conj]
  have hnum : ‖1 - conj a * a‖ * ‖a‖ * ‖c - b‖ ^ 2 * ‖ρ‖ ≤ 2 * ‖c - b‖ ^ 2 := by
    have ha1 : ‖a‖ ≤ 1 := ha.trans hk1.le
    have hna : ‖1 - conj a * a‖ * ‖a‖ ≤ 2 := by
      calc
        _ ≤ 2 * 1 := mul_le_mul (norm_translation_numerator_le hk0 hk1 ha)
          ha1 (norm_nonneg _) (by norm_num)
        _ = 2 := mul_one _
    calc
      _ ≤ (2 * ‖c - b‖ ^ 2) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hna (sq_nonneg _)) hρ
          (norm_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _))
      _ = _ := mul_one _
  have hden : (1 - k ^ 2) ^ 3 ≤
      ‖1 - conj a * c‖ * ‖1 - conj a * b‖ ^ 2 := by
    calc
      _ = (1 - k ^ 2) * (1 - k ^ 2) ^ 2 := by ring
      _ ≤ _ := mul_le_mul hdc (pow_le_pow_left₀ hd.le hdb 2)
        (sq_nonneg _) (norm_nonneg _)
  calc
    _ ≤ (2 * ‖c - b‖ ^ 2) / (1 - k ^ 2) ^ 3 :=
      div_le_div₀ (mul_nonneg (by norm_num) (sq_nonneg _)) hnum (pow_pos hd 3) hden
    _ = _ := by ring

/-- The literal derivative weight at the arbitrary actual ambient coefficient. -/
def translationCenterWeight (ν : Ball Γ) (μ : Ambient) (z : ℍ) : ℂ :=
  (1 - conj (ν.val.val z) * ν.val.val z) /
    (1 - conj (ν.val.val z) * μ z) ^ 2 * derivativePhase ν z

theorem translationCenterWeight_aestronglyMeasurable (ν : Ball Γ) (μ : Ambient) :
    AEStronglyMeasurable (translationCenterWeight ν μ) (volume : Measure ℍ) := by
  have hn := Lp.aestronglyMeasurable ν.val.val
  have hm := Lp.aestronglyMeasurable μ
  exact ((aestronglyMeasurable_const.sub
      ((Complex.continuous_conj.comp_aestronglyMeasurable hn).mul hn)).div₀
    ((aestronglyMeasurable_const.sub
      ((Complex.continuous_conj.comp_aestronglyMeasurable hn).mul hm)).pow 2)).mul
    (derivativePhase_aestronglyMeasurable ν)

theorem norm_translationCenterWeight_ae_le
    (ν : Ball Γ) (μ : Ambient) (hμ : ‖μ‖ < 1) :
    ∀ᵐ z : ℍ ∂volume, ‖translationCenterWeight ν μ z‖ ≤
      2 / (1 - translationJointBound ν μ ^ 2) ^ 2 := by
  let k := translationJointBound ν μ
  have hk0 := translationJointBound_nonneg ν μ
  have hk1 := translationJointBound_lt_one ν μ hμ
  have hd : 0 < 1 - k ^ 2 := translationJointBound_gap_pos ν μ hμ
  have hμk : ‖μ‖ ≤ k := by
    apply le_trans (show ‖μ‖ ≤ (1 + ‖μ‖) / 2 by linarith)
    exact le_max_right _ _
  filter_upwards [lpInfinity_norm_ae_le ν.val.val, lpInfinity_norm_ae_le μ] with z hn hm
  have hn' := hn.trans (le_max_left ‖ν.val.val‖ ((1 + ‖μ‖) / 2))
  have hm' := hm.trans hμk
  have hden := LiZhongQC.ahT_denom_ge hk0 hm' hn'
  rw [translationCenterWeight, norm_mul, norm_div, norm_pow]
  calc
    _ ≤ (2 / (1 - k ^ 2) ^ 2) * 1 := by
      apply mul_le_mul
      · exact div_le_div₀ (by norm_num) (norm_translation_numerator_le hk0 hk1 hn')
          (pow_pos hd 2) (pow_le_pow_left₀ hd.le hden 2)
      · exact norm_derivativePhase_le ν z
      · exact norm_nonneg _
      · exact div_nonneg (by norm_num) (sq_nonneg _)
    _ = _ := mul_one _

/-- The real all-direction derivative, with the same actual normalized inverse pullback. -/
def ambientTranslationDerivativeAt (ν : Ball Γ) (μ : Ambient) (hμ : ‖μ‖ < 1) :
    Ambient →L[ℂ] Ambient :=
  (quasiPullback (normalizedUpperEquiv ν).symm
    (normalizedUpperEquiv_symm_quasiMeasurePreserving ν)).comp
    (boundedMultiply (translationCenterWeight ν μ)
      (translationCenterWeight_aestronglyMeasurable ν μ)
      (C := 2 / (1 - translationJointBound ν μ ^ 2) ^ 2)
      (div_nonneg (by norm_num) (sq_nonneg _))
      (norm_translationCenterWeight_ae_le ν μ hμ))

theorem ambientTranslationDerivativeAt_coe_ae
    (ν : Ball Γ) (μ : Ambient) (hμ : ‖μ‖ < 1) (h : Ambient) :
    ambientTranslationDerivativeAt ν μ hμ h =ᵐ[volume] fun z =>
      translationCenterWeight ν μ ((normalizedUpperEquiv ν).symm z) *
        h ((normalizedUpperEquiv ν).symm z) := by
  filter_upwards [quasiPullback_coe_ae (normalizedUpperEquiv ν).symm
      (normalizedUpperEquiv_symm_quasiMeasurePreserving ν)
      (boundedMultiply (translationCenterWeight ν μ)
        (translationCenterWeight_aestronglyMeasurable ν μ)
        (C := 2 / (1 - translationJointBound ν μ ^ 2) ^ 2)
        (div_nonneg (by norm_num) (sq_nonneg _))
        (norm_translationCenterWeight_ae_le ν μ hμ) h),
    (normalizedUpperEquiv_symm_quasiMeasurePreserving ν).ae
      (boundedMultiply_coe_ae (translationCenterWeight ν μ)
        (translationCenterWeight_aestronglyMeasurable ν μ)
        (C := 2 / (1 - translationJointBound ν μ ^ 2) ^ 2)
        (div_nonneg (by norm_num) (sq_nonneg _))
        (norm_translationCenterWeight_ae_le ν μ hμ) h)] with z hp hm
  exact hp.trans hm

/-- The bound is uniform in every ambient direction in a genuine norm neighborhood. -/
theorem translation_center_quadratic_remainder (ν : Ball Γ) (μ : Ambient) (hμ : ‖μ‖ < 1)
    (h : Ambient) (hh : ‖h‖ < translationCenterRadius μ) :
    ‖translation ν (μ + h) - translation ν μ - ambientTranslationDerivativeAt ν μ hμ h‖ ≤
      (2 / (1 - translationJointBound ν μ ^ 2) ^ 3) * ‖h‖ ^ 2 := by
  let k := translationJointBound ν μ
  have hk0 := translationJointBound_nonneg ν μ
  have hk1 := translationJointBound_lt_one ν μ hμ
  have hμk : ‖μ‖ ≤ k := by
    apply le_trans (show ‖μ‖ ≤ (1 + ‖μ‖) / 2 by linarith)
    exact le_max_right _ _
  have hsumk : ‖μ + h‖ ≤ k := by
    apply (norm_add_le μ h).trans
    apply le_trans (show ‖μ‖ + ‖h‖ ≤ (1 + ‖μ‖) / 2 by
      unfold translationCenterRadius at hh
      linarith)
    exact le_max_right _ _
  have hraw : ∀ᵐ z : ℍ ∂volume,
      ‖rawTranslation ν (μ + h) z - rawTranslation ν μ z -
        translationCenterWeight ν μ z * h z‖ ≤ (2 / (1 - k ^ 2) ^ 3) * ‖h‖ ^ 2 := by
    filter_upwards [Lp.coeFn_add μ h, lpInfinity_norm_ae_le ν.val.val,
      lpInfinity_norm_ae_le μ, lpInfinity_norm_ae_le (μ + h), lpInfinity_norm_ae_le h]
      with z hadd hn hm hs hhz
    simp only [Pi.add_apply] at hadd
    have he := fractional_center_remainder_le hk0 hk1
      (hn.trans (le_max_left ‖ν.val.val‖ ((1 + ‖μ‖) / 2)))
      (hm.trans hμk) (hs.trans hsumk) (norm_derivativePhase_le ν z)
    have hdiff : (μ + h) z - μ z = h z := by rw [hadd]; ring
    change ‖rawTranslation ν (μ + h) z - rawTranslation ν μ z -
      translationCenterWeight ν μ z * ((μ + h) z - μ z)‖ ≤ _ at he
    rw [hdiff] at he
    exact he.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hhz 2)
      (div_nonneg (by norm_num) (pow_nonneg (translationJointBound_gap_pos ν μ hμ).le 3)))
  apply lpInfinity_norm_le_of_ae_bound _
    (mul_nonneg (div_nonneg (by norm_num)
      (pow_nonneg (translationJointBound_gap_pos ν μ hμ).le 3)) (sq_nonneg _))
  filter_upwards [Lp.coeFn_sub (translation ν (μ + h)) (translation ν μ),
    Lp.coeFn_sub (translation ν (μ + h) - translation ν μ)
      (ambientTranslationDerivativeAt ν μ hμ h),
    translation_coe_ae ν (μ + h) (hsumk.trans_lt hk1), translation_coe_ae ν μ hμ,
    ambientTranslationDerivativeAt_coe_ae ν μ hμ h,
    (normalizedUpperEquiv_symm_quasiMeasurePreserving ν).ae hraw]
    with z hsub hsub' hs hm hd hb
  simp only [Pi.sub_apply] at hsub hsub'
  rw [hsub', hsub, hs, hm, hd]
  exact hb

/-- The fixed normalized coefficient coordinate change is Fréchet differentiable at every point. -/
theorem hasFDerivAt_translation_at (ν : Ball Γ) (μ : Ambient) (hμ : ‖μ‖ < 1) :
    HasFDerivAt (translation ν) (ambientTranslationDerivativeAt ν μ hμ) μ := by
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  let C := 2 / (1 - translationJointBound ν μ ^ 2) ^ 3
  have hC : 0 < C := div_pos (by norm_num)
    (pow_pos (translationJointBound_gap_pos ν μ hμ) 3)
  have hr : 0 < min (translationCenterRadius μ) (ε / C) := by
    apply lt_min
    · unfold translationCenterRadius
      exact div_pos (sub_pos.mpr hμ) (by norm_num)
    · exact div_pos hε hC
  filter_upwards [Metric.ball_mem_nhds (0 : Ambient) hr] with h hh
  have hn := mem_ball_zero_iff.mp hh
  have hsmall := hn.trans_le (min_le_left (translationCenterRadius μ) (ε / C))
  have hbound : C * ‖h‖ ≤ ε := by
    have ht := (lt_div_iff₀ hC).mp (hn.trans_le (min_le_right (translationCenterRadius μ) (ε / C)))
    nlinarith
  exact (translation_center_quadratic_remainder ν μ hμ h hsmall).trans
    (by nlinarith [norm_nonneg h])

/-- All compatible directions retain the actual deformed deck equations. -/
theorem ambientTranslationDerivativeAt_mem_compatible
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) (h : Space Γ) :
    ambientTranslationDerivativeAt ν μ.val.val (Ball.norm_lt_one μ) h.val ∈
      compatibleSubmodule (deformedGroup hΓ ν) := by
  have hd := (hasFDerivAt_translation_at ν μ.val.val (Ball.norm_lt_one μ)).comp μ.val
    ((compatibleSubmodule Γ).subtypeL.hasFDerivAt)
  have hlim := hd.lim h (tendsto_norm_cobounded_atTop (E := ℂ))
  apply (isClosed_compatibleSubmodule (deformedGroup hΓ ν)).mem_of_tendsto hlim
  apply Eventually.of_forall
  intro c
  exact (compatibleSubmodule (deformedGroup hΓ ν)).smul_mem c
    ((compatibleSubmodule (deformedGroup hΓ ν)).sub_mem
      (translation_mem_compatible hΓ ν (μ.val + c⁻¹ • h))
      (translation_mem_compatible hΓ ν μ.val))

/-- Restrict the literal derivative to the actual compatible closed subspaces. -/
def gammaTranslationDerivativeAt (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) :
    Space Γ →L[ℂ] Space (deformedGroup hΓ ν) :=
  ((ambientTranslationDerivativeAt ν μ.val.val (Ball.norm_lt_one μ)).domRestrict
    (compatibleSubmodule Γ)).codRestrict (compatibleSubmodule (deformedGroup hΓ ν))
      (ambientTranslationDerivativeAt_mem_compatible hΓ ν μ)

/-- The actual compatible map is differentiable at EVERY original subunit coefficient. -/
theorem hasFDerivAt_gammaTranslation_at (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) :
    HasFDerivAt (gammaTranslation hΓ ν) (gammaTranslationDerivativeAt hΓ ν μ) μ.val := by
  have hd := (hasFDerivAt_translation_at ν μ.val.val (Ball.norm_lt_one μ)).comp μ.val
    ((compatibleSubmodule Γ).subtypeL.hasFDerivAt)
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  have he := Asymptotics.isLittleO_iff.mp (hasFDerivAt_iff_isLittleO_nhds_zero.mp hd) hε
  filter_upwards [he] with h hh
  change ‖translation ν ((μ.val + h).val) - translation ν μ.val.val -
    ambientTranslationDerivativeAt ν μ.val.val (Ball.norm_lt_one μ) h.val‖ ≤ ε * ‖h‖
  exact hh

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
