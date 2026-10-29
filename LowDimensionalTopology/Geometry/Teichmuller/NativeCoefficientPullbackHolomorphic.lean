module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientTranslationHolomorphic
public import Mathlib.Tactic.LinearCombination

/-!
# The actual normalized coefficient pullback is differentiable on the entire ball

The inverse coefficient formula is derived from the independently defined
normalized QC composition and its genuine cancellation law. At an arbitrary
coefficient center, the same scalar fractional remainder proves a full
Fréchet derivative in the unchanged essential norm. Forward composition uses
only the actual normalized map's quasi-measure preservation.

The normalized maps and coefficient convention use Wu Xiaobin's
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

/-- The literal coefficient in the original coordinates, including its true inverse phase. -/
def pullbackIncrement (ν : Ball Γ) (κ : Ambient) (z : ℍ) : ℂ :=
  κ (normalizedUpperEquiv ν z) * conj (derivativePhase ν z)

private theorem pullbackIncrement_aestronglyMeasurable (ν : Ball Γ) (κ : Ambient) :
    AEStronglyMeasurable (pullbackIncrement ν κ) (volume : Measure ℍ) :=
  ((Lp.aestronglyMeasurable κ).comp_quasiMeasurePreserving
    (normalizedUpperEquiv_quasiMeasurePreserving ν)).mul
      (Complex.continuous_conj.comp_aestronglyMeasurable
        (derivativePhase_aestronglyMeasurable ν))

private theorem norm_pullbackIncrement_ae_le (ν : Ball Γ) (κ : Ambient) :
    ∀ᵐ z : ℍ ∂volume, ‖pullbackIncrement ν κ z‖ ≤ ‖κ‖ := by
  filter_upwards [(normalizedUpperEquiv_quasiMeasurePreserving ν).ae
    (lpInfinity_norm_ae_le κ)] with z hz
  rw [pullbackIncrement, norm_mul, Complex.norm_conj]
  exact (mul_le_mul hz (norm_derivativePhase_le ν z) (norm_nonneg _) (norm_nonneg κ)).trans_eq
    (mul_one _)

/-- The actual inverse fractional formula before passing to its a.e. class. -/
def rawPullback (ν : Ball Γ) (κ : Ambient) (z : ℍ) : ℂ :=
  (ν.val.val z + pullbackIncrement ν κ z) /
    (1 + conj (ν.val.val z) * pullbackIncrement ν κ z)

/-- Cancellation of the genuine normalized compositions proves the literal formula for EVERY
subunit input, rather than just for the small Ahlfors-Weill section. -/
theorem pullback_coe_ae (ν : Ball Γ) (κ : Ambient) (hκ : ‖κ‖ < 1) :
    pullback ν κ =ᵐ[volume] rawPullback ν κ := by
  let μ := pullback ν κ
  have hμ : ‖μ‖ < 1 := norm_pullback_lt_one ν κ
  have ht : ∀ᵐ z : ℍ ∂volume,
      rawTranslation ν μ z = κ (normalizedUpperEquiv ν z) := by
    have he := (normalizedUpperEquiv_quasiMeasurePreserving ν).ae
      (translation_coe_ae ν μ hμ)
    filter_upwards [he] with z hz
    rw [translation_pullback ν κ hκ, (normalizedUpperEquiv ν).symm_apply_apply] at hz
    exact hz.symm
  filter_upwards [ht, norm_derivativePhase_ae ν, lpInfinity_norm_ae_le μ,
    lpInfinity_norm_ae_le ν.val.val, norm_pullbackIncrement_ae_le ν κ] with z ht hp hm hn hi
  have hd : 1 - conj (ν.val.val z) * μ z ≠ 0 :=
    LiZhongQC.b33_t_one_sub_ne (hn.trans_lt (Ball.norm_lt_one ν)) (hm.trans_lt hμ)
  have hρ : derivativePhase ν z * conj (derivativePhase ν z) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp]
    norm_num
  have he : (μ z - ν.val.val z) / (1 - conj (ν.val.val z) * μ z) =
      pullbackIncrement ν κ z := by
    have hh := congrArg (fun a : ℂ => a * conj (derivativePhase ν z)) ht
    change ((μ z - ν.val.val z) / (1 - conj (ν.val.val z) * μ z) *
      derivativePhase ν z) * conj (derivativePhase ν z) = pullbackIncrement ν κ z at hh
    rwa [mul_assoc, hρ, mul_one] at hh
  have hnew : 1 + conj (ν.val.val z) * pullbackIncrement ν κ z ≠ 0 := by
    have hh := LiZhongQC.b33_t_one_sub_ne
      (show ‖-(ν.val.val z)‖ < 1 by rw [norm_neg]; exact hn.trans_lt (Ball.norm_lt_one ν))
      (hi.trans_lt hκ)
    simpa only [map_neg, neg_mul, sub_neg_eq_add] using hh
  have hmul := (div_eq_iff hd).mp he
  change μ z = rawPullback ν κ z
  rw [rawPullback]
  apply (eq_div_iff hnew).mpr
  linear_combination hmul

private theorem pullbackJointBound_nonneg (ν : Ball Γ) (κ : Ambient) :
    0 ≤ translationJointBound ν κ :=
  (norm_nonneg ν.val.val).trans (le_max_left _ _)

private theorem pullbackJointBound_lt_one (ν : Ball Γ) (κ : Ambient) (hκ : ‖κ‖ < 1) :
    translationJointBound ν κ < 1 :=
  max_lt (Ball.norm_lt_one ν) (by linarith)

private theorem pullbackJointBound_gap_pos (ν : Ball Γ) (κ : Ambient) (hκ : ‖κ‖ < 1) :
    0 < 1 - translationJointBound ν κ ^ 2 := by
  have hk0 := pullbackJointBound_nonneg ν κ
  have hk1 := pullbackJointBound_lt_one ν κ hκ
  nlinarith

/-- The literal derivative multiplier at an arbitrary coefficient center. -/
def pullbackCenterWeight (ν : Ball Γ) (κ : Ambient) (z : ℍ) : ℂ :=
  (1 - conj (ν.val.val z) * ν.val.val z) /
      (1 + conj (ν.val.val z) * pullbackIncrement ν κ z) ^ 2 *
    conj (derivativePhase ν z)

theorem pullbackCenterWeight_aestronglyMeasurable (ν : Ball Γ) (κ : Ambient) :
    AEStronglyMeasurable (pullbackCenterWeight ν κ) (volume : Measure ℍ) := by
  have hn := Lp.aestronglyMeasurable ν.val.val
  exact ((coefficientDenominator_aestronglyMeasurable ν).div₀
    ((aestronglyMeasurable_const.add
      ((Complex.continuous_conj.comp_aestronglyMeasurable hn).mul
        (pullbackIncrement_aestronglyMeasurable ν κ))).pow 2)).mul
    (Complex.continuous_conj.comp_aestronglyMeasurable (derivativePhase_aestronglyMeasurable ν))

theorem norm_pullbackCenterWeight_ae_le
    (ν : Ball Γ) (κ : Ambient) (hκ : ‖κ‖ < 1) :
    ∀ᵐ z : ℍ ∂volume, ‖pullbackCenterWeight ν κ z‖ ≤
      2 / (1 - translationJointBound ν κ ^ 2) ^ 2 := by
  let k := translationJointBound ν κ
  have hk0 := pullbackJointBound_nonneg ν κ
  have hd := pullbackJointBound_gap_pos ν κ hκ
  have hκk : ‖κ‖ ≤ k := by
    apply le_trans (show ‖κ‖ ≤ (1 + ‖κ‖) / 2 by linarith)
    exact le_max_right _ _
  filter_upwards [lpInfinity_norm_ae_le ν.val.val, norm_pullbackIncrement_ae_le ν κ,
    coefficientDenominator_upper_ae ν] with z hn hi hnum
  have hden : 1 - k ^ 2 ≤ ‖1 + conj (ν.val.val z) * pullbackIncrement ν κ z‖ := by
    have hh := LiZhongQC.ahT_denom_ge hk0 (hi.trans hκk)
      (show ‖-(ν.val.val z)‖ ≤ k by rw [norm_neg]; exact hn.trans (le_max_left _ _))
    simpa only [map_neg, neg_mul, sub_neg_eq_add] using hh
  have hn2 : ‖1 - conj (ν.val.val z) * ν.val.val z‖ ≤ 2 := by
    have hh : inverseBound ν ≤ 2 := by
      unfold inverseBound
      have hv : ‖ν.val.val‖ < 1 := by
        rw [ClosedSubmodule.norm_coe]
        exact Ball.norm_lt_one ν
      nlinarith [norm_nonneg ν.val.val]
    exact hnum.trans hh
  rw [pullbackCenterWeight, norm_mul, norm_div, norm_pow, Complex.norm_conj]
  calc
    _ ≤ (2 / (1 - k ^ 2) ^ 2) * 1 := by
      apply mul_le_mul
      · exact div_le_div₀ (by norm_num) hn2 (pow_pos hd 2)
          (pow_le_pow_left₀ hd.le hden 2)
      · exact norm_derivativePhase_le ν z
      · exact norm_nonneg _
      · exact div_nonneg (by norm_num) (sq_nonneg _)
    _ = _ := mul_one _

/-- The actual all-direction coefficient derivative: forward pullback followed by the literal
bounded multiplier, in the original L-infinity norm. -/
def ambientPullbackDerivativeAt (ν : Ball Γ) (κ : Ambient) (hκ : ‖κ‖ < 1) :
    Ambient →L[ℂ] Ambient :=
  (boundedMultiply (pullbackCenterWeight ν κ)
    (pullbackCenterWeight_aestronglyMeasurable ν κ)
    (C := 2 / (1 - translationJointBound ν κ ^ 2) ^ 2)
    (div_nonneg (by norm_num) (sq_nonneg _))
    (norm_pullbackCenterWeight_ae_le ν κ hκ)).comp
      (quasiPullback (normalizedUpperEquiv ν) (normalizedUpperEquiv_quasiMeasurePreserving ν))

theorem ambientPullbackDerivativeAt_coe_ae
    (ν : Ball Γ) (κ : Ambient) (hκ : ‖κ‖ < 1) (h : Ambient) :
    ambientPullbackDerivativeAt ν κ hκ h =ᵐ[volume] fun z =>
      pullbackCenterWeight ν κ z * h (normalizedUpperEquiv ν z) := by
  filter_upwards [boundedMultiply_coe_ae (pullbackCenterWeight ν κ)
      (pullbackCenterWeight_aestronglyMeasurable ν κ)
      (C := 2 / (1 - translationJointBound ν κ ^ 2) ^ 2)
      (div_nonneg (by norm_num) (sq_nonneg _))
      (norm_pullbackCenterWeight_ae_le ν κ hκ)
      (quasiPullback (normalizedUpperEquiv ν) (normalizedUpperEquiv_quasiMeasurePreserving ν) h),
    quasiPullback_coe_ae (normalizedUpperEquiv ν) (normalizedUpperEquiv_quasiMeasurePreserving ν) h]
    with z hm hp
  exact hm.trans (congrArg (fun w : ℂ => pullbackCenterWeight ν κ z * w) hp)

/-- Uniform quadratic remainder at every coefficient center of the entire inverse ball. -/
theorem pullback_center_quadratic_remainder (ν : Ball Γ) (κ : Ambient) (hκ : ‖κ‖ < 1)
    (h : Ambient) (hh : ‖h‖ < translationCenterRadius κ) :
    ‖pullback ν (κ + h) - pullback ν κ - ambientPullbackDerivativeAt ν κ hκ h‖ ≤
      (2 / (1 - translationJointBound ν κ ^ 2) ^ 3) * ‖h‖ ^ 2 := by
  let k := translationJointBound ν κ
  have hk0 := pullbackJointBound_nonneg ν κ
  have hk1 := pullbackJointBound_lt_one ν κ hκ
  have hκk : ‖κ‖ ≤ k := by
    apply le_trans (show ‖κ‖ ≤ (1 + ‖κ‖) / 2 by linarith)
    exact le_max_right _ _
  have hsumk : ‖κ + h‖ ≤ k := by
    apply (norm_add_le κ h).trans
    apply le_trans (show ‖κ‖ + ‖h‖ ≤ (1 + ‖κ‖) / 2 by
      unfold translationCenterRadius at hh
      linarith)
    exact le_max_right _ _
  have hraw : ∀ᵐ z : ℍ ∂volume,
      ‖rawPullback ν (κ + h) z - rawPullback ν κ z -
        pullbackCenterWeight ν κ z * h (normalizedUpperEquiv ν z)‖ ≤
          (2 / (1 - k ^ 2) ^ 3) * ‖h‖ ^ 2 := by
    filter_upwards [lpInfinity_norm_ae_le ν.val.val, norm_pullbackIncrement_ae_le ν κ,
      norm_pullbackIncrement_ae_le ν (κ + h),
      (normalizedUpperEquiv_quasiMeasurePreserving ν).ae (Lp.coeFn_add κ h),
      (normalizedUpperEquiv_quasiMeasurePreserving ν).ae (lpInfinity_norm_ae_le h)]
      with z hn hb hc hadd hhz
    simp only [Pi.add_apply] at hadd
    have he := fractional_center_remainder_le hk0 hk1
      (show ‖-(ν.val.val z)‖ ≤ k by rw [norm_neg]; exact hn.trans (le_max_left _ _))
      (hb.trans hκk) (hc.trans hsumk) (show ‖(1 : ℂ)‖ ≤ 1 by norm_num)
    have hdiff : pullbackIncrement ν (κ + h) z - pullbackIncrement ν κ z =
        h (normalizedUpperEquiv ν z) * conj (derivativePhase ν z) := by
      unfold pullbackIncrement
      rw [hadd]
      ring
    simp only [map_neg, neg_mul, mul_neg, neg_neg, sub_neg_eq_add, mul_one] at he
    rw [add_comm (pullbackIncrement ν (κ + h) z) (ν.val.val z),
      add_comm (pullbackIncrement ν κ z) (ν.val.val z), hdiff] at he
    have hlin : ((1 - conj (ν.val.val z) * ν.val.val z) /
        (1 + conj (ν.val.val z) * pullbackIncrement ν κ z) ^ 2) *
          (h (normalizedUpperEquiv ν z) * conj (derivativePhase ν z)) =
        pullbackCenterWeight ν κ z * h (normalizedUpperEquiv ν z) := by
      unfold pullbackCenterWeight
      ring
    rw [hlin] at he
    have hδ : ‖h (normalizedUpperEquiv ν z) * conj (derivativePhase ν z)‖ ≤ ‖h‖ := by
      rw [norm_mul, Complex.norm_conj]
      exact (mul_le_mul hhz (norm_derivativePhase_le ν z) (norm_nonneg _) (norm_nonneg h)).trans_eq
        (mul_one _)
    exact he.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hδ 2)
      (div_nonneg (by norm_num) (pow_nonneg (pullbackJointBound_gap_pos ν κ hκ).le 3)))
  apply lpInfinity_norm_le_of_ae_bound _
    (mul_nonneg (div_nonneg (by norm_num)
      (pow_nonneg (pullbackJointBound_gap_pos ν κ hκ).le 3)) (sq_nonneg _))
  filter_upwards [Lp.coeFn_sub (pullback ν (κ + h)) (pullback ν κ),
    Lp.coeFn_sub (pullback ν (κ + h) - pullback ν κ) (ambientPullbackDerivativeAt ν κ hκ h),
    pullback_coe_ae ν (κ + h) (hsumk.trans_lt hk1), pullback_coe_ae ν κ hκ,
    ambientPullbackDerivativeAt_coe_ae ν κ hκ h, hraw] with z hsub hsub' hs hb hd hr
  simp only [Pi.sub_apply] at hsub hsub'
  rw [hsub', hsub, hs, hb, hd]
  exact hr

/-- The true normalized inverse coefficient composition is differentiable at every ball point. -/
theorem hasFDerivAt_pullback_at (ν : Ball Γ) (κ : Ambient) (hκ : ‖κ‖ < 1) :
    HasFDerivAt (pullback ν) (ambientPullbackDerivativeAt ν κ hκ) κ := by
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  let C := 2 / (1 - translationJointBound ν κ ^ 2) ^ 3
  have hC : 0 < C := div_pos (by norm_num) (pow_pos (pullbackJointBound_gap_pos ν κ hκ) 3)
  have hr : 0 < min (translationCenterRadius κ) (ε / C) := by
    apply lt_min
    · unfold translationCenterRadius
      exact div_pos (sub_pos.mpr hκ) (by norm_num)
    · exact div_pos hε hC
  filter_upwards [Metric.ball_mem_nhds (0 : Ambient) hr] with h hh
  have hn := mem_ball_zero_iff.mp hh
  have hsmall := hn.trans_le (min_le_left (translationCenterRadius κ) (ε / C))
  have hbound : C * ‖h‖ ≤ ε := by
    have ht := (lt_div_iff₀ hC).mp (hn.trans_le (min_le_right (translationCenterRadius κ) (ε / C)))
    nlinarith
  exact (pullback_center_quadratic_remainder ν κ hκ h hsmall).trans
    (by nlinarith [norm_nonneg h])

/-- The derivative retains every original group-compatibility equation. -/
theorem ambientPullbackDerivativeAt_mem_compatible
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) (κ : Ball (deformedGroup hΓ ν))
    (h : Space (deformedGroup hΓ ν)) :
    ambientPullbackDerivativeAt ν κ.val.val (Ball.norm_lt_one κ) h.val ∈ compatibleSubmodule Γ := by
  have hd := (hasFDerivAt_pullback_at ν κ.val.val (Ball.norm_lt_one κ)).comp κ.val
    ((compatibleSubmodule (deformedGroup hΓ ν)).subtypeL.hasFDerivAt)
  have hlim := hd.lim h (tendsto_norm_cobounded_atTop (E := ℂ))
  apply (isClosed_compatibleSubmodule Γ).mem_of_tendsto hlim
  apply Eventually.of_forall
  intro c
  exact (compatibleSubmodule Γ).smul_mem c ((compatibleSubmodule Γ).sub_mem
    (pullback_mem_compatible hΓ ν (κ.val + c⁻¹ • h)) (pullback_mem_compatible hΓ ν κ.val))

/-- Restriction of the literal bounded inverse derivative to the genuine compatible spaces. -/
def gammaPullbackDerivativeAt (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (κ : Ball (deformedGroup hΓ ν)) : Space (deformedGroup hΓ ν) →L[ℂ] Space Γ :=
  ((ambientPullbackDerivativeAt ν κ.val.val (Ball.norm_lt_one κ)).domRestrict
    (compatibleSubmodule (deformedGroup hΓ ν))).codRestrict (compatibleSubmodule Γ)
      (ambientPullbackDerivativeAt_mem_compatible hΓ ν κ)

/-- The actual compatible normalized pullback has its true Banach derivative at EVERY input point. -/
theorem hasFDerivAt_gammaPullback_at (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (κ : Ball (deformedGroup hΓ ν)) :
    HasFDerivAt (gammaPullback hΓ ν) (gammaPullbackDerivativeAt hΓ ν κ) κ.val := by
  have hd := (hasFDerivAt_pullback_at ν κ.val.val (Ball.norm_lt_one κ)).comp κ.val
    ((compatibleSubmodule (deformedGroup hΓ ν)).subtypeL.hasFDerivAt)
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  have he := Asymptotics.isLittleO_iff.mp (hasFDerivAt_iff_isLittleO_nhds_zero.mp hd) hε
  filter_upwards [he] with h hh
  change ‖pullback ν ((κ.val + h).val) - pullback ν κ.val.val -
    ambientPullbackDerivativeAt ν κ.val.val (Ball.norm_lt_one κ) h.val‖ ≤ ε * ‖h‖
  exact hh

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
