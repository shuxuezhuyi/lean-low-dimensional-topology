module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeAhlforsWeillSection
public import LowDimensionalTopology.Geometry.Teichmuller.NativeTranslatedBersDerivative
public import Mathlib.Tactic.LinearCombination

/-!
# A pointwise holomorphic representative of the actual pulled-back section

The fixed base coefficient is clipped only on its genuine null exceptional
set. The conjugate actual quasiconformal phase is bounded at every point
and is its reciprocal almost everywhere. The resulting literal rational
coefficient is uniformly subunit on a fixed small weighted Bers ball and
holomorphic in its genuine automorphic argument at every point. Its actual
infinity class is proved to be the independently defined normalized
quasiconformal pullback, using the actual coefficient cancellation identity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- Choose a globally bounded version of the fixed coefficient, without changing its class. -/
def clippedBase (ν : Ball Γ) (z : ℍ) : ℂ := by
  classical
  exact if ‖ν.val.val z‖ ≤ ‖ν.val.val‖ then ν.val.val z else 0

theorem norm_clippedBase_le (ν : Ball Γ) (z : ℍ) : ‖clippedBase ν z‖ ≤ ‖ν.val.val‖ := by
  classical
  unfold clippedBase
  split_ifs with hz
  · exact hz
  · simpa only [norm_zero] using norm_nonneg ν.val.val

theorem clippedBase_ae (ν : Ball Γ) : clippedBase ν =ᵐ[volume] ν.val.val := by
  filter_upwards [lpInfinity_norm_ae_le ν.val.val] with z hz
  exact ite_eq_left hz

theorem clippedBase_measurable (ν : Ball Γ) : Measurable (clippedBase ν) := by
  classical
  have hm : Measurable (fun z : ℍ => ν.val.val z) :=
    (Lp.stronglyMeasurable ν.val.val).measurable
  exact Measurable.ite (measurableSet_le hm.norm measurable_const) hm measurable_const

/-- An explicit weighted coordinate ball for a uniformly subunit inverse representative. -/
def inverseSectionRadius (ν : Ball Γ) : ℝ := (1 - ‖ν.val.val‖) / 8

def inverseSectionScale (ν : Ball Γ) : ℝ := (1 - ‖ν.val.val‖) / 4

def inverseSectionBound (ν : Ball Γ) : ℝ :=
  (‖ν.val.val‖ + inverseSectionScale ν) / (1 - ‖ν.val.val‖ * inverseSectionScale ν)

theorem inverseSectionRadius_pos (ν : Ball Γ) : 0 < inverseSectionRadius ν := by
  unfold inverseSectionRadius
  exact div_pos (sub_pos.mpr (Ball.norm_lt_one ν)) (by norm_num)

theorem inverseSectionScale_pos (ν : Ball Γ) : 0 < inverseSectionScale ν := by
  unfold inverseSectionScale
  exact div_pos (sub_pos.mpr (Ball.norm_lt_one ν)) (by norm_num)

theorem inverseSectionScale_lt_one (ν : Ball Γ) : inverseSectionScale ν < 1 := by
  unfold inverseSectionScale
  linarith [norm_nonneg ν.val.val]

theorem inverseSection_denominator_pos (ν : Ball Γ) :
    0 < 1 - ‖ν.val.val‖ * inverseSectionScale ν := by
  unfold inverseSectionScale
  nlinarith [norm_nonneg ν.val.val, Ball.norm_lt_one ν, sq_nonneg ‖ν.val.val‖]

theorem inverseSectionBound_nonneg (ν : Ball Γ) : 0 ≤ inverseSectionBound ν := by
  exact div_nonneg (add_nonneg (norm_nonneg _) (inverseSectionScale_pos ν).le)
    (inverseSection_denominator_pos ν).le

theorem inverseSectionBound_lt_one (ν : Ball Γ) : inverseSectionBound ν < 1 := by
  unfold inverseSectionBound
  apply (div_lt_one (inverseSection_denominator_pos ν)).mpr
  have hk : ‖ν.val.val‖ < 1 := by
    rw [ClosedSubmodule.norm_coe]
    exact Ball.norm_lt_one ν
  have hp : 0 < (1 - ‖ν.val.val‖) * (3 - ‖ν.val.val‖) :=
    mul_pos (sub_pos.mpr hk) (by linarith [hk])
  unfold inverseSectionScale
  nlinarith

/-- The actual section coefficient composed with the fixed normalized map and inverse phase. -/
def inverseSectionIncrement (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) (z : ℍ) : ℂ :=
  BersWeighted.ahlforsWeillCoefficient φ (normalizedUpperEquiv ν z) * conj (derivativePhase ν z)

theorem norm_inverseSectionIncrement_le (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) (z : ℍ) :
    ‖inverseSectionIncrement hΓ ν φ z‖ ≤ 2 * ‖φ‖ := by
  rw [inverseSectionIncrement, norm_mul, Complex.norm_conj]
  exact (mul_le_mul (BersWeighted.norm_ahlforsWeillCoefficient_le φ _)
    (norm_derivativePhase_le ν z) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)

/-- The literal inverse fractional coefficient, pointwise in the faithful automorphic argument. -/
def inverseSectionCoefficient (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) (z : ℍ) : ℂ :=
  (clippedBase ν z + inverseSectionIncrement hΓ ν φ z) /
    (1 + conj (clippedBase ν z) * inverseSectionIncrement hΓ ν φ z)

/-- The denominator is uniformly separated from zero at every point of the small ball. -/
theorem inverseSectionDenominator_lower (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hφ : ‖φ‖ < inverseSectionRadius ν) (z : ℍ) :
    1 - ‖ν.val.val‖ * inverseSectionScale ν ≤
      ‖1 + conj (clippedBase ν z) * inverseSectionIncrement hΓ ν φ z‖ := by
  have hi : ‖inverseSectionIncrement hΓ ν φ z‖ ≤ inverseSectionScale ν := by
    apply (norm_inverseSectionIncrement_le hΓ ν φ z).trans
    unfold inverseSectionRadius at hφ
    unfold inverseSectionScale
    linarith
  have hm : ‖conj (clippedBase ν z) * inverseSectionIncrement hΓ ν φ z‖ ≤
      ‖ν.val.val‖ * inverseSectionScale ν := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (norm_clippedBase_le ν z) hi (norm_nonneg _) (norm_nonneg _)
  have he := norm_sub_le
    (1 + conj (clippedBase ν z) * inverseSectionIncrement hΓ ν φ z)
    (conj (clippedBase ν z) * inverseSectionIncrement hΓ ν φ z)
  rw [add_sub_cancel_right, norm_one] at he
  linarith

theorem inverseSectionDenominator_ne_zero (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hφ : ‖φ‖ < inverseSectionRadius ν) (z : ℍ) :
    1 + conj (clippedBase ν z) * inverseSectionIncrement hΓ ν φ z ≠ 0 :=
  norm_pos_iff.mp ((inverseSection_denominator_pos ν).trans_le
    (inverseSectionDenominator_lower hΓ ν φ hφ z))

/-- A single strict subunit bound holds at every point and throughout the parameter ball. -/
theorem norm_inverseSectionCoefficient_le (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hφ : ‖φ‖ < inverseSectionRadius ν) (z : ℍ) :
    ‖inverseSectionCoefficient hΓ ν φ z‖ ≤ inverseSectionBound ν := by
  have hi : ‖inverseSectionIncrement hΓ ν φ z‖ ≤ inverseSectionScale ν := by
    apply (norm_inverseSectionIncrement_le hΓ ν φ z).trans
    unfold inverseSectionRadius at hφ
    unfold inverseSectionScale
    linarith
  rw [inverseSectionCoefficient, norm_div]
  apply (div_le_div_of_nonneg_right
    ((norm_add_le _ _).trans (add_le_add (norm_clippedBase_le ν z) hi))
    (norm_nonneg _)).trans
  exact div_le_div_of_nonneg_left
    (add_nonneg (norm_nonneg _) (inverseSectionScale_pos ν).le)
    (inverseSection_denominator_pos ν) (inverseSectionDenominator_lower hΓ ν φ hφ z)

theorem inverseSectionCoefficient_aestronglyMeasurable (hΓ : LiZhongQC.IsFuchsian Γ)
    (ν : Ball Γ) (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) :
    AEStronglyMeasurable (inverseSectionCoefficient hΓ ν φ) (volume : Measure ℍ) := by
  have hb : AEStronglyMeasurable (clippedBase ν) (volume : Measure ℍ) :=
    (clippedBase_measurable ν).aestronglyMeasurable
  have hs := ((BersWeighted.ahlforsWeillCoefficient_continuous φ).aestronglyMeasurable).comp_quasiMeasurePreserving
    (normalizedUpperEquiv_quasiMeasurePreserving ν)
  have hi := hs.mul (Complex.continuous_conj.comp_aestronglyMeasurable
    (derivativePhase_aestronglyMeasurable ν))
  exact (hb.add hi).div₀ (aestronglyMeasurable_const.add
    ((Complex.continuous_conj.comp_aestronglyMeasurable hb).mul hi))

/-- This representative has an actual strict subunit L-infinity bound. -/
theorem inverseSectionCoefficient_memLp (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hφ : ‖φ‖ < inverseSectionRadius ν) :
    MemLp (inverseSectionCoefficient hΓ ν φ) (⊤ : ℝ≥0∞) (volume : Measure ℍ) :=
  memLp_top_of_bound (inverseSectionCoefficient_aestronglyMeasurable hΓ ν φ)
    (inverseSectionBound ν) (Eventually.of_forall (norm_inverseSectionCoefficient_le hΓ ν φ hφ))

/-- The literal representative is complex differentiable in its genuine automorphic argument. -/
theorem differentiableAt_inverseSectionCoefficient (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hφ : ‖φ‖ < inverseSectionRadius ν) (z : ℍ) :
    DifferentiableAt ℂ (fun q => inverseSectionCoefficient hΓ ν q z) φ := by
  have he : DifferentiableAt ℂ
      (BersWeighted.ahlforsWeillEvaluation (Γ := deformedGroup hΓ ν) (normalizedUpperEquiv ν z)) φ :=
    (BersWeighted.ahlforsWeillEvaluation (Γ := deformedGroup hΓ ν)
      (normalizedUpperEquiv ν z)).differentiableAt
  have hi := he.mul_const (conj (derivativePhase ν z))
  have hb : DifferentiableAt ℂ
      (fun _ : BersWeighted.Automorphic (deformedGroup hΓ ν) => clippedBase ν z) φ :=
    differentiableAt_const _
  have hc : DifferentiableAt ℂ
      (fun _ : BersWeighted.Automorphic (deformedGroup hΓ ν) => conj (clippedBase ν z)) φ :=
    differentiableAt_const _
  have h1 : DifferentiableAt ℂ
      (fun _ : BersWeighted.Automorphic (deformedGroup hΓ ν) => (1 : ℂ)) φ :=
    differentiableAt_const _
  have hnum : DifferentiableAt ℂ
      (fun q : BersWeighted.Automorphic (deformedGroup hΓ ν) =>
        clippedBase ν z + inverseSectionIncrement hΓ ν q z) φ := hb.add hi
  have hden : DifferentiableAt ℂ
      (fun q : BersWeighted.Automorphic (deformedGroup hΓ ν) =>
        1 + conj (clippedBase ν z) * inverseSectionIncrement hΓ ν q z) φ := h1.add (hc.mul hi)
  have hquot : DifferentiableAt ℂ
      (fun q : BersWeighted.Automorphic (deformedGroup hΓ ν) =>
        (clippedBase ν z + inverseSectionIncrement hΓ ν q z) *
          (1 + conj (clippedBase ν z) * inverseSectionIncrement hΓ ν q z)⁻¹) φ :=
    hnum.mul (hden.inv (inverseSectionDenominator_ne_zero hΓ ν φ hφ z))
  simpa only [inverseSectionCoefficient, div_eq_mul_inv] using hquot

/-- The pointwise holomorphic rational coefficient is the actual normalized pullback a.e. -/
theorem pullback_ahlforsWeill_coe_ae (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hφ : ‖φ‖ < inverseSectionRadius ν) :
    pullback ν (BersWeighted.ahlforsWeill φ).val =ᵐ[volume]
      inverseSectionCoefficient hΓ ν φ := by
  let κ : Ambient := (BersWeighted.ahlforsWeill φ).val
  let μ : Ambient := pullback ν κ
  have hκ : ‖κ‖ < 1 := by
    apply (BersWeighted.norm_ahlforsWeill_le φ).trans_lt
    have hs := inverseSectionScale_lt_one ν
    unfold inverseSectionScale at hs
    unfold inverseSectionRadius at hφ
    linarith
  have hμ : ‖μ‖ < 1 := norm_pullback_lt_one ν κ
  have ht : ∀ᵐ z : ℍ ∂volume,
      rawTranslation ν μ z = BersWeighted.ahlforsWeillCoefficient φ (normalizedUpperEquiv ν z) := by
    have he := (normalizedUpperEquiv_quasiMeasurePreserving ν).ae (translation_coe_ae ν μ hμ)
    filter_upwards [he, (normalizedUpperEquiv_quasiMeasurePreserving ν).ae
      (BersWeighted.ahlforsWeill_coe_ae φ)] with z hz hκz
    rw [translation_pullback ν κ hκ, (normalizedUpperEquiv ν).symm_apply_apply] at hz
    exact hz.symm.trans hκz
  filter_upwards [ht, clippedBase_ae ν, norm_derivativePhase_ae ν,
    lpInfinity_norm_ae_le μ, lpInfinity_norm_ae_le ν.val.val] with z ht hb hp hm hn
  have hd : 1 - conj (ν.val.val z) * μ z ≠ 0 :=
    LiZhongQC.b33_t_one_sub_ne (hn.trans_lt (Ball.norm_lt_one ν)) (hm.trans_lt hμ)
  have hρ : derivativePhase ν z * conj (derivativePhase ν z) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp]
    norm_num
  have he : (μ z - ν.val.val z) / (1 - conj (ν.val.val z) * μ z) =
      inverseSectionIncrement hΓ ν φ z := by
    have hh := congrArg (fun a : ℂ => a * conj (derivativePhase ν z)) ht
    change ((μ z - ν.val.val z) / (1 - conj (ν.val.val z) * μ z) *
      derivativePhase ν z) * conj (derivativePhase ν z) = inverseSectionIncrement hΓ ν φ z at hh
    rwa [mul_assoc, hρ, mul_one] at hh
  have hmul := (div_eq_iff hd).mp he
  have hnew := inverseSectionDenominator_ne_zero hΓ ν φ hφ z
  rw [hb] at hnew
  change μ z = inverseSectionCoefficient hΓ ν φ z
  rw [inverseSectionCoefficient, hb]
  apply (eq_div_iff hnew).mpr
  linear_combination hmul

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
