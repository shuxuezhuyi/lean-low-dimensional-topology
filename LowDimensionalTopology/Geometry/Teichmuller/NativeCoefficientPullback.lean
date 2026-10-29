module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientTranslation
public import LowDimensionalTopology.Geometry.Teichmuller.NativeGammaSourceRealization
public import LowDimensionalTopology.Geometry.Teichmuller.ComplexBersInverse
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# The actual normalized pullback is the differentiable inverse coefficient map

The inverse map is built from the coefficient of the actual composition of
normalized quasiconformal maps. Its local inverse identity follows from a.e.
uniqueness of normalized solutions. Its L-infinity continuity is proved by a
literal coefficient estimate; the public inverse-derivative theorem then
gives the actual reciprocal bounded transport.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- The literal zero-extended representative of an ambient subunit class. -/
def ambientToSourceH (μ : Ambient) (hμ : ‖μ‖ < 1) : LiZhongQC.BeltramiH :=
  ⟨planeRepresentative μ,
    ⟨⟨‖μ‖, norm_nonneg μ, hμ, planeRepresentative_isBeltramiCoeff_univ μ⟩,
      fun _ hz => planeRepresentative_off μ (not_lt.mpr hz)⟩⟩

theorem sourceAmbient_ambientToSourceH (μ : Ambient) (hμ : ‖μ‖ < 1) :
    sourceAmbient (ambientToSourceH μ hμ) = μ := by
  apply Lp.ext
  filter_upwards [sourceAmbient_coe_ae (ambientToSourceH μ hμ)] with z hz
  simpa only [ambientToSourceH, planeRepresentative_coe] using hz

/-- The genuine fractional translation agrees with every source coefficient's
actual normalized composition, after taking its unchanged native a.e. class. -/
theorem translation_sourceAmbient_ae (ν : Ball Γ) (μ : LiZhongQC.BeltramiH) :
    translation ν (sourceAmbient μ) =ᵐ[volume] fun z : ℍ =>
      LiZhongQC.translatedBeltrami (planeRepresentative ν.val.val) μ.val z := by
  obtain ⟨_, hn, _, _, _, _, _, _⟩ := normalizedMap_spec ν
  obtain ⟨_, hm, _, _, _, _, _, hmd⟩ := LiZhongQC.b33_t_fs_spec μ
  have hc := LiZhongQC.ahQ_comp_inv_dilatation hm hn
  rw [Measure.restrict_univ] at hc
  have hs : ∀ᵐ z : ℍ ∂volume,
      LiZhongQC.translatedBeltrami (planeRepresentative ν.val.val) μ.val
          (normalizedUpperEquiv ν z) = rawTranslation ν (sourceAmbient μ) z := by
    filter_upwards [ae_plane_iff.mp (ae_restrict_of_ae hc),
      normalizedMap_dilatation_ae ν, ae_plane_iff.mp hmd,
      sourceAmbient_coe_ae μ] with z hc hn hm hclass
    change LiZhongQC.upperHalf.indicator
        (LiZhongQC.complexDilatation
          (LiZhongQC.fMuSym μ.val ∘ normalizedInverse ν))
        (normalizedMap ν z) = rawTranslation ν (sourceAmbient μ) z
    rw [indicator_of_mem (normalizedMap_mapsTo_upper ν z.im_pos), normalizedInverse, hc, hm, hn]
    unfold rawTranslation
    rw [hclass]
    rfl
  filter_upwards [translation_coe_ae ν (sourceAmbient μ) (norm_sourceAmbient_lt_one μ),
    (normalizedUpperEquiv_symm_quasiMeasurePreserving ν).ae hs] with z ht hs
  rw [(normalizedUpperEquiv ν).apply_symm_apply] at hs
  exact ht.trans hs.symm

/-- The coefficient of the actual normalized composition in the inverse order. -/
def pullback (ν : Ball Γ) (κ : Ambient) : Ambient := by
  classical
  exact if hκ : ‖κ‖ < 1 then
    sourceAmbient (LiZhongQC.b33_t_pb (toSourceGamma ν).val (ambientToSourceH κ hκ))
  else ν.val.val

theorem norm_pullback_lt_one (ν : Ball Γ) (κ : Ambient) : ‖pullback ν κ‖ < 1 := by
  unfold pullback
  split_ifs
  · exact norm_sourceAmbient_lt_one _
  · exact Ball.norm_lt_one ν

/-- The actual normalized inverse compositions cancel on the original coefficient class. -/
theorem translation_pullback (ν : Ball Γ) (κ : Ambient) (hκ : ‖κ‖ < 1) :
    translation ν (pullback ν κ) = κ := by
  rw [pullback, dite_eq_left hκ]
  apply Lp.ext
  have hs := bersInverse_translated_pullback_ae
    (toSourceGamma ν).val (ambientToSourceH κ hκ)
  filter_upwards [translation_sourceAmbient_ae ν
      (LiZhongQC.b33_t_pb (toSourceGamma ν).val (ambientToSourceH κ hκ)),
    ae_plane_iff.mp hs] with z ht hs
  change LiZhongQC.translatedBeltrami (planeRepresentative ν.val.val)
      (LiZhongQC.b33_t_pb (toSourceGamma ν).val (ambientToSourceH κ hκ)).val (z : ℂ) =
        planeRepresentative κ z at hs
  exact ht.trans (hs.trans (planeRepresentative_coe κ z))

/-- Actual inverse coefficients approach the original base in the original essential norm. -/
theorem norm_pullback_sub_base_le (ν : Ball Γ) (κ : Ambient) (hκ : ‖κ‖ < 1) :
    ‖pullback ν κ - ν.val.val‖ ≤ 2 * ‖κ‖ := by
  let μ := pullback ν κ
  let k := max ‖ν.val.val‖ ‖μ‖
  have hμ1 : ‖μ‖ < 1 := norm_pullback_lt_one ν κ
  have hk0 : 0 ≤ k := (norm_nonneg ν.val.val).trans (le_max_left _ _)
  have hk1 : k < 1 := max_lt (Ball.norm_lt_one ν) hμ1
  have hd : 0 < 1 - k ^ 2 := by nlinarith
  have hraw : ∀ᵐ z : ℍ ∂volume,
      rawTranslation ν μ z = κ (normalizedUpperEquiv ν z) := by
    have he := (normalizedUpperEquiv_quasiMeasurePreserving ν).ae
      (translation_coe_ae ν μ hμ1)
    filter_upwards [he] with z hz
    rw [translation_pullback ν κ hκ, (normalizedUpperEquiv ν).symm_apply_apply] at hz
    exact hz.symm
  apply lpInfinity_norm_le_of_ae_bound _ (mul_nonneg (by norm_num) (norm_nonneg κ))
  filter_upwards [Lp.coeFn_sub μ ν.val.val, lpInfinity_norm_ae_le μ,
    lpInfinity_norm_ae_le ν.val.val, norm_derivativePhase_ae ν, hraw,
    (normalizedUpperEquiv_quasiMeasurePreserving ν).ae (lpInfinity_norm_ae_le κ)]
    with z hsub hm hn hp hr hk
  simp only [Pi.sub_apply] at hsub
  have hd0 : 1 - conj (ν.val.val z) * μ z ≠ 0 := by
    apply norm_pos_iff.mp
    exact hd.trans_le (LiZhongQC.ahT_denom_ge hk0
      (hm.trans (le_max_right _ _)) (hn.trans (le_max_left _ _)))
  have hden : ‖1 - conj (ν.val.val z) * μ z‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖conj (ν.val.val z) * μ z‖ := norm_sub_le _ _
      _ = 1 + ‖ν.val.val z‖ * ‖μ z‖ := by rw [norm_one, norm_mul, Complex.norm_conj]
      _ ≤ 2 := by
        have hh := mul_le_mul (hn.trans (Ball.norm_lt_one ν).le)
          (hm.trans hμ1.le) (norm_nonneg (μ z)) zero_le_one
        norm_num only [one_mul] at hh
        linarith
  have heq : ‖μ z - ν.val.val z‖ =
      ‖κ (normalizedUpperEquiv ν z)‖ * ‖1 - conj (ν.val.val z) * μ z‖ := by
    rw [← hr, rawTranslation, norm_mul, norm_div, hp, mul_one,
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hd0)]
  rw [hsub, heq]
  calc
    _ ≤ ‖κ‖ * 2 := mul_le_mul hk hden (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem pullback_base (ν : Ball Γ) : pullback ν (0 : Ambient) = ν.val.val := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [norm_zero, mul_zero] using norm_pullback_sub_base_le ν 0 (by simp)

/-- Continuity is proved quantitatively for the actual normalized inverse map. -/
theorem continuousAt_pullback_zero (ν : Ball Γ) : ContinuousAt (pullback ν) 0 := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min 1 (ε / 2), lt_min zero_lt_one (div_pos hε (by norm_num)), ?_⟩
  intro κ hκ
  have hn : ‖κ‖ < min 1 (ε / 2) := by simpa only [dist_zero_right] using hκ
  have hκ1 : ‖κ‖ < 1 := hn.trans_le (min_le_left _ _)
  rw [dist_eq_norm, pullback_base]
  exact (norm_pullback_sub_base_le ν κ hκ1).trans_lt
    (by linarith [hn.trans_le (min_le_right 1 (ε / 2))])

/-- The actual inverse normalized coefficient map has the inverse genuine Banach derivative. -/
theorem hasFDerivAt_pullback (ν : Ball Γ) :
    HasFDerivAt (pullback ν) (ambientEquiv ν).symm.toContinuousLinearMap 0 := by
  have hf : HasFDerivAt (translation ν) (ambientEquiv ν).toContinuousLinearMap
      (pullback ν 0) := by
    rw [pullback_base]
    exact hasFDerivAt_translation ν
  apply hf.of_local_left_inverse (continuousAt_pullback_zero ν)
  filter_upwards [Metric.ball_mem_nhds (0 : Ambient) (by norm_num : 0 < (1 : ℝ))] with κ hκ
  exact translation_pullback ν κ (mem_ball_zero_iff.mp hκ)

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
