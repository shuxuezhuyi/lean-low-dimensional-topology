module

public import LowDimensionalTopology.External.LiZhongQC.Ch10.S33_BersEmbedding
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# The inverse Bers epsilon estimate

The weighted Bers norm controls the actual source Teichmuller distance locally.
The proof uses an Ahlfors--Weill coefficient after actual right translation and
pulls it back to a compatible representative. No topological compatibility is
assumed. The distance below has the source half-log normalization.
The extension and normalization argument reuses Wu Xiaobin's LiZhongQC source,
fixed commit 1c0d5473c020b66ed5106331a38a61536760b9b2, retained under Apache-2.0.
-/

@[expose] public section
noncomputable section

open Complex Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller

open LiZhongQC

/-- The actual coefficient pseudodistance respects equality almost everywhere. -/
theorem bersInverse_dilatationDiffNorm_congr_ae
    {μ μ' ν ν' : ℂ → ℂ}
    (hμ : μ =ᵐ[volume.restrict upperHalf] μ')
    (hν : ν =ᵐ[volume.restrict upperHalf] ν') :
    UniversalTeichmuller.dilatationDiffNorm μ ν =
      UniversalTeichmuller.dilatationDiffNorm μ' ν' := by
  unfold UniversalTeichmuller.dilatationDiffNorm
  congr 1
  apply essSup_congr_ae
  filter_upwards [hμ, hν] with z hzμ hzν
  rw [hzμ, hzν]

/-- Right translation of the pullback has the original coefficient a.e.,
which is stronger than equality of their Teichmuller classes. -/
theorem bersInverse_translated_pullback_ae (μ₀ κ : BeltramiH) :
    translatedBeltrami μ₀.1 (b33_t_pb μ₀ κ).1 =ᵐ[volume.restrict upperHalf] κ.1 := by
  obtain ⟨_, -, -, -, -, -, -, ht⟩ := b33_t_fs_spec (b33_t_tb μ₀ (b33_t_pb μ₀ κ))
  obtain ⟨_, -, -, -, -, -, -, hκ⟩ := b33_t_fs_spec κ
  filter_upwards [ht, hκ] with z htz hκz
  change complexDilatation (fMuSym (translatedBeltrami μ₀.1 (b33_t_pb μ₀ κ).1)) z =
    translatedBeltrami μ₀.1 (b33_t_pb μ₀ κ).1 z at htz
  rw [b33_t_tb_pb_fMuSym] at htz
  exact htz.symm.trans hκz

/-- The Ahlfors--Weill coefficient has the required actual L-infinity bound. -/
theorem bersInverse_aw_dilatation_le {φ : ℂ → ℂ} {η : ℝ} (hη : 0 ≤ η)
    (hφ : bersNormL φ < ENNReal.ofReal η) (κ : BeltramiH)
    (hκ : ∀ z ∈ upperHalf, κ.1 z = -2 * (z.im : ℂ) ^ 2 * φ (conj z)) :
    UniversalTeichmuller.dilatationDiffNorm 0 κ.1 ≤ 2 * η := by
  rw [UniversalTeichmuller.ut_d_symm, bB_l_dilatationDiffNorm_zero]
  apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by norm_num) hη)
  refine essSup_le_of_ae_le _ ?_
  filter_upwards [ae_restrict_mem isOpen_upperHalf.measurableSet] with z hz
  rw [← enorm_eq_nnnorm, ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  have hc : conj z ∈ lowerHalf := by
    change (conj z).im < 0
    rw [Complex.conj_im]
    exact neg_lt_zero.mpr hz
  have hp : ENNReal.ofReal (‖φ (conj z)‖ * (conj z).im ^ 2) ≤ bersNormL φ := by
    unfold bersNormL
    exact le_iSup₂_of_le (conj z) hc le_rfl
  have hp' : ‖φ (conj z)‖ * (conj z).im ^ 2 ≤ η :=
    (ENNReal.ofReal_le_ofReal_iff hη).1 (hp.trans hφ.le)
  rw [Complex.conj_im, neg_sq] at hp'
  rw [hκ z hz]
  simp only [norm_mul, norm_neg, norm_pow, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith

/-- Exact invariance plus actual a.e. cancellation identifies the distance
from the base representative to the pulled-back coefficient. -/
theorem bersInverse_pullback_distance (μ₀ κ : BeltramiH) :
    UniversalTeichmuller.dilatationDiffNorm μ₀.1 (b33_t_pb μ₀ κ).1 =
      UniversalTeichmuller.dilatationDiffNorm 0 κ.1 := by
  have h := b33_t_dd_tb μ₀ μ₀ (b33_t_pb μ₀ κ)
  rw [b33_t_tb_self] at h
  exact h.symm.trans (bersInverse_dilatationDiffNorm_congr_ae
    Filter.EventuallyEq.rfl (bersInverse_translated_pullback_ae μ₀ κ))

/-- The inverse of the Bers embedding is continuous for the actual source
half-log Teichmuller distance, expressed without an auxiliary topology. -/
theorem bersMapGamma_inverse_epsilon
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (p : TeichGamma Γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ q : TeichGamma Γ,
      bersNormL (bersMapGamma Γ q - bersMapGamma Γ p) < ENNReal.ofReal δ →
        teichDistanceGamma p q < ε := by
  let μ₀ : BeltramiGamma Γ := Quotient.out p
  have hp : bersMapGamma Γ p = bersFunction μ₀.1.1 := rfl
  obtain ⟨Γμ₀, hFμ₀, hΓμ₀1, hΓμ₀2⟩ := exists_deformation_group hΓ μ₀
  obtain ⟨χ, -, c2, c3, c4, c5, c6, -⟩ :=
    eq33_12_translation hΓ μ₀ ⟨hΓμ₀1, hΓμ₀2⟩
  obtain ⟨t, ht0, ht1, htlog⟩ := aw_t_log_small (ε := 2 * ε) (by linarith)
  let η : ℝ := min (1 / 4) (t / 4)
  have hη0 : 0 < η := lt_min (by norm_num) (by linarith)
  have hηhalf : η < 1 / 2 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hηt : 2 * η < t := by
    have h := min_le_right (1 / 4 : ℝ) (t / 4)
    change η ≤ t / 4 at h
    linarith
  obtain ⟨δ, hδ, hcont⟩ := c4 μ₀.1 η hη0
  refine ⟨δ, hδ, fun q hq => ?_⟩
  let ν : BeltramiGamma Γ := Quotient.out q
  have hν : bersMapGamma Γ q = bersFunction ν.1.1 := rfl
  have hsmall : bersNormL (χ (bersFunction ν.1.1)) < ENNReal.ofReal η := by
    have h := hcont ν.1 (by rw [← hν, ← hp]; exact hq)
    rwa [c3, sub_zero] at h
  have hauto : χ (bersFunction ν.1.1) ∈ automorphicQD Γμ₀ := by
    apply (c5 ν.1).1
    rw [← hν]
    exact (bersMapGamma_mem hΓ q).1
  have hsmallhalf : bersNormL (χ (bersFunction ν.1.1)) < ENNReal.ofReal (1 / 2) :=
    hsmall.trans ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hηhalf)
  obtain ⟨hle, hs0, hs⟩ := t203_t_toReal hsmallhalf
  have hφs : ∀ z ∈ lowerHalf, ‖χ (bersFunction ν.1.1) z‖ * z.im ^ 2 ≤
      (bersNormL (χ (bersFunction ν.1.1))).toReal := by
    intro z hz
    have hpoint : ENNReal.ofReal (‖χ (bersFunction ν.1.1) z‖ * z.im ^ 2) ≤
        bersNormL (χ (bersFunction ν.1.1)) := by
      unfold bersNormL
      exact le_iSup₂_of_le z hz le_rfl
    exact (ENNReal.ofReal_le_ofReal_iff hs0).1 (hpoint.trans hle)
  obtain ⟨hφd, hφ0, -⟩ := id hauto
  obtain ⟨H, K, hH, hHs, hH0, hH1, hHd, hHS, hHμ⟩ :=
    l333_core hs0 hs hφd hφs
  have hmem := l333_mu_mem hs0 hs hφd hφs
  let κ : BeltramiGamma Γμ₀ :=
    ⟨⟨l333_mu (χ (bersFunction ν.1.1)), hmem⟩, l333_mu_compat hauto⟩
  have hsol : normalizedSolution (l333_mu (χ (bersFunction ν.1.1))) = H := by
    obtain ⟨hq, hsq, hq0, hq1, hd⟩ := ut_spec κ.1
    refine thm13_5_uniqueness_plane hq ⟨K, hH⟩ hsq hHs ?_ hq0 hq1 hH0 hH1
    have hnull : ∀ᵐ z : ℂ, z ∉ {w : ℂ | w.im = 0} :=
      measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
    filter_upwards [hd, hnull] with z h1 h2
    rw [h1]
    show l333_mu (χ (bersFunction ν.1.1)) z = complexDilatation H z
    rcases lt_or_gt_of_ne (h2 : z.im ≠ 0) with hlt | hgt
    · have hdiff : DifferentiableAt ℂ H z :=
        hHd.differentiableAt (isOpen_lowerHalf.mem_nhds hlt)
      have hbar : dzbar H z = 0 := (cauchyRiemann_iff.1 hdiff).2
      rw [complexDilatation, hbar, zero_div]
      exact hmem.2 z hlt.le
    · rw [hHμ z hgt]
      exact indicator_of_mem (show z ∈ upperHalf from hgt) _
  have hκpoint : ∀ z ∈ upperHalf,
      κ.1.1 z = -2 * (z.im : ℂ) ^ 2 * χ (bersFunction ν.1.1) (conj z) :=
    fun z hz => show l333_mu (χ (bersFunction ν.1.1)) z = _ from indicator_of_mem hz _
  have hκB : bersFunction κ.1.1 = χ (bersFunction ν.1.1) := by
    funext z
    show lowerHalf.indicator
      (schwarzian (normalizedSolution (l333_mu (χ (bersFunction ν.1.1))))) z = _
    rw [hsol]
    by_cases hz : z ∈ lowerHalf
    · rw [indicator_of_mem hz, hHS z hz]
    · rw [indicator_of_notMem hz, hφ0 z hz]
  let μ' : BeltramiGamma Γ :=
    ⟨b33_t_pb μ₀.1 κ.1,
      b33_t_pb_compat μ₀.1 κ.1 hΓμ₀1 (fun γ hγ => b33_d_def κ hγ)⟩
  have hχ : χ (bersFunction μ'.1.1) = χ (bersFunction ν.1.1) := by
    rw [c2, ← hκB]
    exact (b33_t_bf_eq_iff (b33_t_tb μ₀.1 (b33_t_pb μ₀.1 κ.1)) κ.1).2
      (b33_t_tb_pb_equiv μ₀.1 κ.1)
  have hB : bersFunction μ'.1.1 = bersFunction ν.1.1 :=
    c6 ⟨μ'.1, rfl⟩ ⟨ν.1, rfl⟩ hχ
  have hclass : Quotient.mk _ μ' = q := by
    apply bersMapGamma_injective hΓ
    rw [bg_bersMapGamma_eq (μ := μ') rfl, hν]
    exact hB
  have hd : UniversalTeichmuller.dilatationDiffNorm μ₀.1.1 μ'.1.1 ≤ 2 * η := by
    change UniversalTeichmuller.dilatationDiffNorm μ₀.1.1
      (b33_t_pb μ₀.1 κ.1).1 ≤ 2 * η
    rw [bersInverse_pullback_distance]
    exact bersInverse_aw_dilatation_le hη0.le hsmall κ.1 hκpoint
  have hdelta : teichDeltaGamma p q ≤
      UniversalTeichmuller.dilatationDiffNorm μ₀.1.1 μ'.1.1 := by
    unfold teichDeltaGamma
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro d ⟨a, b, -, -, rfl⟩
      exact ENNReal.toReal_nonneg
    · exact ⟨μ₀, μ', Quotient.out_eq p, hclass, rfl⟩
  have hdelta0 := (bg_d_teichDelta_spec p q).1
  have hdeltat : teichDeltaGamma p q < t := hdelta.trans_lt (hd.trans_lt hηt)
  unfold teichDistanceGamma
  calc
    (1 / 2) * Real.log ((1 + teichDeltaGamma p q) / (1 - teichDeltaGamma p q)) ≤
        (1 / 2) * Real.log ((1 + t) / (1 - t)) :=
      s33d_phi_mono hdelta0 hdeltat.le ht1
    _ < ε := by linarith

end LowDimensionalTopology.Geometry.Teichmuller
