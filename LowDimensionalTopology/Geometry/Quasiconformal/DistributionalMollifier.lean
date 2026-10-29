/-
Proofs use the actual mollifiers and approximation theorems of Wu Xiaobin's
Li-Zhong-QC-formalization, commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Quasiconformal.DistributionalPartials
public import LowDimensionalTopology.Geometry.Quasiconformal.SmoothLocalCutoff

/-!
# Smooth approximation of genuine distributional partial derivatives

Reflected smooth mollifiers are actual admissible distributional tests.
Their derivatives converge in every finite local Lp, including L1. The
approximation sequence is constructed explicitly, rather than postulated.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The source mollifier approximation is in fact smooth, with no loss to C1. -/
theorem smooth_lemma92Approx {U : Set ℂ} {f : ℂ → ℂ}
    (hf : ContinuousOn f U) (n : ℕ) : ContDiff ℝ ∞ (lemma92Approx U f n) :=
  (lemma92Bump n).hasCompactSupport_normed.contDiff_convolution_left _
    ((lemma92Bump n).contDiff_normed (μ := volume) (n := ⊤))
    (integrable_indicator_lemma92Exhaust hf n).locallyIntegrable

/-- Testing a genuine weak derivative against a reflected smooth mollifier
identifies the actual derivative of the convolution. -/
theorem distributional_partial_mollifier {f g : ℂ → ℂ} {U : Set ℂ} {v : ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hweak : HasDistributionalPartial f g U v)
    {n : ℕ} {z : ℂ}
    (hball : closedBall z (1 / ((n : ℝ) + 1)) ⊆ lemma92Exhaust U n) :
    fderiv ℝ (lemma92Approx U f n) z v =
      ∫ y, (((lemma92Bump n).normed volume (z - y) : ℝ) : ℂ) * g y := by
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℂ → ℂ,
      ψ = fun y : ℂ => ((((lemma92Bump n).normed volume) (z - y) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hρD : Differentiable ℝ ((lemma92Bump n).normed volume) :=
    ((lemma92Bump n).contDiff_normed (μ := volume) (n := 1)).differentiable one_ne_zero
  have hψSmooth : ContDiff ℝ ∞ ψ := by
    rw [hψdef]
    exact (Complex.ofRealCLM.contDiff.comp
      ((lemma92Bump n).contDiff_normed (μ := volume) (n := ⊤))).comp
        (contDiff_const.sub contDiff_id)
  have hψder : ∀ y w : ℂ, fderiv ℝ ψ y w =
      -((fderiv ℝ ((lemma92Bump n).normed volume) (z - y) w : ℝ) : ℂ) := by
    rw [hψdef]
    exact sp_w_fderiv_shift hρD z
  have hψ0 : ∀ y ∉ closedBall z (1 / ((n : ℝ) + 1)), ψ y = 0 := by
    intro y hy
    rw [mem_closedBall, not_le] at hy
    have h : 1 / ((n : ℝ) + 1) ≤ ‖z - y‖ := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact hy.le
    rw [hψdef]
    simp [lemma92Bump_normed_eq_zero h]
  have hcψ : HasCompactSupport ψ := HasCompactSupport.intro (isCompact_closedBall z _) hψ0
  have hsψ : tsupport ψ ⊆ closedBall z (1 / ((n : ℝ) + 1)) := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    by_contra h
    exact hy (hψ0 y h)
  have hballU : closedBall z (1 / ((n : ℝ) + 1)) ⊆ U :=
    hball.trans (lemma92Exhaust_subset U n)
  have hψder0 : ∀ y ∉ closedBall z (1 / ((n : ℝ) + 1)), fderiv ℝ ψ y v = 0 :=
    fun y hy => sp_fderiv_eq_zero_of_notMem_tsupport (fun h => hy (hsψ h)) v
  have hw : (∫ y, fderiv ℝ ψ y v * f y) = -∫ y, ψ y * g y := by
    have hw := hweak.2.2 ψ hψSmooth hcψ (hsψ.trans hballU)
    rw [sp_setIntegral_eq_integral (h := fun y => fderiv ℝ ψ y v * f y)
        hU.measurableSet hballU (fun y hy => by rw [hψder0 y hy, zero_mul]),
      sp_setIntegral_eq_integral (h := fun y => ψ y * g y)
        hU.measurableSet hballU (fun y hy => by rw [hψ0 y hy, zero_mul])] at hw
    exact hw
  have hderaux : fderiv ℝ (lemma92Approx U f n) z v =
      ∫ y, fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v •
        (lemma92Exhaust U n).indicator f y := by
    rw [fderiv_lemma92Approx_apply hf n z v,
      ← integral_sub_left_eq_self
        (fun y => fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v •
          (lemma92Exhaust U n).indicator f y) volume z]
    simp
  calc fderiv ℝ (lemma92Approx U f n) z v
      = -∫ y, fderiv ℝ ψ y v * (lemma92Exhaust U n).indicator f y := by
          rw [hderaux, ← integral_neg]
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          change fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v •
            (lemma92Exhaust U n).indicator f y =
              -(fderiv ℝ ψ y v * (lemma92Exhaust U n).indicator f y)
          rw [Complex.real_smul, ← neg_mul, hψder y v, neg_neg]
    _ = -∫ y, fderiv ℝ ψ y v * f y := by
      apply congrArg Neg.neg
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      change fderiv ℝ ψ y v * (lemma92Exhaust U n).indicator f y =
        fderiv ℝ ψ y v * f y
      by_cases hy : y ∈ closedBall z (1 / ((n : ℝ) + 1))
      · rw [indicator_of_mem (hball hy)]
      · rw [hψder0 y hy, zero_mul, zero_mul]
    _ = ∫ y, ψ y * g y := by rw [hw, neg_neg]
    _ = ∫ y, (((lemma92Bump n).normed volume (z - y) : ℝ) : ℂ) * g y := by rw [hψdef]

/-- Near a compact set the derivative is the mollifier of the actual weak derivative,
truncated only outside a fixed compact neighborhood. -/
theorem distributional_partial_mollifier_eq_convolution
    {f g : ℂ → ℂ} {U C : Set ℂ} {v : ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hweak : HasDistributionalPartial f g U v)
    {δ : ℝ} {n : ℕ} (hn : 1 / ((n : ℝ) + 1) < δ)
    (hK : cthickening δ C ⊆ lemma92Exhaust U n) {z : ℂ} (hz : z ∈ C) :
    fderiv ℝ (lemma92Approx U f n) z v =
      convolution ((lemma92Bump n).normed volume) ((cthickening δ C).indicator g)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
  have hball : closedBall z (1 / ((n : ℝ) + 1)) ⊆ cthickening δ C := fun y hy =>
    mem_cthickening_of_dist_le y z δ C hz ((mem_closedBall.1 hy).trans hn.le)
  rw [distributional_partial_mollifier hU hf hweak (hball.trans hK)]
  calc (∫ y, (((lemma92Bump n).normed volume (z - y) : ℝ) : ℂ) * g y)
      = ∫ y, (lemma92Bump n).normed volume (z - y) •
          (cthickening δ C).indicator g y := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        change (((lemma92Bump n).normed volume (z - y) : ℝ) : ℂ) * g y =
          (lemma92Bump n).normed volume (z - y) • (cthickening δ C).indicator g y
        rw [Complex.real_smul]
        by_cases hy : y ∈ closedBall z (1 / ((n : ℝ) + 1))
        · rw [indicator_of_mem (hball hy)]
        · have hy' : 1 / ((n : ℝ) + 1) ≤ ‖z - y‖ := by
            rw [mem_closedBall, not_le] at hy
            rw [norm_sub_rev, ← dist_eq_norm]
            exact hy.le
          rw [lemma92Bump_normed_eq_zero hy', Complex.ofReal_zero, zero_mul, zero_mul]
    _ = ∫ t, (lemma92Bump n).normed volume t •
        (cthickening δ C).indicator g (z - t) := by
      rw [← integral_sub_left_eq_self
        (fun t => (lemma92Bump n).normed volume t •
          (cthickening δ C).indicator g (z - t)) volume z]
      simp only [sub_sub_cancel]
    _ = convolution ((lemma92Bump n).normed volume) ((cthickening δ C).indicator g)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
      rw [convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply]

/-- Actual mollifier derivatives converge locally in every finite Lp, including p=1. -/
theorem tendsto_eLpNorm_mollifier_partial_sub
    {f g : ℂ → ℂ} {U : Set ℂ} {v : ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hweak : HasDistributionalPartial f g U v)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hloc : ∀ C ⊆ U, IsCompact C → MemLp g p (volume.restrict C))
    {C : Set ℂ} (hCU : C ⊆ U) (hC : IsCompact C) :
    Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (lemma92Approx U f n) z v - g z)
      p (volume.restrict C)) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hδU, hev⟩ := lemma92_eventually hU hC hCU
  have hKc : IsCompact (cthickening δ C) := hC.cthickening
  have hKU : cthickening δ C ⊆ U :=
    (cthickening_mono (by linarith) C).trans hδU
  have hb : Tendsto (fun n => (lemma92Bump n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hG : MemLp ((cthickening δ C).indicator g) p volume :=
    (memLp_indicator_iff_restrict hKc.measurableSet.nullMeasurableSet).2 (hloc _ hKU hKc)
  refine (tendsto_eLpNorm_convolution_normed_sub hb hp hp' hG hC.measure_lt_top.ne).congr' ?_
  filter_upwards [hev] with n hn
  obtain ⟨hnδ, hnK⟩ := hn
  refine eLpNorm_congr_ae ((ae_restrict_iff' hC.measurableSet).2
    (Eventually.of_forall fun z hz => ?_))
  beta_reduce
  rw [indicator_of_mem (self_subset_cthickening C hz),
    ← distributional_partial_mollifier_eq_convolution hU hf hweak hnδ hnK hz]

/-- Genuine weak partials produce the explicit smooth approximation defining
Lp generalized partials, for all finite p≥1. -/
theorem hasGenPartials_of_distributional {f fx fy : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hweak : HasDistributionalPartials f fx fy U)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hloc : ∀ C ⊆ U, IsCompact C →
      MemLp fx p (volume.restrict C) ∧ MemLp fy p (volume.restrict C)) :
    HasGenPartials f fx fy U p := by
  refine ⟨hloc, lemma92Approx U f, fun n => (contDiff_lemma92Approx hf n).contDiffOn,
    tendstoLocallyUniformlyOn_lemma92Approx hU hf, fun C hCU hC => ?_⟩
  exact ⟨tendsto_eLpNorm_mollifier_partial_sub hU hf hweak.1 hp hp'
      (fun K hKU hK => (hloc K hKU hK).1) hCU hC,
    tendsto_eLpNorm_mollifier_partial_sub hU hf hweak.2 hp hp'
      (fun K hKU hK => (hloc K hKU hK).2) hCU hC⟩

/-- A continuous function with locally integrable genuine distributional partials
is ACL, and its ordinary coordinate derivatives equal the supplied data a.e. -/
theorem isACL_of_distributional_partials {f fx fy : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hweak : HasDistributionalPartials f fx fy U) :
    IsACL f U ∧ (∀ᵐ z ∂(volume.restrict U), partialX f z = fx z) ∧
      ∀ᵐ z ∂(volume.restrict U), partialY f z = fy z := by
  have hgp : HasGenPartials f fx fy U 1 := by
    apply hasGenPartials_of_distributional hU hf hweak le_rfl (by norm_num)
    intro C hCU hC
    exact ⟨memLp_one_iff_integrable.2
        ((locallyIntegrableOn_iff hU.isLocallyClosed).1 hweak.1.2.1 C hCU hC),
      memLp_one_iff_integrable.2
        ((locallyIntegrableOn_iff hU.isLocallyClosed).1 hweak.2.2.1 C hCU hC)⟩
  exact ⟨⟨hf, fun a b c d hab hcd hR =>
      ⟨(hasGenPartials_vertical hU le_rfl hgp hab hcd hR).1,
        (hasGenPartials_horizontal hU le_rfl hgp hab hcd hR).1⟩⟩,
    ae_restrict_of_forall_openRect hU fun a b c d hab hcd hR =>
      (hasGenPartials_horizontal hU le_rfl hgp hab hcd hR).2,
    ae_restrict_of_forall_openRect hU fun a b c d hab hcd hR =>
      (hasGenPartials_vertical hU le_rfl hgp hab hcd hR).2⟩

/-- For every compact subset, genuine weak partial derivatives admit actual
compactly supported smooth approximants inside the original open domain.
Values converge uniformly and both ordinary partials converge in finite Lp. -/
theorem exists_smooth_compact_approximation_of_distributional
    {f fx fy : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hweak : HasDistributionalPartials f fx fy U)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hloc : ∀ C ⊆ U, IsCompact C →
      MemLp fx p (volume.restrict C) ∧ MemLp fy p (volume.restrict C))
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ φ : ℕ → ℂ → ℂ,
      (∀ n, ContDiff ℝ ∞ (φ n) ∧ HasCompactSupport (φ n) ∧ tsupport (φ n) ⊆ U) ∧
      TendstoUniformlyOn φ f atTop K ∧
      Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (φ n) z 1 - fx z)
        p (volume.restrict K)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (φ n) z I - fy z)
        p (volume.restrict K)) atTop (𝓝 0) := by
  have hval : TendstoUniformlyOn (lemma92Approx U f) f atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1
      (tendstoLocallyUniformlyOn_lemma92Approx hU hf) K hKU hK
  obtain ⟨φ, hφ, -, hφval, hφx, hφy⟩ := smooth_compact_localization hK hU hKU
    (smooth_lemma92Approx hf) hval
    (tendsto_eLpNorm_mollifier_partial_sub hU hf hweak.1 hp hp'
      (fun C hCU hC => (hloc C hCU hC).1) hKU hK)
    (tendsto_eLpNorm_mollifier_partial_sub hU hf hweak.2 hp hp'
      (fun C hCU hC => (hloc C hCU hC).2) hKU hK)
  exact ⟨φ, hφ, hφval, hφx, hφy⟩

end LowDimensionalTopology.Geometry.Quasiconformal
