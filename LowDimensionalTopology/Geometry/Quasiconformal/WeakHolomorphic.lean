/-
Proofs adapted from Wu Xiaobin's Li-Zhong-QC-formalization,
commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.External.LiZhongQC.Ch02.S13_Representation
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Holomorphicity from a vanishing distributional antiholomorphic derivative

The distributional condition quantifies over actual smooth compactly supported
test functions. The proof tests against smooth reflected mollifiers, proves
that their local convolutions are holomorphic, and passes to the actual locally
uniform limit. No condition on all C² test functions or assumption that an
approximation sequence exists is imposed.

The necessary mollifier proof is adapted from Wu Xiaobin's fixed source above;
its original finite-regularity tests are replaced here by genuinely smooth tests.
The external manifest retains the original source, author and license.
-/

@[expose] public section

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped ContDiff ComplexConjugate
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The antiholomorphic derivative of F vanishes as a distribution on U:
every actual compactly supported smooth test function has zero weak pairing. -/
def HasDistributionalDbarZero (F : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ ψ : ℂ → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    ∫ w in U, F w * dzbar ψ w = 0

/-- Testing against genuine smooth mollifiers gives zero antiholomorphic
derivative for every interior mollifier approximation. -/
theorem distributional_dbar_zero_mollifier {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : ContinuousOn F U)
    (hweak : HasDistributionalDbarZero F U) {n : ℕ} {z : ℂ}
    (hball : closedBall z (1 / ((n : ℝ) + 1)) ⊆ lemma92Exhaust U n) :
    dzbar (lemma92Approx U F n) z = 0 := by
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℂ → ℂ,
      ψ = fun y : ℂ => ((((lemma92Bump n).normed volume) (z - y) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hρD : Differentiable ℝ ((lemma92Bump n).normed volume) :=
    ((lemma92Bump n).contDiff_normed (μ := volume) (n := 1)).differentiable one_ne_zero
  have hshift : ContDiff ℝ 1 (fun y : ℂ => z - y) := contDiff_const.sub contDiff_id
  have hshiftSmooth : ContDiff ℝ ∞ (fun y : ℂ => z - y) := contDiff_const.sub contDiff_id
  have hψ1 : ContDiff ℝ 1 ψ := by
    rw [hψdef]
    exact (Complex.ofRealCLM.contDiff.comp
      ((lemma92Bump n).contDiff_normed (μ := volume) (n := 1))).comp hshift
  have hψSmooth : ContDiff ℝ ∞ ψ := by
    rw [hψdef]
    exact (Complex.ofRealCLM.contDiff.comp
      ((lemma92Bump n).contDiff_normed (μ := volume) (n := ⊤))).comp hshiftSmooth
  have hψder : ∀ y v : ℂ, fderiv ℝ ψ y v
      = -((fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v : ℝ) : ℂ) := by
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
  have hballU : closedBall z (1 / ((n : ℝ) + 1)) ⊆ U := hball.trans (lemma92Exhaust_subset U n)
  have hdz0 : ∀ y ∉ closedBall z (1 / ((n : ℝ) + 1)), dzbar ψ y = 0 := by
    intro y hy
    have h : y ∉ tsupport ψ := fun h' => hy (hsψ h')
    show (fderiv ℝ ψ y 1 + I * fderiv ℝ ψ y I) / 2 = 0
    rw [sp_fderiv_eq_zero_of_notMem_tsupport h 1, sp_fderiv_eq_zero_of_notMem_tsupport h I]
    ring
  have hw : ∫ y, F y * dzbar ψ y = 0 := by
    rw [← sp_setIntegral_eq_integral (h := fun y => F y * dzbar ψ y) hU.measurableSet hballU
      fun y hy => by rw [hdz0 y hy, mul_zero]]
    exact hweak ψ hψSmooth hcψ (hsψ.trans hballU)
  have hderaux : ∀ v : ℂ, fderiv ℝ (lemma92Approx U F n) z v
      = ∫ y, fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v •
          (lemma92Exhaust U n).indicator F y := by
    intro v
    rw [fderiv_lemma92Approx_apply hF n z v,
      ← integral_sub_left_eq_self
        (fun y => fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v •
          (lemma92Exhaust U n).indicator F y) volume z]
    simp
  have hder : ∀ v : ℂ, fderiv ℝ (lemma92Approx U F n) z v
      = -∫ y, fderiv ℝ ψ y v * (lemma92Exhaust U n).indicator F y := by
    intro v
    rw [hderaux v, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v •
      (lemma92Exhaust U n).indicator F y = -(fderiv ℝ ψ y v * (lemma92Exhaust U n).indicator F y)
    rw [Complex.real_smul, ← neg_mul]
    congr 1
    rw [hψder y v, neg_neg]
  rw [sp_w_dzbar_combine (integrable_indicator_lemma92Exhaust hF n) hψ1 hcψ hder]
  have hGF : ∀ y, dzbar ψ y * (lemma92Exhaust U n).indicator F y = F y * dzbar ψ y := by
    intro y
    by_cases hy : y ∈ closedBall z (1 / ((n : ℝ) + 1))
    · rw [Set.indicator_of_mem (hball hy)]; ring
    · rw [hdz0 y hy]; ring
  rw [integral_congr_ae (Eventually.of_forall hGF), hw, neg_zero]

/-- A continuous function whose distributional antiholomorphic derivative
vanishes is holomorphic on its actual open domain. -/
theorem holomorphic_of_distributional_dbar_zero {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : ContinuousOn F U)
    (hweak : HasDistributionalDbarZero F U) :
    DifferentiableOn ℂ F U := by
  have step : ∀ C : Set ℂ, IsCompact C → C ⊆ U →
      ∀ᶠ n : ℕ in atTop, ∀ z ∈ C, DifferentiableAt ℂ (lemma92Approx U F n) z := by
    intro C hC hCU
    obtain ⟨δ, hδ, hδU, hev⟩ := lemma92_eventually hU hC hCU
    filter_upwards [hev] with n hn z hz
    obtain ⟨hnδ, hnK⟩ := hn
    have hball : closedBall z (1 / ((n : ℝ) + 1)) ⊆ lemma92Exhaust U n := fun y hy =>
      hnK (mem_cthickening_of_dist_le y z δ C hz ((mem_closedBall.1 hy).trans hnδ.le))
    exact cauchyRiemann_iff.2
      ⟨(contDiff_lemma92Approx hF n).differentiable one_ne_zero z,
        distributional_dbar_zero_mollifier hU hF hweak hball⟩
  intro z₀ hz₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have hCU : closedBall z₀ (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  have hVC : ball z₀ (r / 2) ⊆ closedBall z₀ (r / 2) := ball_subset_closedBall
  have hdiff : ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (lemma92Approx U F n) (ball z₀ (r / 2)) := by
    filter_upwards [step (closedBall z₀ (r / 2)) (isCompact_closedBall _ _) hCU] with n hn z hz
    exact (hn z (hVC hz)).differentiableWithinAt
  have hFV : DifferentiableOn ℂ F (ball z₀ (r / 2)) :=
    ((tendstoLocallyUniformlyOn_lemma92Approx hU hF).mono (hVC.trans hCU)).differentiableOn
      hdiff isOpen_ball
  exact (hFV.differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_self (by linarith)))).differentiableWithinAt

end LowDimensionalTopology.Geometry.Quasiconformal
