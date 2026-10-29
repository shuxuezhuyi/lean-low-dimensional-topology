/-
The reflected-mollifier computation and Lp approximation APIs are adapted from
Wu Xiaobin's Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2, with retained attribution.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.NormalizedCauchyDistributional
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Tactic.LinearCombination

/-!
# Rigidity of entire locally weak holomorphic functions in finite Lp

Reflected smooth tests show that the actual untruncated mollifiers are entire.
Hölder's convolution estimate makes each mollifier globally bounded, so
Liouville's theorem makes it constant. Finite Lp norm on the plane forces that
constant to vanish. Actual global Lp approximation then proves the original
continuous weakly holomorphic function vanishes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Metric MeasureTheory Filter Topology
open scoped ContDiff ENNReal Convolution
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem fderiv_mollifier_apply {F : ℂ → ℂ} (hF : Continuous F)
    (n : ℕ) (z v : ℂ) :
    fderiv ℝ (t5Mollify F n) z v =
      ∫ t, fderiv ℝ ((lemma92Bump n).normed volume) t v • F (z - t) := by
  have hg : LocallyIntegrable F (volume : Measure ℂ) := hF.locallyIntegrable
  have hd := (lemma92Bump n).hasCompactSupport_normed.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    ((lemma92Bump n).contDiff_normed (μ := volume) (n := 1)) hg z
  have hex := ((lemma92Bump n).hasCompactSupport_normed.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ)
    (((lemma92Bump n).contDiff_normed (μ := volume) (n := 1)).continuous_fderiv one_ne_zero)
    hg z
  unfold t5Mollify
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex]
  simp

/-- Every actual global mollifier of a continuous weakly holomorphic function
has zero antiholomorphic derivative everywhere. -/
theorem mollifier_dbar_zero_of_distributional {F : ℂ → ℂ} (hF : Continuous F)
    (hw : HasDistributionalDbarZero F univ) (n : ℕ) (z : ℂ) :
    dzbar (t5Mollify F n) z = 0 := by
  let ψ : ℂ → ℂ := fun y => (((lemma92Bump n).normed volume (z - y) : ℝ) : ℂ)
  have hρD : Differentiable ℝ ((lemma92Bump n).normed volume) :=
    ((lemma92Bump n).contDiff_normed (μ := volume) (n := 1)).differentiable one_ne_zero
  have hψ : ContDiff ℝ ∞ ψ :=
    (Complex.ofRealCLM.contDiff.comp
      ((lemma92Bump n).contDiff_normed (μ := volume) (n := ⊤))).comp
        (contDiff_const.sub contDiff_id)
  have hcψ : HasCompactSupport ψ := by
    refine HasCompactSupport.intro (isCompact_closedBall z (1 / ((n : ℝ) + 1))) ?_
    intro y hy
    rw [mem_closedBall, not_le] at hy
    have hdist : 1 / ((n : ℝ) + 1) ≤ ‖z - y‖ := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact hy.le
    simp only [ψ, lemma92Bump_normed_eq_zero hdist, Complex.ofReal_zero]
  have hψder (y v : ℂ) : fderiv ℝ ψ y v =
      -((fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v : ℝ) : ℂ) :=
    sp_w_fderiv_shift hρD z y v
  have htest : (∫ y, F y * dzbar ψ y) = 0 := by
    simpa only [Measure.restrict_univ] using hw ψ hψ hcψ (subset_univ _)
  have hderaux (v : ℂ) : fderiv ℝ (t5Mollify F n) z v =
      ∫ y, fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v • F y := by
    rw [fderiv_mollifier_apply hF n z v,
      ← integral_sub_left_eq_self
        (fun y => fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v • F y) volume z]
    simp
  have hder (v : ℂ) : fderiv ℝ (t5Mollify F n) z v =
      -∫ y, fderiv ℝ ψ y v * F y := by
    rw [hderaux v, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Complex.real_smul, ← neg_mul]
    congr 1
    rw [hψder y v, neg_neg]
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hint (v : ℂ) : Integrable (fun y => fderiv ℝ ψ y v * F y) volume := by
    have hdψ : Continuous (fun y => fderiv ℝ ψ y v) :=
      (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (hdψ.mul hF).integrable_of_hasCompactSupport
      ((sp_hasCompactSupport_fderiv hcψ v).mul_right)
  have hzero : (∫ y, dzbar ψ y * F y) = 0 := by
    simpa only [mul_comm] using htest
  have hsum : (∫ y, fderiv ℝ ψ y 1 * F y) +
      I * (∫ y, fderiv ℝ ψ y I * F y) = 0 := by
    calc
      _ = 2 * ∫ y, dzbar ψ y * F y := by
        rw [← integral_const_mul I (fun y => fderiv ℝ ψ y I * F y),
          ← integral_add (hint 1) ((hint I).const_mul I), ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        show _ = 2 * ((fderiv ℝ ψ y 1 + I * fderiv ℝ ψ y I) / 2 * F y)
        ring
      _ = 0 := by rw [hzero, mul_zero]
  show (fderiv ℝ (t5Mollify F n) z 1 + I * fderiv ℝ (t5Mollify F n) z I) / 2 = 0
  rw [hder 1, hder I]
  linear_combination -hsum / 2

/-- A continuous globally weakly holomorphic finite-Lp function on the actual
plane vanishes. No boundedness or behavior at infinity is assumed. -/
theorem distributional_dbar_zero_eq_zero_of_memLp {F : ℂ → ℂ} {p : ℝ}
    (hp : 1 < p) (hF : Continuous F) (hw : HasDistributionalDbarZero F univ)
    (hmem : MemLp F (ENNReal.ofReal p) (volume : Measure ℂ)) : F = 0 := by
  let P : ℝ≥0∞ := ENNReal.ofReal p
  have hP : 1 ≤ P := by
    rw [show P = ENNReal.ofReal p from rfl, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  let : Fact (1 ≤ P) := ⟨hP⟩
  have hP0 : P ≠ 0 := (ENNReal.ofReal_pos.mpr (lt_trans one_pos hp)).ne'
  have hPtop : P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hvanish (n : ℕ) : t5Mollify F n = 0 := by
    have hρmem : MemLp ((lemma92Bump n).normed volume) (ENNReal.conjExponent P) volume :=
      (lemma92Bump n).continuous_normed.memLp_of_hasCompactSupport
        (lemma92Bump n).hasCompactSupport_normed
    let B : ℝ≥0∞ := ‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)‖ₑ *
      eLpNorm ((lemma92Bump n).normed volume) (ENNReal.conjExponent P) volume *
        eLpNorm F P volume
    have hB : B ≠ ⊤ := by dsimp only [B]; finiteness
    have hbound (z : ℂ) : ‖t5Mollify F n z‖ₑ ≤ B :=
      enorm_convolution_le (p := ENNReal.conjExponent P) (q := P)
        (ContinuousLinearMap.lsmul ℝ ℝ) hρmem.aestronglyMeasurable
        hmem.aestronglyMeasurable z
    have hbdd : Bornology.IsBounded (range (t5Mollify F n)) := by
      refine isBounded_iff_forall_norm_le.mpr ⟨B.toReal, ?_⟩
      rintro _ ⟨z, rfl⟩
      simpa only [toReal_enorm] using ENNReal.toReal_mono hB (hbound z)
    have hFn1 : ContDiff ℝ 1 (t5Mollify F n) :=
      (t5Mollify_contDiff hp.le hmem n).of_le (by simp)
    have hhol : Differentiable ℂ (t5Mollify F n) := by
      intro z
      exact cauchyRiemann_iff.mpr
        ⟨hFn1.differentiable_one z,
          mollifier_dbar_zero_of_distributional hF hw n z⟩
    have hc (z : ℂ) : t5Mollify F n z = t5Mollify F n 0 :=
      hhol.apply_eq_apply_of_bounded hbdd z 0
    have hcMem : MemLp (fun _ : ℂ => t5Mollify F n 0) P volume := by
      have hm := t5Mollify_memLp hp.le hPtop hmem n
      convert hm using 1
      funext z
      exact (hc z).symm
    have hc0 : t5Mollify F n 0 = 0 := by
      rcases (memLp_const_iff hP0 hPtop).mp hcMem with hz | hfin
      · exact hz
      · rw [measure_univ_of_isAddLeftInvariant (volume : Measure ℂ)] at hfin
        exact (lt_irrefl ⊤ hfin).elim
    funext z
    exact (hc z).trans hc0
  have hlim := t5Mollify_tendsto_global hp.le hPtop hmem
  have heq (n : ℕ) : (fun z => t5Mollify F n z - F z) = -F := by
    funext z
    change t5Mollify F n z - F z = -F z
    simp only [hvanish n, Pi.zero_apply, zero_sub]
  have hlim' : Tendsto (fun _ : ℕ => eLpNorm F P volume) atTop (𝓝 0) := by
    simpa only [heq, eLpNorm_neg] using hlim
  have hnorm : eLpNorm F P volume = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hlim'
  exact (hF.ae_eq_iff_eq (volume : Measure ℂ) continuous_zero).mp
    ((eLpNorm_eq_zero_iff hP0).mp hnorm)

/-- Every actual entire function has vanishing distributional antiholomorphic
 derivative against the same smooth compact tests. -/
theorem entire_hasDistributionalDbarZero {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    HasDistributionalDbarZero F univ := by
  have hF1 : ContDiff ℝ 1 F :=
    (show ContDiff ℂ 1 F from hF.contDiff).restrict_scalars ℝ
  intro ψ hψ hcψ _
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hibp := (c1_wirtinger_integral_by_parts hF1 hψ1 hcψ).2
  have hbar (z : ℂ) : dzbar F z = 0 := (cauchyRiemann_iff.mp (hF z)).2
  simpa only [Measure.restrict_univ, hbar, mul_zero, integral_zero, neg_zero] using hibp

/-- An actual entire function in finite Lp on the actual plane vanishes.
The hypotheses contain no boundedness or asymptotic normalization. -/
theorem entire_eq_zero_of_memLp {F : ℂ → ℂ} {p : ℝ} (hp : 1 < p)
    (hF : Differentiable ℂ F)
    (hmem : MemLp F (ENNReal.ofReal p) (volume : Measure ℂ)) : F = 0 :=
  distributional_dbar_zero_eq_zero_of_memLp hp hF.continuous
    (entire_hasDistributionalDbarZero hF) hmem

end LowDimensionalTopology.Geometry.Quasiconformal
