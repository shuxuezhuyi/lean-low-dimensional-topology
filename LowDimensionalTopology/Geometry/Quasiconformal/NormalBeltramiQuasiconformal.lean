/-
The same-exponent fixed-point quasiconformality theorem used below is due to
Wu Xiaobin, Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2. Apache-2.0 attribution is retained
in the external source and THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.NormalBeltramiContinuity
public import LowDimensionalTopology.Geometry.Quasiconformal.WirtingerWeakApproximation
public import Mathlib.Tactic.Linarith

/-!
# Quasiconformality of every actual normal solution

The original given exponent and the actual normal solution are retained.
Only an internal coefficient representative is cut off to a compact set.
The actual fixed-point theorem supplies a plane homeomorphism and the precise
geometric distortion bound. A conformal translation restores normalization
at zero, and the original genuine weak equation identifies the actual complex
dilatation almost everywhere. No homeomorphism or growth premise is added.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Metric MeasureTheory Filter Topology
open scoped ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

/-- Every actual origin-normalized distributional solution for a compactly
essentially supported L-infinity coefficient is a quasiconformal plane
homeomorphism with the given coefficient, including the zero-bound case. -/
theorem normalLpSolution_quasiconformal
    (μ : MeasurableBeltramiSpace) {f : ℂ → ℂ} {k p : ℝ}
    (hk : k ∈ Ico (0 : ℝ) 1) (hμk : ‖μ‖ ≤ k)
    (hcomp : HasCompactEssentialSupport (μ : ℂ → ℂ))
    (hp : 2 < p) (hsmall : k * smoothHilbertNorm p < 1)
    (hf : IsNormalLpSolution (μ : ℂ → ℂ) f p) :
    IsKQC f univ ((1 + k) / (1 - k)) ∧
      (∃ e : ℂ ≃ₜ ℂ, (e : ℂ → ℂ) = f) ∧
        complexDilatation f =ᵐ[volume] (μ : ℂ → ℂ) := by
  have hp1 : 1 < p := lt_trans one_lt_two hp
  have hkp : k * hilbertNorm p < 1 := by
    simpa only [smoothHilbertNorm_eq_hilbertNorm hp1] using hsmall
  have hμ : IsBeltramiCoeff (μ : ℂ → ℂ) univ k := by
    refine ⟨(MeasurableBeltramiSpace.isBeltramiCoeff μ).1, ?_⟩
    filter_upwards [(MeasurableBeltramiSpace.isBeltramiCoeff μ).2] with z hz
    exact hz.trans hμk
  have hμLp := measurableBeltrami_memLp_of_compactEssentialSupport μ hcomp (ENNReal.ofReal p)
  obtain ⟨ω, hω, hfixed, hrepr⟩ := normalLpSolution_representation hp hμ hμLp hf
  obtain ⟨K, hK, hsupp⟩ := hcomp
  let ν : ℂ → ℂ := K.indicator (μ : ℂ → ℂ)
  have hν : ν =ᵐ[volume] (μ : ℂ → ℂ) := by
    filter_upwards [hsupp] with z hz
    change K.indicator (μ : ℂ → ℂ) z = (μ : ℂ → ℂ) z
    by_cases hzK : z ∈ K
    · exact indicator_of_mem hzK _
    · rw [indicator_of_notMem hzK, hz hzK]
  have hνCoeff : IsBeltramiCoeff ν univ k :=
    (planar_isBeltramiCoeff_congr_ae hν).mpr hμ
  obtain ⟨R, -, hRK⟩ := hK.isBounded.exists_pos_norm_le
  have hνSupp : ∀ z, R < ‖z‖ → ν z = 0 := by
    intro z hz
    exact indicator_of_notMem (fun hzK => (not_le_of_gt hz) (hRK z hzK)) _
  have hνCompact : IsCompactBeltramiCoeff ν k := ⟨hνCoeff, R, hνSupp⟩
  have hνFixed : ω =ᵐ[volume] fun z => ν z * hilbertH ω z + ν z := by
    filter_upwards [hfixed, hν] with z hz hνz
    simpa only [hνz] using hz
  obtain ⟨hrawQC, e, he⟩ := thm12_1_isKQC hk.1 hk.2 hνCompact hp hkp hω hνFixed
  have hP := normalizedCauchyPotential_eq_cauchyT_sub_of_fixedPoint hp hω hνSupp hνFixed
  have hfshift : f = fun z => (z + cauchyT ω z) - cauchyT ω 0 := by
    rw [hrepr, hP]
    funext z
    dsimp only
    ring
  have htranslation : IsConformalOnto (fun z : ℂ => z - cauchyT ω 0) univ univ := by
    simpa only [div_one] using
      (nxE_affine_isConformalOnto (a := (1 : ℂ)) (b := cauchyT ω 0) one_ne_zero)
  have hcomposed := thm7_1_comp hrawQC
    (isKQC_one_of_conformal isOpen_univ htranslation) (subset_univ _)
  have hcompfun : (fun z : ℂ => z - cauchyT ω 0) ∘ (fun z => z + cauchyT ω z) = f := by
    funext z
    dsimp only [Function.comp_apply]
    exact (congrFun hfshift z).symm
  have hQC : IsKQC f univ ((1 + k) / (1 - k)) := by
    simpa only [hcompfun, mul_one] using hcomposed
  have hhomeo : ∃ e : ℂ ≃ₜ ℂ, (e : ℂ → ℂ) = f := by
    refine ⟨e.trans (Homeomorph.subRight (cauchyT ω 0)), ?_⟩
    funext z
    show (Homeomorph.subRight (cauchyT ω 0)) (e z) = f z
    rw [Homeomorph.subRight_apply, congrFun he z, congrFun hfshift z]
  obtain ⟨-, -, g, h, hw, -, heq⟩ := hf
  have hactual : ∀ᵐ z ∂(volume : Measure ℂ), dz f z = g z ∧ dzbar f z = h z := by
    simpa only [Measure.restrict_univ] using
      homeomorph_wirtinger_eq_distributional_ae isOpen_univ hQC.2.2.1 hw
  have hJ : ∀ᵐ z ∂(volume : Measure ℂ), 0 < jacobian f z := by
    simpa only [Measure.restrict_univ] using thm9_6_cor2_jacobian_pos hQC
  refine ⟨hQC, hhomeo, ?_⟩
  filter_upwards [hactual, heq, hJ] with z hz heqz hJz
  have hg : g z ≠ 0 := by
    intro hgz
    rw [jacobian, hz.1, hgz, norm_zero] at hJz
    nlinarith [sq_nonneg ‖dzbar f z‖]
  rw [complexDilatation, hz.1, hz.2, heqz, mul_div_cancel_right₀ _ hg]

end LowDimensionalTopology.Geometry.Quasiconformal
