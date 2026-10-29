/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
public import LowDimensionalTopology.External.LiZhongQC.Ch05.S21_UniversalTeichmuller
public import Mathlib.Tactic.Linarith

/-!
# The original coefficient difference estimate

The actual pseudohyperbolic essential supremum is bounded by the original
coefficient difference divided by the uniform positive denominator. For
native measurable coefficients this difference is the genuine L-infinity
class norm, with no pointwise choice of representatives assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller

open LiZhongQC

/-- Actual almost-everywhere coefficient bounds control the original
pseudohyperbolic difference essential supremum on the upper half-plane. -/
theorem dilatationDiffNorm_le_of_ae_bounds
    {μ ν : ℂ → ℂ} {k M : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hM : 0 ≤ M)
    (hμ : ∀ᵐ z ∂(volume.restrict upperHalf), ‖μ z‖ ≤ k)
    (hν : ∀ᵐ z ∂(volume.restrict upperHalf), ‖ν z‖ ≤ k)
    (hdiff : ∀ᵐ z ∂(volume.restrict upperHalf), ‖μ z - ν z‖ ≤ M) :
    UniversalTeichmuller.dilatationDiffNorm μ ν ≤ M / (1 - k ^ 2) := by
  have hden : 0 < 1 - k ^ 2 := by nlinarith
  unfold UniversalTeichmuller.dilatationDiffNorm
  apply ENNReal.toReal_le_of_le_ofReal (div_nonneg hM hden.le)
  apply essSup_le_of_ae_le _
  filter_upwards [hμ, hν, hdiff] with z hzμ hzν hzdiff
  have hfrac : ‖(μ z - ν z) / (1 - conj (ν z) * μ z)‖ ≤ M / (1 - k ^ 2) := by
    simpa only [mul_one] using
      (ahT_frac_le (x := μ z - ν z) (a := μ z) (b := ν z) (ρ := (1 : ℂ))
        hk₀ hk hzμ hzν (by simp) hzdiff)
  exact (ofReal_norm _).symm.trans_le (ENNReal.ofReal_le_ofReal hfrac)

namespace GammaMeasurableBeltrami

/-- The original raw difference of two native planar representatives is
bounded almost everywhere by their genuine L-infinity class difference. -/
theorem planeRepresentative_sub_norm_ae_le (μ ν : Ambient) :
    ∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf),
      ‖planeRepresentative μ z - planeRepresentative ν z‖ ≤ ‖μ - ν‖ := by
  apply ae_plane_iff.2
  have hdiff : ∀ᵐ z : ℍ ∂volume, ‖μ z - ν z‖ ≤ ‖μ - ν‖ := by
    filter_upwards [Lp.coeFn_sub μ ν, lpInfinity_norm_ae_le (μ - ν)] with z hsub hb
    change (μ - ν) z = μ z - ν z at hsub
    rwa [hsub] at hb
  simpa only [planeRepresentative_coe] using hdiff

/-- A uniform subunit norm bound gives the actual coefficient difference
estimate directly in the native Banach space's original norm. -/
theorem dilatationDiffNorm_planeRepresentative_le
    (μ ν : Ambient) {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : ‖μ‖ ≤ k) (hν : ‖ν‖ ≤ k) :
    UniversalTeichmuller.dilatationDiffNorm
        (planeRepresentative μ) (planeRepresentative ν) ≤ ‖μ - ν‖ / (1 - k ^ 2) := by
  apply dilatationDiffNorm_le_of_ae_bounds hk₀ hk (norm_nonneg (μ - ν))
  · filter_upwards [(planeRepresentative_isBeltramiCoeff μ).2] with z hz
    exact hz.trans hμ
  · filter_upwards [(planeRepresentative_isBeltramiCoeff ν).2] with z hz
    exact hz.trans hν
  · exact planeRepresentative_sub_norm_ae_le μ ν

end GammaMeasurableBeltrami
end LowDimensionalTopology.Geometry.Teichmuller
