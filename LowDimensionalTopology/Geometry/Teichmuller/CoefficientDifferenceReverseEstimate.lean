/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.CoefficientDifferenceEstimate

/-!
# Recovering the genuine coefficient norm from fractional distortion

The difference of two native subunit coefficients is bounded by twice their
actual fractional distortion. Finiteness of the essential supremum is proved
from their actual subunit norms before passing to its real value.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

open LiZhongQC

/-- The native L-infinity difference is controlled by the actual fractional
distortion. The two subunit bounds need not be equal. -/
theorem norm_sub_le_twice_dilatationDiffNorm
    (μ ν : Ambient) (hμ : ‖μ‖ < 1) (hν : ‖ν‖ < 1) :
    ‖μ - ν‖ ≤ 2 * UniversalTeichmuller.dilatationDiffNorm
      (planeRepresentative μ) (planeRepresentative ν) := by
  let a := planeRepresentative μ
  let b := planeRepresentative ν
  let k := max ‖μ‖ ‖ν‖
  have hk₀ : 0 ≤ k := le_max_of_le_left (norm_nonneg μ)
  have hk : k < 1 := max_lt hμ hν
  have ha : ∀ᵐ z ∂(volume.restrict upperHalf), ‖a z‖ ≤ k :=
    (planeRepresentative_isBeltramiCoeff μ).2.mono fun _ hz =>
      hz.trans (le_max_left _ _)
  have hb : ∀ᵐ z ∂(volume.restrict upperHalf), ‖b z‖ ≤ k :=
    (planeRepresentative_isBeltramiCoeff ν).2.mono fun _ hz =>
      hz.trans (le_max_right _ _)
  let q : ℂ → ℝ≥0∞ := fun z => (‖(a z - b z) / (1 - conj (b z) * a z)‖₊ : ℝ≥0∞)
  let E := essSup q (volume.restrict upperHalf)
  have hqbound : ∀ᵐ z ∂(volume.restrict upperHalf),
      q z ≤ ENNReal.ofReal (2 * k / (1 + k ^ 2)) := by
    filter_upwards [ha, hb] with z hza hzb
    exact (ofReal_norm _).symm.trans_le
      (ENNReal.ofReal_le_ofReal (ahQ_pseudo_bound hk₀ hk hza hzb))
  have hE : E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (essSup_le_of_ae_le _ hqbound)
  have hfrac : ∀ᵐ z ∂(volume.restrict upperHalf),
      ‖(a z - b z) / (1 - conj (b z) * a z)‖ ≤ E.toReal := by
    filter_upwards [ENNReal.ae_le_essSup q] with z hz
    simpa only [q, ENNReal.coe_toReal, coe_nnnorm] using ENNReal.toReal_mono hE hz
  have hdiff : ∀ᵐ z ∂(volume.restrict upperHalf), ‖a z - b z‖ ≤ 2 * E.toReal := by
    filter_upwards [ha, hb, hfrac] with z hza hzb hzq
    have hmul : ‖conj (b z) * a z‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      have hprod : ‖b z‖ * ‖a z‖ ≤ k ^ 2 := by
        calc
          ‖b z‖ * ‖a z‖ ≤ k * k := mul_le_mul hzb hza (norm_nonneg _) hk₀
          _ = k ^ 2 := by ring
      have hk2 : k ^ 2 < 1 := by nlinarith
      exact hprod.trans_lt hk2
    have hden : 1 - conj (b z) * a z ≠ 0 := by
      intro hz
      have heq : conj (b z) * a z = 1 := (sub_eq_zero.mp hz).symm
      rw [heq, norm_one] at hmul
      exact (lt_irrefl (1 : ℝ)) hmul
    have hdenbound : ‖1 - conj (b z) * a z‖ ≤ 2 := by
      have ht := norm_sub_le (1 : ℂ) (conj (b z) * a z)
      rw [norm_one] at ht
      linarith
    calc
      ‖a z - b z‖ =
          ‖((a z - b z) / (1 - conj (b z) * a z)) * (1 - conj (b z) * a z)‖ := by
        rw [div_mul_cancel₀ _ hden]
      _ ≤ E.toReal * 2 := by
        rw [norm_mul]
        exact mul_le_mul hzq hdenbound (norm_nonneg _) ENNReal.toReal_nonneg
      _ = 2 * E.toReal := mul_comm _ _
  apply lpInfinity_norm_le_of_ae_bound (μ - ν) (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
  have hplane := ae_plane_iff.1 hdiff
  filter_upwards [hplane, Lp.coeFn_sub μ ν] with z hz hsub
  change (μ - ν) z = μ z - ν z at hsub
  rw [hsub]
  simpa only [a, b, planeRepresentative_coe] using hz

end LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
