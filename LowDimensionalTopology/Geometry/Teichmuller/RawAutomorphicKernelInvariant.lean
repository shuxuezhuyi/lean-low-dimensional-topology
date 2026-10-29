/-
Copyright (c) 2026 Wu Xiaobin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wu Xiaobin (original proof)
-/
module

public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton
public import Mathlib.Tactic.FieldSimp

/-!
# Kernel invariance for the original pointwise automorphic coefficient

This adapts the complete proof of `h36p_c_kinv` from Wu Xiaobin's
Li-Zhong-QC-formalization, commit `1c0d5473c020b66ed5106331a38a61536760b9b2`
(Apache-2.0), `LiZhongQC/Ch11/S36_Hamilton.lean`. The proof uses only the
original pointwise automorphy equation; holomorphy and integrability are not
premises. The original kernel, inverse matrix and Jacobian factor are retained.
See `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.AutomorphicPoincare

open LiZhongQC

/-- The original pointwise weight-minus-four equation alone gives the exact
kernel transformation with the inverse matrix and the original Jacobian. -/
theorem rawAutomorphicKernel_invariant
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {f : ℂ → ℂ}
    (ha : ∀ γ ∈ Γ, ∀ w ∈ upperHalf,
      f (h36p_m γ w) / ((γ 1 0 : ℂ) * w + γ 1 1) ^ 4 = f w)
    {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hδ : δ ∈ Γ)
    {ζ z : ℂ} (hζ : ζ ∈ upperHalf) (hz : z ∈ upperHalf) :
    h36p_c_K f ζ (h36p_m δ⁻¹ z) / (((δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
      (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) ^ 4 =
      ((‖(δ 1 0 : ℂ) * ζ + δ 1 1‖⁻¹ ^ 4 : ℝ) : ℂ) * h36p_c_K f (h36p_m δ ζ) z := by
  have hdet := b33_d_det δ
  have hy : 0 < ζ.im := hζ
  have hv : 0 < z.im := hz
  have e00 : (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 = δ 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have e01 : (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 = -δ 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have e10 : (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 = -δ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have e11 : (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 = δ 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hW : h36p_m δ⁻¹ z ∈ upperHalf := h36p_m_mem δ⁻¹ hz
  have hJ : ((δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
      (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 ≠ 0 :=
    k24_d_den_ne_zero (b33_d_det δ⁻¹) hv.ne'
  have hWJ : h36p_m δ⁻¹ z * (((δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
      (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) =
      ((δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 : ℂ) * z +
        (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 := by
    unfold h36p_m
    exact div_mul_cancel₀ _ hJ
  have hA : (δ 1 0 : ℂ) * ζ + δ 1 1 ≠ 0 := k24_d_den_ne_zero hdet hy.ne'
  have hAc : (δ 1 0 : ℂ) * conj ζ + δ 1 1 ≠ 0 :=
    k24_d_den_ne_zero hdet (by rw [conj_im]; linarith)
  have hconj : conj (h36p_m δ ζ) = ((δ 0 0 : ℂ) * conj ζ + δ 0 1) / ((δ 1 0 : ℂ) * conj ζ + δ 1 1) := by
    simp [h36p_m, map_div₀]
  have hfu : f (h36p_m δ ζ) = f ζ * ((δ 1 0 : ℂ) * ζ + δ 1 1) ^ 4 := by
    have hA' := ha δ hδ ζ hζ
    rw [← hA', div_mul_cancel₀ _ (pow_ne_zero _ hA)]
  have him : ((h36p_m δ ζ).im : ℂ) =
      (ζ.im : ℂ) / (((δ 1 0 : ℂ) * ζ + δ 1 1) * conj ((δ 1 0 : ℂ) * ζ + δ 1 1)) := by
    rw [Complex.mul_conj]
    have e : (h36p_m δ ζ).im = ζ.im / Complex.normSq ((δ 1 0 : ℂ) * ζ + δ 1 1) := by
      unfold h36p_m
      rw [Complex.div_im]
      simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
      rw [div_sub_div_same]
      congr 1
      linear_combination ζ.im * hdet
    rw [e]
    push_cast
    ring
  have hnrm : ((‖(δ 1 0 : ℂ) * ζ + δ 1 1‖⁻¹ ^ 4 : ℝ) : ℂ) =
      ((((δ 1 0 : ℂ) * ζ + δ 1 1) * conj ((δ 1 0 : ℂ) * ζ + δ 1 1)) ^ 2)⁻¹ := by
    rw [Complex.mul_conj']
    push_cast
    ring
  have hcA : conj ((δ 1 0 : ℂ) * ζ + δ 1 1) = (δ 1 0 : ℂ) * conj ζ + δ 1 1 := by simp
  have hkey : ((δ 0 0 : ℂ) * conj ζ + δ 0 1) / ((δ 1 0 : ℂ) * conj ζ + δ 1 1) - z =
      (((δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
        (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) * (conj ζ - h36p_m δ⁻¹ z) /
        ((δ 1 0 : ℂ) * conj ζ + δ 1 1) := by
    rw [eq_div_iff hAc, sub_mul, div_mul_cancel₀ _ hAc]
    rw [e00, e01, e10, e11] at hWJ
    rw [e10, e11]
    push_cast at hWJ ⊢
    linear_combination hWJ
  have hZW : conj ζ - h36p_m δ⁻¹ z ≠ 0 := h36p_c_conj_sub_ne hζ hW
  have hAc' : conj ζ * (δ 1 0 : ℂ) + δ 1 1 ≠ 0 := by rwa [mul_comm]
  have hA' : ζ * (δ 1 0 : ℂ) + δ 1 1 ≠ 0 := by rwa [mul_comm]
  unfold h36p_c_K
  rw [hfu, him, hnrm, hconj, hcA, hkey]
  field_simp

end LowDimensionalTopology.Geometry.Teichmuller.AutomorphicPoincare
