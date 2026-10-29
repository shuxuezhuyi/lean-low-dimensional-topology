/-
The actual fixed-point formulas used below are due to Wu Xiaobin,
Li-Zhong-QC-formalization, pinned commit
1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0).
See the retained external source and THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.External.LiZhongQC.Ch07.S27_TeichmullerExistence
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Positive matrix representatives from actual fixed-point normalization

The hypotheses describe the actual attracting and repelling points of the
original hyperbolic transformations. The sign of a determinant-one matrix is
chosen internally. No positivity or missing-entry condition is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Teichmuller

/-- Attracting infinity and repelling zero give a positive diagonal
representative of the same real Möbius transformation. -/
theorem exists_positive_diagonal_of_fixedpoints
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : 2 < |A 0 0 + A 1 1|)
    (hattr : attractingFixedPoint A = extInf)
    (hrep : repellingFixedPoint A = ((0 : ℂ) : ExtPlane)) :
    ∃ A' : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (A' = A ∨ A' = -A) ∧ A' 0 1 = 0 ∧ A' 1 0 = 0 ∧ 1 < A' 0 0 := by
  have hc : A 1 0 = 0 := by
    by_contra hn
    obtain ⟨σ, hσ⟩ := hnf_attr_exists hn
    exact OnePoint.coe_ne_infty _ (hσ.symm.trans hattr)
  have ha : 1 < |A 0 0| := by
    by_contra hn
    have hfinite := ((hnf_fixed_of_eq_zero hc).2 hn).1
    exact OnePoint.coe_ne_infty _ (hfinite.symm.trans hattr)
  have had : A 0 0 * A 1 1 = 1 := by
    simpa only [hc, mul_zero, sub_zero] using hnf_sl2_det A
  have hd : A 1 1 - A 0 0 ≠ 0 := (hnf_core_eq had hA).1
  have hb : A 0 1 = 0 := by
    have hfinite := ((hnf_fixed_of_eq_zero hc).1 ha).2
    have heq : A 0 1 / (A 1 1 - A 0 0) = 0 :=
      Complex.ofReal_injective (OnePoint.coe_injective (hfinite.symm.trans hrep))
    exact (div_eq_zero_iff.mp heq).resolve_right hd
  by_cases hpos : 0 ≤ A 0 0
  · exact ⟨A, Or.inl rfl, hb, hc, by simpa only [abs_of_nonneg hpos] using ha⟩
  · refine ⟨-A, Or.inr rfl, ?_, ?_, ?_⟩
    · simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, hb, neg_zero]
    · simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, hc, neg_zero]
    · change 1 < -A 0 0
      simpa only [abs_of_neg (lt_of_not_ge hpos)] using ha

/-- Attracting one and a negative repelling point give a determinant-one
representative with all entries positive and equal row sums. -/
theorem exists_positive_matrix_of_fixedpoints
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) {r : ℝ}
    (hB : 2 < |B 0 0 + B 1 1|) (hr : r < 0)
    (hattr : attractingFixedPoint B = ((1 : ℂ) : ExtPlane))
    (hrep : repellingFixedPoint B = ((r : ℂ) : ExtPlane)) :
    ∃ B' : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (B' = B ∨ B' = -B) ∧ 0 < B' 0 0 ∧ 0 < B' 0 1 ∧
        0 < B' 1 0 ∧ 0 < B' 1 1 ∧ B' 0 0 + B' 0 1 = B' 1 0 + B' 1 1 := by
  have hc : B 1 0 ≠ 0 := by
    intro heq
    by_cases ha : 1 < |B 0 0|
    · have hinf := ((hnf_fixed_of_eq_zero heq).1 ha).1
      exact OnePoint.coe_ne_infty _ (hattr.symm.trans hinf)
    · have hinf := ((hnf_fixed_of_eq_zero heq).2 ha).2
      exact OnePoint.coe_ne_infty _ (hrep.symm.trans hinf)
  obtain ⟨hε, hε2, hεt, hs, hs2⟩ := hnf_sign_sqrt hB
  have hσ := hnf_attr_eq hc hattr
  have hτ := hnf_rep_eq hc hrep
  obtain ⟨hroot1, hrootr, _, _⟩ := hnf_core_ne (hnf_sl2_det B) hc hε2 hεt hs hs2 hσ hτ
  have hrow : B 0 0 + B 0 1 = B 1 0 + B 1 1 := by
    nlinarith [hroot1]
  have hbc : B 0 1 = -B 1 0 * r := by
    have hprod : (r - 1) * (B 1 0 * r + B 0 1) = 0 := by
      linear_combination hrootr - r * hroot1
    have heq := (mul_eq_zero.mp hprod).resolve_left (by linarith : r - 1 ≠ 0)
    linarith
  have hcs : B 1 0 * (1 - r) = Real.sign (B 0 0 + B 1 1) *
      Real.sqrt ((B 0 0 + B 1 1) ^ 2 - 4) := by
    nlinarith [hσ, hτ]
  obtain ⟨P, hPpm, hP00, hP01, hP10, hP11⟩ :
      ∃ P : Matrix.SpecialLinearGroup (Fin 2) ℝ, (P = B ∨ P = -B) ∧
        P 0 0 = Real.sign (B 0 0 + B 1 1) * B 0 0 ∧
        P 0 1 = Real.sign (B 0 0 + B 1 1) * B 0 1 ∧
        P 1 0 = Real.sign (B 0 0 + B 1 1) * B 1 0 ∧
        P 1 1 = Real.sign (B 0 0 + B 1 1) * B 1 1 := by
    rcases hε with hn | hp
    · refine ⟨-B, Or.inr rfl, ?_, ?_, ?_, ?_⟩ <;>
        simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, hn, neg_one_mul]
    · refine ⟨B, Or.inl rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [hp, one_mul]
  have hPcS : P 1 0 * (1 - r) = Real.sqrt ((B 0 0 + B 1 1) ^ 2 - 4) := by
    rw [hP10]
    calc
      _ = Real.sign (B 0 0 + B 1 1) * (B 1 0 * (1 - r)) := by ring
      _ = Real.sign (B 0 0 + B 1 1) *
          (Real.sign (B 0 0 + B 1 1) * Real.sqrt ((B 0 0 + B 1 1) ^ 2 - 4)) := by rw [hcs]
      _ = _ := by rw [← mul_assoc, ← pow_two, hε2, one_mul]
  have hPc : 0 < P 1 0 := by
    by_contra hn
    have hle := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (by linarith : 0 ≤ 1 - r)
    rw [hPcS] at hle
    exact not_le_of_gt hs hle
  have hPtrace : P 0 0 + P 1 1 = |B 0 0 + B 1 1| := by
    rw [hP00, hP11, ← mul_add]
    have heq := congrArg (fun x : ℝ => Real.sign (B 0 0 + B 1 1) * x) hεt
    rw [← mul_assoc, ← pow_two, hε2, one_mul] at heq
    exact heq.symm
  have hPpos : 0 < P 0 0 + P 1 1 := by rw [hPtrace]; linarith
  have hPbc : P 0 1 = -P 1 0 * r := by rw [hP01, hP10, hbc]; ring
  have hPb : 0 < P 0 1 := by
    rw [hPbc]
    exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr hPc) hr
  have hPad : 0 < P 0 0 * P 1 1 := by
    nlinarith [hnf_sl2_det P, mul_pos hPb hPc]
  have hPa : 0 < P 0 0 := by
    by_contra hn
    have hdpos : 0 < P 1 1 := by linarith
    exact not_le_of_gt hPad (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hdpos.le)
  have hPd : 0 < P 1 1 := by
    by_contra hn
    exact not_le_of_gt hPad (mul_nonpos_of_nonneg_of_nonpos hPa.le (le_of_not_gt hn))
  refine ⟨P, hPpm, hPa, hPb, hPc, hPd, ?_⟩
  rw [hP00, hP01, hP10, hP11]
  linear_combination Real.sign (B 0 0 + B 1 1) * hrow

end LowDimensionalTopology.Geometry.Teichmuller
