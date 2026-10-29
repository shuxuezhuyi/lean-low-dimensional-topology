module

public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The literal finite trace data of a normalized generator system

The data use the two base generators and exactly their positive and negative
single powers and the positive and negative powers of their ordered product.
No additional inverse-product words or standard surface-group presentation
are required. Signs of determinant-one representatives are retained.

The matrix trace and sign APIs are reused from Wu Xiaobin,
Li-Zhong-QC-formalization, commit
1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0).
See THIRD_PARTY_NOTICES.md and the retained external source.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set

namespace LowDimensionalTopology.Geometry.Teichmuller

abbrev TraceSL := Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The original finite list of absolute trace observations. -/
def SameBookTraceData {m : ℕ} (γ δ : Fin (m + 2) → TraceSL) : Prop :=
  |LiZhongQC.slTrace (δ 0 * δ 1)| = |LiZhongQC.slTrace (γ 0 * γ 1)| ∧
  (∀ j, |LiZhongQC.slTrace (δ j)| = |LiZhongQC.slTrace (γ j)|) ∧
  ∀ k, k ≠ 0 → k ≠ 1 →
    |LiZhongQC.slTrace (δ 0 * δ k)| = |LiZhongQC.slTrace (γ 0 * γ k)| ∧
    |LiZhongQC.slTrace ((δ 0)⁻¹ * δ k)| = |LiZhongQC.slTrace ((γ 0)⁻¹ * γ k)| ∧
    |LiZhongQC.slTrace (δ 1 * δ k)| = |LiZhongQC.slTrace (γ 1 * γ k)| ∧
    |LiZhongQC.slTrace ((δ 1)⁻¹ * δ k)| = |LiZhongQC.slTrace ((γ 1)⁻¹ * γ k)| ∧
    |LiZhongQC.slTrace ((δ 0 * δ 1) * δ k)| =
      |LiZhongQC.slTrace ((γ 0 * γ 1) * γ k)| ∧
    |LiZhongQC.slTrace ((δ 0 * δ 1)⁻¹ * δ k)| =
      |LiZhongQC.slTrace ((γ 0 * γ 1)⁻¹ * γ k)|

private theorem trace_comm (A B : TraceSL) :
    LiZhongQC.slTrace (A * B) = LiZhongQC.slTrace (B * A) := by
  simp only [LiZhongQC.slTrace, LiZhongQC.s30e1_mul00, LiZhongQC.s30e1_mul11]
  ring

private theorem diagonal_last {A : TraceSL}
    (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) :
    A 1 1 = (A 0 0)⁻¹ := by
  have hdet := LiZhongQC.hnf_sl2_det A
  rw [h01, h10, zero_mul, sub_zero] at hdet
  exact eq_inv_of_mul_eq_one_right (by simpa only [mul_comm] using hdet)

private theorem diagonal_determined {A A' : TraceSL}
    (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) (ha : 1 < A 0 0)
    (h01' : A' 0 1 = 0) (h10' : A' 1 0 = 0) (ha' : 1 < A' 0 0)
    (ht : |LiZhongQC.slTrace A'| = |LiZhongQC.slTrace A|) : A' = A := by
  have hd := diagonal_last h01 h10
  have hd' := diagonal_last h01' h10'
  have ht' : |A' 0 0 + (A' 0 0)⁻¹| = |A 0 0 + (A 0 0)⁻¹| := by
    simpa only [LiZhongQC.slTrace, hd, hd'] using ht
  have he := LiZhongQC.s30e1_diag_pm (by nlinarith : 1 < A 0 0 ^ 2)
    (by nlinarith : 1 < A' 0 0 ^ 2) ht'
  have h00 : A' 0 0 = A 0 0 := by
    rcases he with h | h
    · exact h
    · linarith
  exact LiZhongQC.s30l_eq_of_entries h00 (h01'.trans h01.symm)
    (h10'.trans h10.symm) (by rw [hd', hd, h00])

private theorem positive_pair_determined {A A' B B' : TraceSL}
    (hA : A 0 1 = 0 ∧ A 1 0 = 0 ∧ 1 < A 0 0)
    (hA' : A' 0 1 = 0 ∧ A' 1 0 = 0 ∧ 1 < A' 0 0)
    (hB : 0 < B 0 0 ∧ 0 < B 0 1 ∧ 0 < B 1 0 ∧ 0 < B 1 1 ∧
      B 0 0 + B 0 1 = B 1 0 + B 1 1)
    (hB' : 0 < B' 0 0 ∧ 0 < B' 0 1 ∧ 0 < B' 1 0 ∧ 0 < B' 1 1 ∧
      B' 0 0 + B' 0 1 = B' 1 0 + B' 1 1)
    (htA : |LiZhongQC.slTrace A'| = |LiZhongQC.slTrace A|)
    (htB : |LiZhongQC.slTrace B'| = |LiZhongQC.slTrace B|)
    (htAB : |LiZhongQC.slTrace (A' * B')| = |LiZhongQC.slTrace (A * B)|) :
    A' = A ∧ B' = B := by
  have hAe := diagonal_determined hA.1 hA.2.1 hA.2.2 hA'.1 hA'.2.1 hA'.2.2 htA
  subst A'
  have hd := diagonal_last hA.1 hA.2.1
  have hdpos : 0 < A 1 1 := by rw [hd]; exact inv_pos.mpr (by linarith [hA.2.2])
  have htb : B' 0 0 + B' 1 1 = B 0 0 + B 1 1 := by
    simpa only [LiZhongQC.slTrace, abs_of_pos (add_pos hB.1 hB.2.2.2.1),
      abs_of_pos (add_pos hB'.1 hB'.2.2.2.1)] using htB
  have hp : ∀ C : TraceSL, 0 < C 0 0 → 0 < C 1 1 →
      0 < LiZhongQC.slTrace (A * C) := by
    intro C hc0 hc1
    simp only [LiZhongQC.slTrace, LiZhongQC.s30e1_mul00, LiZhongQC.s30e1_mul11,
      hA.1, hA.2.1, zero_mul, zero_add, add_zero]
    exact add_pos (mul_pos (by linarith [hA.2.2]) hc0) (mul_pos hdpos hc1)
  have htab : A 0 0 * B' 0 0 + A 1 1 * B' 1 1 =
      A 0 0 * B 0 0 + A 1 1 * B 1 1 := by
    rw [abs_of_pos (hp B' hB'.1 hB'.2.2.2.1),
      abs_of_pos (hp B hB.1 hB.2.2.2.1)] at htAB
    simpa only [LiZhongQC.slTrace, LiZhongQC.s30e1_mul00, LiZhongQC.s30e1_mul11,
      hA.1, hA.2.1, zero_mul, zero_add, add_zero] using htAB
  have hdiff : A 0 0 - A 1 1 ≠ 0 := by
    intro h
    have heq : A 0 0 = A 1 1 := sub_eq_zero.mp h
    have hdet := LiZhongQC.hnf_sl2_det A
    rw [hA.1, hA.2.1, zero_mul, sub_zero, ← heq] at hdet
    nlinarith [hA.2.2]
  have h00 : B' 0 0 = B 0 0 := by
    have hz : (A 0 0 - A 1 1) * (B' 0 0 - B 0 0) = 0 := by
      linear_combination htab - A 1 1 * htb
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hdiff)
  have h11 : B' 1 1 = B 1 1 := by linarith
  have hdB := LiZhongQC.hnf_sl2_det B
  have hdB' := LiZhongQC.hnf_sl2_det B'
  have hc : B' 1 0 = B 1 0 := by
    have hf : (B' 1 0 - B 1 0) * (B' 1 0 + B 0 1) = 0 := by
      rw [h00, h11] at hdB'
      have hrow' : B 0 0 + B' 0 1 = B' 1 0 + B 1 1 := by
        simpa only [h00, h11] using hB'.2.2.2.2
      linear_combination hdB - hdB' -
        B' 1 0 * hrow' + B' 1 0 * (hB.2.2.2.2)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right (by
      linarith [hB'.2.2.1, hB.2.1]))
  have hb : B' 0 1 = B 0 1 := by
    linarith [hB.2.2.2.2, hB'.2.2.2.2]
  exact ⟨rfl, LiZhongQC.s30l_eq_of_entries h00 hb hc h11⟩

private theorem trace_basis_separates {A B C C' : TraceSL}
    (hA : A 0 1 = 0 ∧ A 1 0 = 0 ∧ 1 < A 0 0)
    (hb : B 0 1 ≠ 0) (hc : B 1 0 ≠ 0)
    (h0 : LiZhongQC.slTrace C' = LiZhongQC.slTrace C)
    (h1 : LiZhongQC.slTrace (A * C') = LiZhongQC.slTrace (A * C))
    (h2 : LiZhongQC.slTrace (B * C') = LiZhongQC.slTrace (B * C))
    (h3 : LiZhongQC.slTrace ((A * B) * C') = LiZhongQC.slTrace ((A * B) * C)) : C' = C := by
  have hd := diagonal_last hA.1 hA.2.1
  have hs : A 0 0 ≠ 0 := by linarith [hA.2.2]
  have hs2 : A 0 0 ^ 2 ≠ 1 := by nlinarith [hA.2.2]
  simp only [LiZhongQC.slTrace, LiZhongQC.s30e1_mul00, LiZhongQC.s30e1_mul01,
    LiZhongQC.s30e1_mul10, LiZhongQC.s30e1_mul11, hA.1, hA.2.1, hd,
    zero_mul, zero_add, add_zero] at h0 h1 h2 h3
  obtain ⟨e00, e10, e01, e11⟩ := LiZhongQC.s30e1_det_real
    (s := A 0 0) (a := B 0 0) (b := B 1 0) (c := B 0 1) (d := B 1 1)
    (x := C' 0 0 - C 0 0) (y := C' 1 0 - C 1 0)
    (z := C' 0 1 - C 0 1) (w := C' 1 1 - C 1 1) hs hs2 hc hb
    (by linarith) (by nlinarith) (by nlinarith) (by nlinarith)
  exact LiZhongQC.s30l_eq_of_entries (sub_eq_zero.mp e00) (sub_eq_zero.mp e01)
    (sub_eq_zero.mp e10) (sub_eq_zero.mp e11)

private theorem trace_product_signed {D C C' : TraceSL}
    (hD : LiZhongQC.slTrace D ≠ 0) (hC : LiZhongQC.slTrace C ≠ 0)
    (ht : LiZhongQC.slTrace C' = LiZhongQC.slTrace C)
    (h1 : |LiZhongQC.slTrace (D * C')| = |LiZhongQC.slTrace (D * C)|)
    (h2 : |LiZhongQC.slTrace (D⁻¹ * C')| = |LiZhongQC.slTrace (D⁻¹ * C)|) :
    LiZhongQC.slTrace (D * C') = LiZhongQC.slTrace (D * C) := by
  have hsum' := LiZhongQC.s30e1_trace_identity C' D
  have hsum := LiZhongQC.s30e1_trace_identity C D
  rw [trace_comm C' D, trace_comm C' D⁻¹, ht] at hsum'
  rw [trace_comm C D, trace_comm C D⁻¹] at hsum
  exact LiZhongQC.s30e1_sign h1 h2 (hsum'.trans hsum.symm)
    (by rw [hsum]; exact mul_ne_zero hC hD)

private theorem further_determined {A B C C' : TraceSL}
    (hA : A 0 1 = 0 ∧ A 1 0 = 0 ∧ 1 < A 0 0)
    (hB : 0 < B 0 0 ∧ 0 < B 0 1 ∧ 0 < B 1 0 ∧ 0 < B 1 1)
    (hC : LiZhongQC.slTrace C ≠ 0)
    (h0 : |LiZhongQC.slTrace C'| = |LiZhongQC.slTrace C|)
    (h1 : |LiZhongQC.slTrace (A * C')| = |LiZhongQC.slTrace (A * C)|)
    (h1' : |LiZhongQC.slTrace (A⁻¹ * C')| = |LiZhongQC.slTrace (A⁻¹ * C)|)
    (h2 : |LiZhongQC.slTrace (B * C')| = |LiZhongQC.slTrace (B * C)|)
    (h2' : |LiZhongQC.slTrace (B⁻¹ * C')| = |LiZhongQC.slTrace (B⁻¹ * C)|)
    (h3 : |LiZhongQC.slTrace ((A * B) * C')| = |LiZhongQC.slTrace ((A * B) * C)|)
    (h3' : |LiZhongQC.slTrace ((A * B)⁻¹ * C')| = |LiZhongQC.slTrace ((A * B)⁻¹ * C)|) :
    C' = C ∨ C' = -C := by
  have hd := diagonal_last hA.1 hA.2.1
  have ha : 0 < A 0 0 := by linarith [hA.2.2]
  have hdpos : 0 < A 1 1 := by rw [hd]; exact inv_pos.mpr ha
  have hAt : LiZhongQC.slTrace A ≠ 0 := (add_pos ha hdpos).ne'
  have hBt : LiZhongQC.slTrace B ≠ 0 := (add_pos hB.1 hB.2.2.2).ne'
  have hABt : LiZhongQC.slTrace (A * B) ≠ 0 := by
    have hpos : 0 < LiZhongQC.slTrace (A * B) := by
      simp only [LiZhongQC.slTrace, LiZhongQC.s30e1_mul00, LiZhongQC.s30e1_mul11,
        hA.1, hA.2.1, zero_mul, zero_add, add_zero]
      exact add_pos (mul_pos ha hB.1) (mul_pos hdpos hB.2.2.2)
    exact hpos.ne'
  obtain ⟨T, hT, ht⟩ : ∃ T : TraceSL, (T = C' ∨ T = -C') ∧
      LiZhongQC.slTrace T = LiZhongQC.slTrace C := by
    rcases abs_eq_abs.mp h0 with h | h
    · exact ⟨C', Or.inl rfl, h⟩
    · exact ⟨-C', Or.inr rfl, by rw [LiZhongQC.s30e1_slTrace_neg, h, neg_neg]⟩
  have hchange (D : TraceSL) :
      |LiZhongQC.slTrace (D * T)| = |LiZhongQC.slTrace (D * C')| :=
    LiZhongQC.s30e1_abs_tr_pm hT
  have he : T = C := trace_basis_separates hA hB.2.1.ne' hB.2.2.1.ne' ht
    (trace_product_signed hAt hC ht ((hchange A).trans h1) ((hchange A⁻¹).trans h1'))
    (trace_product_signed hBt hC ht ((hchange B).trans h2) ((hchange B⁻¹).trans h2'))
    (trace_product_signed hABt hC ht ((hchange (A * B)).trans h3)
      ((hchange (A * B)⁻¹).trans h3'))
  rcases hT with h | h
  · exact Or.inl (h.symm.trans he)
  · exact Or.inr (neg_eq_iff_eq_neg.mp (h.symm.trans he))

private theorem abs_trace_pm {A B : TraceSL} (h : A = B ∨ A = -B) :
    |LiZhongQC.slTrace A| = |LiZhongQC.slTrace B| := by
  rcases h with rfl | rfl
  · rfl
  · rw [LiZhongQC.s30e1_slTrace_neg, abs_neg]

private theorem pm_of_common {A B T : TraceSL}
    (h : T = A ∨ T = -A) (k : T = B ∨ T = -B) : B = A ∨ B = -A := by
  rcases h with h | h <;> rcases k with k | k
  · exact Or.inl (k.symm.trans h)
  · exact Or.inr (neg_eq_iff_eq_neg.mp (k.symm.trans h))
  · exact Or.inr (k.symm.trans h)
  · exact Or.inl (neg_injective (k.symm.trans h))

/-- The original finite observations separate any normalized finite matrix
system. The geometric fixed-point normalization supplies the positive base
representatives in the original-surface consumer. -/
theorem finite_book_traces_separate_positive_representatives {m : ℕ}
    {γ δ : Fin (m + 2) → TraceSL} (htr : SameBookTraceData γ δ)
    (hzero : ∀ j, LiZhongQC.slTrace (γ j) ≠ 0)
    (A B A' B' : TraceSL)
    (hAg : A = γ 0 ∨ A = -(γ 0)) (hBg : B = γ 1 ∨ B = -(γ 1))
    (hAd : A' = δ 0 ∨ A' = -(δ 0)) (hBd : B' = δ 1 ∨ B' = -(δ 1))
    (hA : A 0 1 = 0 ∧ A 1 0 = 0 ∧ 1 < A 0 0)
    (hA' : A' 0 1 = 0 ∧ A' 1 0 = 0 ∧ 1 < A' 0 0)
    (hB : 0 < B 0 0 ∧ 0 < B 0 1 ∧ 0 < B 1 0 ∧ 0 < B 1 1 ∧
      B 0 0 + B 0 1 = B 1 0 + B 1 1)
    (hB' : 0 < B' 0 0 ∧ 0 < B' 0 1 ∧ 0 < B' 1 0 ∧ 0 < B' 1 1 ∧
      B' 0 0 + B' 0 1 = B' 1 0 + B' 1 1) :
    ∀ j, δ j = γ j ∨ δ j = -(γ j) := by
  have hta : |LiZhongQC.slTrace A'| = |LiZhongQC.slTrace A| :=
    (abs_trace_pm hAd).trans ((htr.2.1 0).trans (abs_trace_pm hAg).symm)
  have htb : |LiZhongQC.slTrace B'| = |LiZhongQC.slTrace B| :=
    (abs_trace_pm hBd).trans ((htr.2.1 1).trans (abs_trace_pm hBg).symm)
  have htab : |LiZhongQC.slTrace (A' * B')| = |LiZhongQC.slTrace (A * B)| :=
    (abs_trace_pm (LiZhongQC.s30e1_pm_mul hAd hBd)).trans
      (htr.1.trans (abs_trace_pm (LiZhongQC.s30e1_pm_mul hAg hBg)).symm)
  obtain ⟨hAe, hBe⟩ := positive_pair_determined hA hA' hB hB' hta htb htab
  subst A'
  subst B'
  intro j
  by_cases hj0 : j = 0
  · subst j
    exact pm_of_common hAg hAd
  by_cases hj1 : j = 1
  · subst j
    exact pm_of_common hBg hBd
  obtain ⟨t1, t1', t2, t2', t3, t3'⟩ := htr.2.2 j hj0 hj1
  have transfer (D E D0 E0 : TraceSL)
      (hD : D = D0 ∨ D = -D0) (hE : E = E0 ∨ E = -E0)
      (h : |LiZhongQC.slTrace (E0 * δ j)| = |LiZhongQC.slTrace (D0 * γ j)|) :
      |LiZhongQC.slTrace (E * δ j)| = |LiZhongQC.slTrace (D * γ j)| :=
    (LiZhongQC.s30e1_abs_tr_pm_left hE).trans
      (h.trans (LiZhongQC.s30e1_abs_tr_pm_left hD).symm)
  exact further_determined hA ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1⟩ (hzero j) (htr.2.1 j)
    (transfer A A _ _ hAg hAd t1)
    (transfer A⁻¹ A⁻¹ _ _ (LiZhongQC.s30e1_pm_inv hAg) (LiZhongQC.s30e1_pm_inv hAd) t1')
    (transfer B B _ _ hBg hBd t2)
    (transfer B⁻¹ B⁻¹ _ _ (LiZhongQC.s30e1_pm_inv hBg) (LiZhongQC.s30e1_pm_inv hBd) t2')
    (transfer (A * B) (A * B) _ _ (LiZhongQC.s30e1_pm_mul hAg hBg)
      (LiZhongQC.s30e1_pm_mul hAd hBd) t3)
    (transfer (A * B)⁻¹ (A * B)⁻¹ _ _
      (LiZhongQC.s30e1_pm_inv (LiZhongQC.s30e1_pm_mul hAg hBg))
      (LiZhongQC.s30e1_pm_inv (LiZhongQC.s30e1_pm_mul hAd hBd)) t3')

end LowDimensionalTopology.Geometry.Teichmuller
