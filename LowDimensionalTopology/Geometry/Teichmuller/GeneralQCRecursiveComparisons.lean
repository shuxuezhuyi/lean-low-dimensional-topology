/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCMarkingCoefficients
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Recursively chosen actual comparisons

The original distance infimum supplies a successor marking on its actual
target. Its transition has the prescribed small logarithmic dilatation.
Iteration produces original representatives with uniformly subunit compatible
coefficients and a genuine Cauchy sequence in the closed Banach subspace.
These representatives are constructed here; they are not supplied as inputs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane BigOperators

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open LiZhongQC
universe u

private theorem log_maxDilatation_trans_le
    {S T U : Surface.{u}} (f : S.carrier ≃ₜ T.carrier) (g : T.carrier ≃ₜ U.carrier)
    (hf : IsQCRS f) (hg : IsQCRS g) :
    Real.log (maxDilatationRS (f.trans g)).toReal ≤
      Real.log (maxDilatationRS f).toReal + Real.log (maxDilatationRS g).toReal := by
  obtain ⟨hc, -⟩ := eq23_4 (s29_m_isKQCRS_maxDil hf) (s29_m_isKQCRS_maxDil hg)
  have hfc := s29_m_one_le_toReal hf
  have hgc := s29_m_one_le_toReal hg
  have hcc := s29_m_one_le_toReal (show IsQCRS (f.trans g) from ⟨_, hc⟩)
  have hle := ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (by linarith [hgc]) (by linarith [hfc])) (maxDilatationRS_le hc)
  have hlog := Real.log_le_log (by linarith [hcc]) hle
  rw [Real.log_mul (by linarith [hgc]) (by linarith [hfc])] at hlog
  linarith

/-- The actual infimum supplies a successor marking on a representative's
original target. Both its small transition and cumulative QC cost are proved. -/
theorem exists_successor_marking
    {R : Surface.{u}} (m : Marked.{u, u} R) (q : Space.{u, u} R)
    {ε : ℝ} (h : distance (mk m) q < ε) :
    ∃ n : Marked.{u, u} R, mk n = q ∧
      Real.log (maxDilatationRS (m.marking.symm.trans n.marking)).toReal < ε ∧
      Real.log (maxDilatationRS n.marking).toReal ≤
        Real.log (maxDilatationRS m.marking).toReal + ε := by
  obtain ⟨t, rfl⟩ := Quotient.exists_rep q
  obtain ⟨f, hf, hh, hlog⟩ := exists_comparison_of_distance_lt m t h
  let n : Marked.{u, u} R :=
    { target := t.target
      marking := m.marking.trans f
      qc := s28q_isQCRS_trans m.qc hf }
  have hn : n.Equivalent t :=
    ⟨Homeomorph.refl _, isBiholomorphic_id, hh⟩
  have htrans : m.marking.symm.trans n.marking = f := by
    ext y
    change f (m.marking (m.marking.symm y)) = f y
    rw [m.marking.apply_symm_apply]
  refine ⟨n, Quotient.sound hn, ?_, ?_⟩
  · rwa [htrans]
  · exact (log_maxDilatation_trans_le m.marking f m.qc hf).trans
      (add_le_add_right hlog.le (Real.log (maxDilatationRS m.marking).toReal))

variable (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
  {p : ℍ → R.carrier} (hp : IsUniformization Γ p)

/-- Geometrically close original classes admit internally chosen accumulated
markings whose coefficients stay uniformly inside the unit ball and form a
Cauchy sequence in the actual closed compatible L-infinity subspace. -/
theorem exists_cauchy_marking_coefficients (q : ℕ → Space.{u, u} R)
    (hq : ∀ j, distance (q j) (q (j + 1)) < (1 / 2 : ℝ) ^ j) :
    ∃ g : ℕ → Marked.{u, u} R, (∀ j, mk (g j) = q j) ∧
      ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
        (∀ j, ‖markingCoefficient R hp (g j)‖ ≤ k) ∧
        CauchySeq (fun j => markingCoefficient R hp (g j)) := by
  let Rep := fun j : ℕ => {m : Marked.{u, u} R // mk m = q j}
  have step (j : ℕ) (m : Rep j) : ∃ n : Rep (j + 1),
      Real.log (maxDilatationRS (m.val.marking.symm.trans n.val.marking)).toReal <
          (1 / 2 : ℝ) ^ j ∧
        Real.log (maxDilatationRS n.val.marking).toReal ≤
          Real.log (maxDilatationRS m.val.marking).toReal + (1 / 2 : ℝ) ^ j := by
    obtain ⟨n, hn, ht, hK⟩ := exists_successor_marking m.val (q (j + 1))
      (by rw [m.property]; exact hq j)
    exact ⟨⟨n, hn⟩, ht, hK⟩
  let g : (j : ℕ) → Rep j := Nat.rec
    (motive := fun j => Rep j) ⟨Quotient.out (q 0), Quotient.out_eq (q 0)⟩
    (fun j m => Classical.choose (step j m))
  have hg (j : ℕ) :
      Real.log (maxDilatationRS ((g j).val.marking.symm.trans (g (j + 1)).val.marking)).toReal <
          (1 / 2 : ℝ) ^ j ∧
        Real.log (maxDilatationRS (g (j + 1)).val.marking).toReal ≤
          Real.log (maxDilatationRS (g j).val.marking).toReal + (1 / 2 : ℝ) ^ j :=
    Classical.choose_spec (step j (g j))
  have hsum (j : ℕ) : Real.log (maxDilatationRS (g j).val.marking).toReal ≤
      Real.log (maxDilatationRS (g 0).val.marking).toReal +
        ∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ i := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ]
      linarith [(hg j).2]
  let B := Real.exp (Real.log (maxDilatationRS (g 0).val.marking).toReal + 2)
  have hB : 1 ≤ B := by
    apply Real.one_le_exp_iff.mpr
    linarith [Real.log_nonneg (s29_m_one_le_toReal (g 0).val.qc)]
  let k := (B - 1) / (B + 1)
  have hk₀ : 0 ≤ k := div_nonneg (by linarith) (by linarith)
  have hk : k < 1 := (div_lt_one (by linarith)).2 (by linarith)
  refine ⟨fun j => (g j).val, fun j => (g j).property, k, hk₀, hk, ?_, ?_⟩
  · intro j
    have hA := s29_m_one_le_toReal (g j).val.qc
    have hAB : (maxDilatationRS (g j).val.marking).toReal ≤ B :=
      Real.le_exp_of_log_le ((hsum j).trans (by linarith [sum_geometric_two_le j]))
    apply (markingCoefficient_norm_le R hp (g j).val
      (s29_m_isKQCRS_maxDil (g j).val.qc)).trans
    exact (div_le_div_iff₀ (by linarith [hA]) (by linarith [hB])).2 (by nlinarith)
  · apply cauchySeq_of_le_geometric (1 / 2 : ℝ) 2 (by norm_num)
    intro j
    rw [dist_eq_norm]
    exact (markingCoefficient_sub_norm_le R hp (g j).val (g (j + 1)).val).trans
      (mul_le_mul_of_nonneg_left (hg j).1.le (by norm_num))

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
