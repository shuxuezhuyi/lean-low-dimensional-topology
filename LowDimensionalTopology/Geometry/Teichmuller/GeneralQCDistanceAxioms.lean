/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCDistanceRepresentatives

/-!
# The full-log distance on general QC-marked classes

The original distance vanishes on the diagonal, is symmetric, and satisfies
the triangle inequality. All comparison maps have their original targets and
marking homotopies. A strict distance bound supplies an actual comparison
between either fixed pair of representatives, for use in the completeness proof.
No compactness, genus or existence of an extremal map is assumed here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

universe u v

/-- The actual fixed comparison family always contains the transition of markings. -/
theorem fixedLogDilatations_nonempty {R : Surface.{u}} (m n : Marked.{u, v} R) :
    (fixedLogDilatations m n).Nonempty := by
  let f := m.marking.symm.trans n.marking
  have hf : LiZhongQC.IsQCRS f :=
    LiZhongQC.s28q_isQCRS_trans (LiZhongQC.s28q_isQCRS_symm m.qc) n.qc
  refine ⟨_, f, hf, ?_, rfl⟩
  have hh : ((m.marking.trans f : R.carrier ≃ₜ n.target.carrier) :
      C(R.carrier, n.target.carrier)) = (n.marking : C(R.carrier, n.target.carrier)) := by
    ext x
    exact congrArg n.marking (m.marking.symm_apply_apply x)
  rw [hh]

/-- The identity comparison has full-log dilatation zero on the same actual class. -/
theorem distance_self {R : Surface.{u}} (p : Space.{u, v} R) : distance p p = 0 := by
  refine Quotient.inductionOn p fun m => ?_
  change distance (mk m) (mk m) = 0
  apply le_antisymm ?_ (distance_nonneg _ _)
  rw [distance_eq_fixed_inf]
  have h1 : LiZhongQC.IsKQCRS (Homeomorph.refl m.target.carrier) 1 :=
    (LiZhongQC.isKQCRS_one_iff _).2
      (LiZhongQC.isBiholomorphic_id : LiZhongQC.IsBiholomorphic
        ((Homeomorph.refl m.target.carrier : _ ≃ₜ _) :
          m.target.carrier → m.target.carrier))
  have hK : LiZhongQC.maxDilatationRS (Homeomorph.refl m.target.carrier : _ → _) = 1 :=
    le_antisymm (by simpa using LiZhongQC.maxDilatationRS_le h1)
      (LiZhongQC.s29_m_one_le_maxDilatationRS ⟨1, h1⟩)
  have hm : Real.log (LiZhongQC.maxDilatationRS
      (Homeomorph.refl m.target.carrier : _ → _)).toReal ∈ fixedLogDilatations m m :=
    ⟨Homeomorph.refl _, ⟨1, h1⟩, ContinuousMap.Homotopic.refl _, rfl⟩
  simpa only [hK, ENNReal.toReal_one, Real.log_one] using
    csInf_le (fixedLogDilatations_bddBelow m m) hm

private theorem comparison_inverse_homotopy {R : Surface.{u}}
    {m n : Marked.{u, v} R} {f : m.target.carrier ≃ₜ n.target.carrier}
    (hh : ContinuousMap.Homotopic
      ((m.marking.trans f : R.carrier ≃ₜ n.target.carrier) :
        C(R.carrier, n.target.carrier))
      (n.marking : C(R.carrier, n.target.carrier))) :
    ContinuousMap.Homotopic
      ((n.marking.trans f.symm : R.carrier ≃ₜ m.target.carrier) :
        C(R.carrier, m.target.carrier))
      (m.marking : C(R.carrier, m.target.carrier)) := by
  rw [LiZhongQC.coe_homeomorph_trans] at hh ⊢
  have hcancel : (f.symm : C(n.target.carrier, m.target.carrier)).comp
      ((f : C(m.target.carrier, n.target.carrier)).comp
        (m.marking : C(R.carrier, m.target.carrier))) =
      (m.marking : C(R.carrier, m.target.carrier)) := by
    ext x
    exact f.symm_apply_apply _
  have h := (ContinuousMap.Homotopic.refl
    (f.symm : C(n.target.carrier, m.target.carrier))).comp hh.symm
  rwa [hcancel] at h

/-- Inverting genuine compatible comparisons proves symmetry of the original infimum. -/
theorem distance_symm {R : Surface.{u}} (p q : Space.{u, v} R) :
    distance p q = distance q p := by
  refine Quotient.inductionOn₂ p q fun m n => ?_
  change distance (mk m) (mk n) = distance (mk n) (mk m)
  rw [distance_eq_fixed_inf, distance_eq_fixed_inf]
  have key : ∀ a b : Marked.{u, v} R, ∀ d ∈ fixedLogDilatations a b,
      ∃ e ∈ fixedLogDilatations b a, e ≤ d := by
    rintro a b d ⟨f, hf, hh, rfl⟩
    obtain ⟨hi, hle⟩ := LiZhongQC.s29_m_maxDil_symm_le hf
    refine ⟨_, ⟨f.symm, hi, comparison_inverse_homotopy hh, rfl⟩, ?_⟩
    have h := LiZhongQC.s29_m_half_log_mono hi hf hle
    linarith
  exact LiZhongQC.s29_m_sInf_eq (fixedLogDilatations_bddBelow m n)
    (fixedLogDilatations_bddBelow n m) (key m n) (key n m)

/-- Composing actual fixed comparisons proves the full-log triangle inequality. -/
theorem distance_triangle {R : Surface.{u}} (p q r : Space.{u, v} R) :
    distance p r ≤ distance p q + distance q r := by
  refine Quotient.inductionOn₃ p q r fun m n k => ?_
  change distance (mk m) (mk k) ≤ distance (mk m) (mk n) + distance (mk n) (mk k)
  rw [distance_eq_fixed_inf, distance_eq_fixed_inf, distance_eq_fixed_inf]
  have key : ∀ a ∈ fixedLogDilatations m n, ∀ b ∈ fixedLogDilatations n k,
      ∃ c ∈ fixedLogDilatations m k, c ≤ a + b := by
    rintro a ⟨f, hf, hhf, rfl⟩ b ⟨g, hg, hhg, rfl⟩
    obtain ⟨hc, hK⟩ := LiZhongQC.eq23_4
      (LiZhongQC.s29_m_isKQCRS_maxDil hf) (LiZhongQC.s29_m_isKQCRS_maxDil hg)
    have hqc : LiZhongQC.IsQCRS (f.trans g) := ⟨_, hc⟩
    refine ⟨_, ⟨f.trans g, hqc, ?_, rfl⟩, ?_⟩
    · rw [LiZhongQC.coe_homeomorph_trans] at hhf hhg ⊢
      rw [LiZhongQC.coe_homeomorph_trans]
      have h := (ContinuousMap.Homotopic.refl
        (g : C(n.target.carrier, k.target.carrier))).comp hhf
      rw [← ContinuousMap.comp_assoc] at h
      exact h.trans hhg
    · have hne : LiZhongQC.maxDilatationRS g * LiZhongQC.maxDilatationRS f ≠ ⊤ :=
        ENNReal.mul_ne_top (LiZhongQC.s29_m_maxDilatationRS_ne_top hg)
          (LiZhongQC.s29_m_maxDilatationRS_ne_top hf)
      have hmono : (LiZhongQC.maxDilatationRS (f.trans g)).toReal ≤
          (LiZhongQC.maxDilatationRS g).toReal *
            (LiZhongQC.maxDilatationRS f).toReal := by
        rw [← ENNReal.toReal_mul]
        exact ENNReal.toReal_mono hne hK
      have hpos := LiZhongQC.s29_m_one_le_toReal hqc
      have hfpos := LiZhongQC.s29_m_one_le_toReal hf
      have hgpos := LiZhongQC.s29_m_one_le_toReal hg
      have hlog := Real.log_le_log (by linarith) hmono
      rw [Real.log_mul (by linarith) (by linarith)] at hlog
      linarith
  have hleft : sInf (fixedLogDilatations m k) - sInf (fixedLogDilatations n k) ≤
      sInf (fixedLogDilatations m n) := by
    apply le_csInf (fixedLogDilatations_nonempty m n)
    intro a ha
    have hright : sInf (fixedLogDilatations m k) - a ≤
        sInf (fixedLogDilatations n k) := by
      apply le_csInf (fixedLogDilatations_nonempty n k)
      intro b hb
      obtain ⟨c, hc, hcab⟩ := key a ha b hb
      have h := csInf_le (fixedLogDilatations_bddBelow m k) hc
      linarith
    linarith
  linarith

/-- A strict original distance bound produces a genuine QC comparison between
the prescribed original representatives, with the same full-log bound. -/
theorem exists_comparison_of_distance_lt {R : Surface.{u}}
    (m n : Marked.{u, v} R) {ε : ℝ} (h : distance (mk m) (mk n) < ε) :
    ∃ f : m.target.carrier ≃ₜ n.target.carrier,
      LiZhongQC.IsQCRS f ∧
      ContinuousMap.Homotopic
        ((m.marking.trans f : R.carrier ≃ₜ n.target.carrier) :
          C(R.carrier, n.target.carrier))
        (n.marking : C(R.carrier, n.target.carrier)) ∧
      Real.log (LiZhongQC.maxDilatationRS f).toReal < ε := by
  rw [distance_eq_fixed_inf] at h
  obtain ⟨d, ⟨f, hf, hh, rfl⟩, hd⟩ :=
    exists_lt_of_csInf_lt (fixedLogDilatations_nonempty m n) h
  exact ⟨f, hf, hh, hd⟩

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
