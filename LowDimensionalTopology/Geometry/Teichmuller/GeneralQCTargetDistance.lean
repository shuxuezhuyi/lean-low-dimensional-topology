/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCDistanceAxioms
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCTargetUniverse

/-!
# Preserve the original distance under actual target-universe transport

Each original marking supplies a genuine biholomorphic identification with
its target on the reference universe. Transporting actual fixed comparisons
in both directions preserves their marking homotopies and cannot increase
their logarithmic maximal dilatations. Thus the original class distance is
unchanged. The target carriers and native atlases remain explicit.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open LiZhongQC
universe u v

/-- The actual biholomorphic target identifications preserve the same original
full-log distance, including for independently sized original targets. -/
theorem distance_eq_sourceCarrierRepresentatives {R : Surface.{u}}
    (m n : Marked.{u, v} R) :
    distance (mk m) (mk n) =
      distance (mk m.sourceCarrierRepresentative) (mk n.sourceCarrierRepresentative) := by
  let a := m.sourceCarrierProjection
  let b := n.sourceCarrierProjection
  rw [distance_eq_fixed_inf, distance_eq_fixed_inf]
  apply s29_m_sInf_eq (fixedLogDilatations_bddBelow m n)
    (fixedLogDilatations_bddBelow m.sourceCarrierRepresentative n.sourceCarrierRepresentative)
  · rintro d ⟨f, hf, hh, rfl⟩
    let g := a.trans (f.trans b.symm)
    obtain ⟨hg, hK⟩ := s29_m_maxDil_conj_biholo hf
      m.sourceCarrierProjection_biholomorphic
      n.sourceCarrierProjection_biholomorphic.homeomorph_symm
    refine ⟨_, ⟨g, hg, ?_, rfl⟩, ?_⟩
    · obtain ⟨H⟩ := hh
      refine ⟨{ toFun := fun tx => b.symm (H tx)
                continuous_toFun := b.symm.continuous.comp H.continuous_toFun
                map_zero_left := ?_
                map_one_left := ?_ }⟩
      · intro x
        change b.symm (H (0, x)) = b.symm (f (a (a.symm (m.marking x))))
        calc
          b.symm (H (0, x)) = b.symm (f (m.marking x)) :=
            congrArg b.symm (H.map_zero_left x)
          _ = b.symm (f (a (a.symm (m.marking x)))) := by rw [a.apply_symm_apply]
      · intro x
        exact congrArg b.symm (H.map_one_left x)
    · have h : (1 / 2 : ℝ) * Real.log (maxDilatationRS g).toReal ≤
          (1 / 2 : ℝ) * Real.log (maxDilatationRS f).toReal :=
        s29_m_half_log_mono hg hf hK
      have hfull : Real.log (maxDilatationRS g).toReal ≤
          Real.log (maxDilatationRS f).toReal := by
        linarith only [h]
      exact hfull
  · rintro d ⟨f, hf, hh, rfl⟩
    let g := a.symm.trans (f.trans b)
    obtain ⟨hg, hK⟩ := s29_m_maxDil_conj_biholo hf
      m.sourceCarrierProjection_biholomorphic.homeomorph_symm
      n.sourceCarrierProjection_biholomorphic
    refine ⟨_, ⟨g, hg, ?_, rfl⟩, ?_⟩
    · obtain ⟨H⟩ := hh
      refine ⟨{ toFun := fun tx => b (H tx)
                continuous_toFun := b.continuous.comp H.continuous_toFun
                map_zero_left := ?_
                map_one_left := ?_ }⟩
      · intro x
        exact congrArg b (H.map_zero_left x)
      · intro x
        change b (H (1, x)) = n.marking x
        calc
          b (H (1, x)) = b (b.symm (n.marking x)) := congrArg b (H.map_one_left x)
          _ = n.marking x := b.apply_symm_apply _
    · have h : (1 / 2 : ℝ) * Real.log (maxDilatationRS g).toReal ≤
          (1 / 2 : ℝ) * Real.log (maxDilatationRS f).toReal :=
        s29_m_half_log_mono hg hf hK
      linarith

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
