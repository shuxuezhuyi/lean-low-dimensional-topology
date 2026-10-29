/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCReferenceChange
public import Mathlib.Tactic.Linarith

/-!
# The original fixed-representative QC distance

Conformal target changes transport actual comparison maps without increasing
maximal dilatation. Thus the infimum over all representatives of two classes
is exactly the original infimum computed with either pair of representatives.
The given reference map preserves even the full fixed-representative family.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

universe u v w

/-- Actual conformal changes of the marked targets transport a compatible QC
comparison without increasing its genuine maximal dilatation. -/
theorem transport_comparison {R : Surface.{u}}
    {m n m' n' : Marked.{u, v} R}
    (hm : m.Equivalent m') (hn : n.Equivalent n')
    {f : m.target.carrier ≃ₜ n.target.carrier} (hf : LiZhongQC.IsQCRS f)
    (hh : ContinuousMap.Homotopic
      ((m.marking.trans f : R.carrier ≃ₜ n.target.carrier) :
        C(R.carrier, n.target.carrier))
      (n.marking : C(R.carrier, n.target.carrier))) :
    ∃ g : m'.target.carrier ≃ₜ n'.target.carrier,
      LiZhongQC.IsQCRS g ∧
      LiZhongQC.maxDilatationRS g ≤ LiZhongQC.maxDilatationRS f ∧
      ContinuousMap.Homotopic
        ((m'.marking.trans g : R.carrier ≃ₜ n'.target.carrier) :
          C(R.carrier, n'.target.carrier))
        (n'.marking : C(R.carrier, n'.target.carrier)) := by
  obtain ⟨c₁, hc₁, hh₁⟩ := hm
  obtain ⟨c₂, hc₂, hh₂⟩ := hn
  obtain ⟨hqc, hle⟩ :=
    LiZhongQC.s29_m_maxDil_conj_biholo hf hc₁.homeomorph_symm hc₂
  refine ⟨c₁.symm.trans (f.trans c₂), hqc, hle, ?_⟩
  rw [LiZhongQC.coe_homeomorph_trans] at hh hh₁ hh₂
  rw [LiZhongQC.coe_homeomorph_trans, LiZhongQC.coe_homeomorph_trans,
    LiZhongQC.coe_homeomorph_trans]
  have hcancel : (c₁.symm : C(m'.target.carrier, m.target.carrier)).comp
      ((c₁ : C(m.target.carrier, m'.target.carrier)).comp
        (m.marking : C(R.carrier, m.target.carrier))) =
      (m.marking : C(R.carrier, m.target.carrier)) := by
    ext x
    exact c₁.symm_apply_apply _
  have hfirst : ContinuousMap.Homotopic
      ((c₁.symm : C(m'.target.carrier, m.target.carrier)).comp
        (m'.marking : C(R.carrier, m'.target.carrier)))
      (m.marking : C(R.carrier, m.target.carrier)) := by
    have h := (ContinuousMap.Homotopic.refl
      (c₁.symm : C(m'.target.carrier, m.target.carrier))).comp hh₁.symm
    rwa [hcancel] at h
  have hmid := (ContinuousMap.Homotopic.refl
    ((c₂ : C(n.target.carrier, n'.target.carrier)).comp
      (f : C(m.target.carrier, n.target.carrier)))).comp hfirst
  have hlast := (ContinuousMap.Homotopic.refl
    (c₂ : C(n.target.carrier, n'.target.carrier))).comp hh
  exact hmid.trans (hlast.trans hh₂)

/-- The original full-log comparison family for two fixed actual markings. -/
def fixedLogDilatations {R : Surface.{u}} (m n : Marked.{u, v} R) : Set ℝ :=
  {d | ∃ f : m.target.carrier ≃ₜ n.target.carrier,
    LiZhongQC.IsQCRS f ∧
      ContinuousMap.Homotopic
        ((m.marking.trans f : R.carrier ≃ₜ n.target.carrier) :
          C(R.carrier, n.target.carrier))
        (n.marking : C(R.carrier, n.target.carrier)) ∧
      d = Real.log (LiZhongQC.maxDilatationRS f).toReal}

/-- Its actual logarithmic values have the same genuine lower bound zero. -/
theorem fixedLogDilatations_bddBelow {R : Surface.{u}} (m n : Marked.{u, v} R) :
    BddBelow (fixedLogDilatations m n) := by
  refine ⟨0, ?_⟩
  rintro d ⟨f, hf, _, rfl⟩
  exact Real.log_nonneg (LiZhongQC.s29_m_one_le_toReal hf)

/-- The class distance is exactly the original fixed-representative infimum. -/
theorem distance_eq_fixed_inf {R : Surface.{u}} (m n : Marked.{u, v} R) :
    distance (mk m) (mk n) = sInf (fixedLogDilatations m n) := by
  unfold distance
  apply LiZhongQC.s29_m_sInf_eq (admissibleLogDilatations_bddBelow (mk m) (mk n))
    (fixedLogDilatations_bddBelow m n)
  · rintro d ⟨m', n', f, hm, hn, hf, hh, rfl⟩
    have hm' : m'.Equivalent m := Quotient.exact hm
    have hn' : n'.Equivalent n := Quotient.exact hn
    obtain ⟨g, hg, hK, hhg⟩ := transport_comparison hm' hn' hf hh
    refine ⟨_, ⟨g, hg, hhg, rfl⟩, ?_⟩
    have hlog := LiZhongQC.s29_m_half_log_mono hg hf hK
    linarith
  · rintro d ⟨f, hf, hh, hd⟩
    exact ⟨d, ⟨m, n, f, rfl, rfl, hf, hh, hd⟩, le_rfl⟩

/-- The literal fixed-marking comparison family is unchanged by the reference map. -/
theorem reference_fixedLogDilatations_eq {R : Surface.{u}} {R1 : Surface.{w}}
    (e : R.carrier ≃ₜ R1.carrier) (he : LiZhongQC.IsQCRS e)
    (m n : Marked.{u, v} R) :
    fixedLogDilatations (referenceMarked e he m) (referenceMarked e he n) =
      fixedLogDilatations m n := by
  ext d
  constructor
  · rintro ⟨f, hf, hh, hd⟩
    have hback := hh.comp (ContinuousMap.Homotopic.refl
      (e : C(R.carrier, R1.carrier)))
    have hm :
        (((referenceMarked e he m).marking.trans f : R1.carrier ≃ₜ n.target.carrier) :
          C(R1.carrier, n.target.carrier)).comp (e : C(R.carrier, R1.carrier)) =
        ((m.marking.trans f : R.carrier ≃ₜ n.target.carrier) :
          C(R.carrier, n.target.carrier)) := by
      ext x
      change f (m.marking (e.symm (e x))) = f (m.marking x)
      rw [e.symm_apply_apply]
    have hn : (_root_.toContinuousMap
        ((referenceMarked e he n).marking : R1.carrier ≃ₜ n.target.carrier)).comp
        (e : C(R.carrier, R1.carrier)) =
        (n.marking : C(R.carrier, n.target.carrier)) := by
      ext x
      change n.marking (e.symm (e x)) = n.marking x
      rw [e.symm_apply_apply]
    change ContinuousMap.Homotopic
      ((((referenceMarked e he m).marking.trans f : R1.carrier ≃ₜ n.target.carrier) :
        C(R1.carrier, n.target.carrier)).comp (e : C(R.carrier, R1.carrier)))
      ((_root_.toContinuousMap
        ((referenceMarked e he n).marking : R1.carrier ≃ₜ n.target.carrier)).comp
        (e : C(R.carrier, R1.carrier))) at hback
    rw [hm, hn] at hback
    exact ⟨f, hf, hback, hd⟩
  · rintro ⟨f, hf, hh, hd⟩
    exact ⟨f, hf, reference_marking_homotopy e he hh, hd⟩

/-- The actual reference homeomorphism preserves the original fixed-marking distance. -/
theorem referenceHomeomorph_distance_eq_fixed {R : Surface.{u}} {R1 : Surface.{w}}
    (e : R.carrier ≃ₜ R1.carrier) (he : LiZhongQC.IsQCRS e)
    (m n : Marked.{u, v} R) :
    distance (referenceHomeomorph e he (mk m)) (referenceHomeomorph e he (mk n)) =
      sInf (fixedLogDilatations m n) := by
  rw [referenceHomeomorph_distance, distance_eq_fixed_inf]

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
