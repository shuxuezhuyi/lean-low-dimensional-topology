/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCDistanceAxioms
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedMarkingActions
public import LowDimensionalTopology.External.LiZhongQC.Ch10.S33_BersEmbedding

/-!
# Actual coefficient control of the original general QC distance

The exact maximal dilatation of the transition of two original markings is
computed from their actual lifted coefficients. The plane and covering
helpers used here apply to open targets; no compact-target packaging is used.
The resulting full-log upper bound is for the same original class distance.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Topology
open scoped Manifold ContDiff UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open LiZhongQC
universe u

/-- The actual transition of markings has the fractional coefficient
distortion computed from the two original raw lifted coefficients. -/
theorem transition_dilatation_spec
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m n : Marked.{u, u} R) :
    let δ := UniversalTeichmuller.dilatationDiffNorm
      (s27u_liftCoeff p m.marking) (s27u_liftCoeff p n.marking)
    δ < 1 ∧ maxDilatationRS (m.marking.symm.trans n.marking) =
      ENNReal.ofReal ((1 + δ) / (1 - δ)) := by
  let f := m.marking.symm.trans n.marking
  have hf : IsQCRS f := s28q_isQCRS_trans (s28q_isQCRS_symm m.qc) n.qc
  let F₁ := canonicalMarkingLift R hp m
  let F₂ := canonicalMarkingLift R hp n
  have h₁ := canonicalMarkingLift_spec R hp m
  have h₂ := canonicalMarkingLift_spec R hp n
  have hlift : IsLift (s27u_proj p m.marking F₁) (s27u_proj p n.marking F₂)
      f (F₁.symm.trans F₂) := by
    intro τ
    change n.marking (p (F₂.symm (F₂ (F₁.symm τ)))) =
      n.marking (m.marking.symm (m.marking (p (F₁.symm τ))))
    rw [F₂.symm_apply_apply, m.marking.symm_apply_apply]
  have hsurface := s33d_K_lift h₁.2.1 h₂.2.1 hf hlift
  obtain ⟨K₁, hK₁⟩ := m.qc
  obtain ⟨K₂, hK₂⟩ := n.qc
  have hk₁0 : 0 ≤ (K₁ - 1) / (K₁ + 1) :=
    div_nonneg (by linarith [hK₁.1]) (by linarith [hK₁.1])
  have hk₁1 : (K₁ - 1) / (K₁ + 1) < 1 :=
    (div_lt_one (by linarith [hK₁.1])).2 (by linarith)
  have hk₂0 : 0 ≤ (K₂ - 1) / (K₂ + 1) :=
    div_nonneg (by linarith [hK₂.1]) (by linarith [hK₂.1])
  have hk₂1 : (K₂ - 1) / (K₂ + 1) < 1 :=
    (div_lt_one (by linarith [hK₂.1])).2 (by linarith)
  have hμ₁ := s27u_liftCoeff_isBeltramiCoeff hp hK₁
  have hμ₂ := s27u_liftCoeff_isBeltramiCoeff hp hK₂
  obtain ⟨himg₁, _, _, hQ₁, hd₁⟩ := s27u_fSym_upperHalf hk₁0 hk₁1 hμ₁
  obtain ⟨_, _, _, hQ₂, hd₂⟩ := s27u_fSym_upperHalf hk₂0 hk₂1 hμ₂
  obtain ⟨hδ, hplane⟩ := s33d_plane_K hQ₂ hQ₁ hd₁ hd₂
  rw [himg₁] at hplane
  have hcong : maxDilatation (liftToC (F₁.symm.trans F₂)) upperHalf =
      maxDilatation (s27u_fSym (s27u_liftCoeff p n.marking) ∘
        Function.invFunOn (s27u_fSym (s27u_liftCoeff p m.marking)) upperHalf) upperHalf := by
    apply s33d_maxDil_congr isOpen_upperHalf
    intro w hw
    set τ : ℍ := F₁.symm (UpperHalfPlane.ofComplex w) with hτ
    have hfirst : s27u_fSym (s27u_liftCoeff p m.marking) (τ : ℂ) = w := by
      rw [← h₁.1 τ, hτ, F₁.apply_symm_apply,
        UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < w.im from hw)]
    have hinv : Function.invFunOn (s27u_fSym (s27u_liftCoeff p m.marking))
        upperHalf w = (τ : ℂ) := by
      rw [← hfirst]
      exact hQ₁.2.2.1.2.1.leftInvOn_invFunOn τ.coe_im_pos
    simp only [Function.comp_apply]
    rw [hinv, ← h₂.1 τ, h23l_liftToC_eq _ hw]
    rfl
  exact ⟨hδ, hsurface.trans (hcong.trans hplane)⟩

/-- The original full-log infimum is bounded by the actual transition of
the prescribed original markings and their literal coefficient difference. -/
theorem distance_mk_le_fractional_log
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m n : Marked.{u, u} R) :
    let δ := UniversalTeichmuller.dilatationDiffNorm
      (s27u_liftCoeff p m.marking) (s27u_liftCoeff p n.marking)
    distance (mk m) (mk n) ≤ Real.log ((1 + δ) / (1 - δ)) := by
  obtain ⟨hδ, hK⟩ := transition_dilatation_spec R hp m n
  let f := m.marking.symm.trans n.marking
  have hf : IsQCRS f := s28q_isQCRS_trans (s28q_isQCRS_symm m.qc) n.qc
  have hh : ((m.marking.trans f : R.carrier ≃ₜ n.target.carrier) :
      C(R.carrier, n.target.carrier)) = (n.marking : C(R.carrier, n.target.carrier)) := by
    ext x
    exact congrArg n.marking (m.marking.symm_apply_apply x)
  have hmem : Real.log (maxDilatationRS f).toReal ∈ fixedLogDilatations m n :=
    ⟨f, hf, by rw [hh], rfl⟩
  have hbound := csInf_le (fixedLogDilatations_bddBelow m n) hmem
  have hδ0 : 0 ≤ UniversalTeichmuller.dilatationDiffNorm
      (s27u_liftCoeff p m.marking) (s27u_liftCoeff p n.marking) := ENNReal.toReal_nonneg
  have hratio0 : 0 ≤ (1 + UniversalTeichmuller.dilatationDiffNorm
      (s27u_liftCoeff p m.marking) (s27u_liftCoeff p n.marking)) /
        (1 - UniversalTeichmuller.dilatationDiffNorm
          (s27u_liftCoeff p m.marking) (s27u_liftCoeff p n.marking)) :=
    div_nonneg (by linarith) (by linarith)
  rw [distance_eq_fixed_inf]
  exact hbound.trans_eq (congrArg Real.log
    ((congrArg ENNReal.toReal hK).trans (ENNReal.toReal_ofReal hratio0)))

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
