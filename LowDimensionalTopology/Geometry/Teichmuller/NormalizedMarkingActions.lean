/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCMarkedSpace
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedLiftFixedEndpoints

/-!
# Normalized lifted actions of general marked surfaces

The original covering group is explicitly in coordinates where zero, one and
infinity are fixed points of nonidentity projective elements. This coordinate
convention is not asserted for an arbitrary group. Targets retain their actual
native atlases and may be noncompact.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Manifold ContDiff UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller

open LiZhongQC

/-- Three genuinely fixed endpoints and the actual lift normalizations force
the conjugating real matrix to act identically on the sphere and on the half-plane. -/
theorem normalizedLift_conjugating_matrix_action_identity
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)
    {F₁ F₂ : ℍ ≃ₜ ℍ} {G₁ G₂ : ExtPlane → ExtPlane}
    (hG₁ : IsHomeoExtension (liftToC F₁) upperHalf upperHalf G₁)
    (hG₂ : IsHomeoExtension (liftToC F₂) upperHalf upperHalf G₂)
    (hnorm₁ : G₁ ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
      G₁ ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ G₁ extInf = extInf)
    (hnorm₂ : G₂ ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
      G₂ ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ G₂ extInf = extInf)
    {N : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hconj : ∀ γ ∈ Γ, ∀ τ : ℍ,
      F₁ (γ • F₁.symm τ) = N • F₂ (γ • F₂.symm (N⁻¹ • τ))) :
    (∀ ξ, mobiusSL (slRealToComplex N) ξ = ξ) ∧ ∀ τ : ℍ, N • τ = τ := by
  obtain ⟨γ₀, hγ₀, hne₀, hfix₀⟩ := hfixed ((0 : ℂ) : ExtPlane) (by simp)
  obtain ⟨γ₁, hγ₁, hne₁, hfix₁⟩ := hfixed ((1 : ℂ) : ExtPlane) (by simp)
  obtain ⟨γinf, hγinf, hneInf, hfixInf⟩ := hfixed extInf (by simp)
  have h0 := normalizedLift_conjugacy_fixed_endpoint hp hG₁ hG₂ hconj hγ₀ hne₀ hfix₀
  have h1 := normalizedLift_conjugacy_fixed_endpoint hp hG₁ hG₂ hconj hγ₁ hne₁ hfix₁
  have hinf := normalizedLift_conjugacy_fixed_endpoint hp hG₁ hG₂ hconj hγinf hneInf hfixInf
  rw [hnorm₁.1, hnorm₂.1] at h0
  rw [hnorm₁.2.1, hnorm₂.2.1] at h1
  rw [hnorm₁.2.2, hnorm₂.2.2] at hinf
  exact s27l_fix3 hinf.symm h0.symm h1.symm

namespace GeneralQC

universe u

/-- General original marked equivalence is precisely equality of all actual
normalized lifted deck actions. The fixed-triple condition is the stated
coordinate convention on the original group, not a compactness assumption. -/
theorem marked_equivalent_iff_normalized_lift_actions
    (R : Surface.{u}) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : ℍ → R.carrier} (hp₀ : IsUniformization Γ₀ p₀)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ₀, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)
    (m₁ m₂ : Marked.{u, u} R)
    {Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₁ : ℍ → m₁.target.carrier} {p₂ : ℍ → m₂.target.carrier}
    (hp₁ : IsUniformization Γ₁ p₁) (hp₂ : IsUniformization Γ₂ p₂)
    {F₁ F₂ : ℍ ≃ₜ ℍ} {G₁ G₂ : ExtPlane → ExtPlane}
    (h₁ : IsNormalizedLift p₀ p₁ m₁.marking F₁ G₁)
    (h₂ : IsNormalizedLift p₀ p₂ m₂.marking F₂ G₂) :
    m₁.Equivalent m₂ ↔
      ∀ γ ∈ Γ₀, ∀ τ : ℍ, F₁ (γ • F₁.symm τ) = F₂ (γ • F₂.symm τ) := by
  constructor
  · rintro ⟨c, hc, hhom⟩
    obtain ⟨τ₂, hτ₂⟩ := hp₂.2.2.1 (c (p₁ UpperHalfPlane.I))
    obtain ⟨C, hC, -⟩ := exists_lift hp₁ hp₂ c UpperHalfPlane.I τ₂ hτ₂
    obtain ⟨M, hM⟩ := utm_eq_smul_of_isKQC_one C
      (h23l_lift_isKQC hp₁ hp₂ ((isKQCRS_one_iff c).2 hc) hC)
    have hL : IsLift p₀ p₂ (m₁.marking.trans c) (F₁.trans C) := fun τ => by
      show p₂ (C (F₁ τ)) = c (m₁.marking (p₀ τ))
      rw [hC, h₁.1]
    obtain ⟨δ, -, hrel⟩ := (thm23_1_homotopy_iff hp₀ hp₂
      (m₁.marking.trans c) m₂.marking hL h₂.1).mp hhom
    let N : Matrix.SpecialLinearGroup (Fin 2) ℝ := M⁻¹ * δ
    have hconj : ∀ γ ∈ Γ₀, ∀ τ : ℍ,
        F₁ (γ • F₁.symm τ) = N • F₂ (γ • F₂.symm (N⁻¹ • τ)) := by
      intro γ hγ τ
      have h := hrel γ hγ (C τ)
      have e1 : (F₁.trans C).symm (C τ) = F₁.symm τ := by
        change F₁.symm (C.symm (C τ)) = F₁.symm τ
        rw [C.symm_apply_apply]
      have e2 : δ⁻¹ • C τ = N⁻¹ • τ := by
        rw [hM]
        simp only [N, mul_inv_rev, inv_inv, mul_smul]
      rw [e1, e2] at h
      have hMrel : M • F₁ (γ • F₁.symm τ) =
          δ • F₂ (γ • F₂.symm (N⁻¹ • τ)) := by
        change C (F₁ (γ • F₁.symm τ)) = _ at h
        rwa [hM] at h
      calc
        F₁ (γ • F₁.symm τ) = M⁻¹ • (M • F₁ (γ • F₁.symm τ)) :=
          (inv_smul_smul M _).symm
        _ = M⁻¹ • (δ • F₂ (γ • F₂.symm (N⁻¹ • τ))) := congrArg (fun z : ℍ => M⁻¹ • z) hMrel
        _ = N • F₂ (γ • F₂.symm (N⁻¹ • τ)) := (mul_smul M⁻¹ δ _).symm
    have hid := (normalizedLift_conjugating_matrix_action_identity hp₀ hfixed
      h₁.2.1 h₂.2.1 h₁.2.2 h₂.2.2 hconj).2
    intro γ hγ τ
    have hNinv : N⁻¹ • τ = τ := by
      have h := hid (N⁻¹ • τ)
      rw [smul_inv_smul] at h
      exact h.symm
    have h := hconj γ hγ τ
    rw [hNinv, hid] at h
    exact h
  · intro hag
    obtain ⟨c, hc, hcp⟩ := s27l_descend_homeomorph hp₁ hp₂
      (s27l_fiber_transfer hp₀ hp₁ h₁.1 h₂.1 hag)
      (s27l_fiber_transfer hp₀ hp₂ h₂.1 h₁.1 fun γ hγ τ => (hag γ hγ τ).symm)
    refine ⟨c, hc, ?_⟩
    have hL : IsLift p₀ p₂ (m₁.marking.trans c) F₁ := fun τ => by
      show p₂ (F₁ τ) = c (m₁.marking (p₀ τ))
      rw [← h₁.1, hcp]
    refine (thm23_1_homotopy_iff hp₀ hp₂
      (m₁.marking.trans c) m₂.marking hL h₂.1).mpr ⟨1, Γ₂.one_mem, ?_⟩
    intro γ hγ τ
    rw [inv_one, one_smul, one_smul]
    exact hag γ hγ τ

/-- The actual canonical half-plane lift of an arbitrary original QC marking.
Its existence is obtained from the general uniformization transport, without
supplying a target covering or a lift as input. -/
def canonicalMarkingLift
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, u} R) : ℍ ≃ₜ ℍ :=
  Classical.choose (s27u_uniformization_transport hp m.marking m.qc)

/-- This is the literal normalized symmetric solution for the original lifted
coefficient, with its actual conjugated covering and normalized extension. -/
theorem canonicalMarkingLift_spec
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, u} R) :
    (∀ τ, (canonicalMarkingLift R hp m τ : ℂ) =
      s27u_fSym (s27u_liftCoeff p m.marking) τ) ∧
    IsUniformization (s27u_conjGroup Γ (canonicalMarkingLift R hp m))
      (s27u_proj p m.marking (canonicalMarkingLift R hp m)) ∧
    IsNormalizedLift p (s27u_proj p m.marking (canonicalMarkingLift R hp m))
      m.marking (canonicalMarkingLift R hp m)
      (OnePoint.map (s27u_fSym (s27u_liftCoeff p m.marking))) := by
  have h := Classical.choose_spec (s27u_uniformization_transport hp m.marking m.qc)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Original marked classes are equal exactly when their actual canonical
lifts induce equal projective deck actions. Both canonical lifts and target
uniformizations are constructed internally for the original markings. -/
theorem marked_equivalent_iff_canonical_lift_actions
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)
    (m₁ m₂ : Marked.{u, u} R) :
    let F₁ := canonicalMarkingLift R hp m₁
    let F₂ := canonicalMarkingLift R hp m₂
    m₁.Equivalent m₂ ↔
      ∀ γ ∈ Γ, ∀ τ : ℍ, F₁ (γ • F₁.symm τ) = F₂ (γ • F₂.symm τ) := by
  dsimp only
  have h₁ := canonicalMarkingLift_spec R hp m₁
  have h₂ := canonicalMarkingLift_spec R hp m₂
  exact marked_equivalent_iff_normalized_lift_actions R hp hfixed m₁ m₂
    h₁.2.1 h₂.2.1 h₁.2.2 h₂.2.2

/-- Equality in the actual original QC-marked quotient is exactly equality of
the projective actions induced by the internally constructed canonical lifts. -/
theorem mk_eq_mk_iff_canonical_lift_actions
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)
    (m₁ m₂ : Marked.{u, u} R) :
    let F₁ := canonicalMarkingLift R hp m₁
    let F₂ := canonicalMarkingLift R hp m₂
    mk m₁ = mk m₂ ↔
      ∀ γ ∈ Γ, ∀ τ : ℍ, F₁ (γ • F₁.symm τ) = F₂ (γ • F₂.symm τ) := by
  dsimp only
  constructor
  · intro h
    exact (marked_equivalent_iff_canonical_lift_actions R hp hfixed m₁ m₂).mp
      (Quotient.exact h)
  · intro h
    exact Quotient.sound
      ((marked_equivalent_iff_canonical_lift_actions R hp hfixed m₁ m₂).mpr h)

end GeneralQC
end LowDimensionalTopology.Geometry.Teichmuller
