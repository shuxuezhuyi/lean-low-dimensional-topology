/-
The covering and boundary comparison arguments reused below are due to
Wu Xiaobin, Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2. Apache-2.0 attribution is
retained in the external source and THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.External.LiZhongQC.Ch07.S27_TeichmullerExistence

/-!
# Canonical lift boundary values and the actual induced deck actions

A compact original surface is sufficient. The targets and their actual
uniformizations are retained, with no closed-target or genus hypothesis.
Conjugation is a genuine homomorphism into the homeomorphism group of the
upper half-plane. Its values identify exactly the underlying real Mobius
actions, so matrix representatives differing by sign are never compared.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open LiZhongQC

/-- Conjugate the original deck action by the actual upper-half-plane lift. -/
def conjugatedCoverAction
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (F : ℍ ≃ₜ ℍ) :
    Γ →* (ℍ ≃ₜ ℍ) where
  toFun γ := F.symm.trans ((Homeomorph.smul γ.val).trans F)
  map_one' := by
    apply Homeomorph.ext
    intro τ
    change F ((1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • F.symm τ) = τ
    rw [one_smul, F.apply_symm_apply]
  map_mul' γ δ := by
    apply Homeomorph.ext
    intro τ
    change F ((γ.val * δ.val) • F.symm τ) =
      F (γ.val • F.symm (F (δ.val • F.symm τ)))
    rw [mul_smul, F.symm_apply_apply]

@[simp] theorem conjugatedCoverAction_apply
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (F : ℍ ≃ₜ ℍ)
    (γ : Γ) (τ : ℍ) :
    conjugatedCoverAction Γ F γ τ = F (γ.val • F.symm τ) := rfl

/-- Conjugated values agree exactly when the original actions agree, rather
than when arbitrarily chosen determinant-one matrix representatives agree. -/
theorem conjugatedCoverAction_apply_eq_iff
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (F : ℍ ≃ₜ ℍ)
    (γ δ : Γ) :
    conjugatedCoverAction Γ F γ = conjugatedCoverAction Γ F δ ↔
      ∀ τ : ℍ, γ.val • τ = δ.val • τ := by
  constructor
  · intro h τ
    have he := congrArg (fun H : ℍ ≃ₜ ℍ => H (F τ)) h
    simp only [conjugatedCoverAction_apply, F.symm_apply_apply] at he
    exact F.injective he
  · intro h
    apply Homeomorph.ext
    intro τ
    exact congrArg F (h (F.symm τ))

/-- Equality of the induced homomorphisms is literal equality of all actual
conjugated deck maps, on every point of the upper half-plane. -/
theorem conjugatedCoverAction_eq_iff
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (F₁ F₂ : ℍ ≃ₜ ℍ) :
    conjugatedCoverAction Γ F₁ = conjugatedCoverAction Γ F₂ ↔
      ∀ γ ∈ Γ, ∀ τ : ℍ,
        F₁ (γ • F₁.symm τ) = F₂ (γ • F₂.symm τ) := by
  constructor
  · intro h γ hγ τ
    exact congrArg (fun θ : Γ →* (ℍ ≃ₜ ℍ) => θ ⟨γ, hγ⟩ τ) h
  · intro h
    apply MonoidHom.ext
    intro γ
    apply Homeomorph.ext
    intro τ
    exact h γ.val γ.property τ

/-- Every conjugated value is an actual deck transformation of the given
TARGET uniformization. Thus these are genuine real Mobius automorphisms,
with no choice of matrix sign involved in their equality. -/
theorem conjugatedCoverAction_eq_deck
    {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → X} {q : ℍ → Y}
    (hp : IsUniformization Γ p) (hq : IsUniformization Δ q)
    {f : X → Y} {F : ℍ ≃ₜ ℍ} (hF : IsLift p q f F) (γ : Γ) :
    ∃ δ ∈ Δ, conjugatedCoverAction Γ F γ = Homeomorph.smul δ := by
  obtain ⟨δ, hδ, hrel⟩ := h23l_deck hp hq hF γ.property
  refine ⟨δ, hδ, ?_⟩
  apply Homeomorph.ext
  intro τ
  change F (γ.val • F.symm τ) = δ • τ
  rw [hrel, F.apply_symm_apply]

universe u
variable {X₀ X₁ X₂ : Type u}
    [TopologicalSpace X₀] [ChartedSpace ℂ X₀] [CompactSpace X₀]
    [TopologicalSpace X₁] [ChartedSpace ℂ X₁]
    [TopologicalSpace X₂] [ChartedSpace ℂ X₂]

/-- For the same actual three uniformizations and original marked maps, the
canonical induced deck homomorphisms agree iff the canonical lifts have the
same boundary values. Only compactness of the original surface is required. -/
theorem normalizedLift_deckActions_eq_iff_boundary
    {Γ₀ Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : ℍ → X₀} {p₁ : ℍ → X₁} {p₂ : ℍ → X₂}
    (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁)
    (hp₂ : IsUniformization Γ₂ p₂) (f₁ : X₀ ≃ₜ X₁) (f₂ : X₀ ≃ₜ X₂)
    {F₁ F₂ : ℍ ≃ₜ ℍ} {G₁ G₂ : ExtPlane → ExtPlane}
    (h₁ : IsNormalizedLift p₀ p₁ f₁ F₁ G₁)
    (h₂ : IsNormalizedLift p₀ p₂ f₂ F₂ G₂) :
    conjugatedCoverAction Γ₀ F₁ = conjugatedCoverAction Γ₀ F₂ ↔
      ∀ x : ℝ, G₁ ((x : ℂ) : ExtPlane) = G₂ ((x : ℂ) : ExtPlane) := by
  rw [conjugatedCoverAction_eq_iff]
  obtain ⟨hF₁, hG₁, -, -, hinf₁⟩ := h₁
  obtain ⟨hF₂, hG₂, -, -, hinf₂⟩ := h₂
  constructor
  · intro hag
    let Φ : ℍ → ℍ := fun τ => F₂.symm (F₁ τ)
    have hΦc : Continuous Φ := F₂.symm.continuous.comp F₁.continuous
    have hΦγ : ∀ γ ∈ Γ₀, ∀ τ : ℍ, Φ (γ • τ) = γ • Φ τ := by
      intro γ hγ τ
      have he := hag γ hγ (F₁ τ)
      rw [F₁.symm_apply_apply] at he
      change F₂.symm (F₁ (γ • τ)) = γ • F₂.symm (F₁ τ)
      rw [he, F₂.symm_apply_apply]
    obtain ⟨D, hD⟩ := s27l_bounded_displacement hp₀ hΦc hΦγ
    have hΦF : ∀ τ : ℍ,
        F₂ (Φ τ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • F₁ τ := by
      intro τ
      dsimp only [Φ]
      rw [F₂.apply_symm_apply, one_smul]
    obtain ⟨hreal, -⟩ := s27l_ext_eq_of_bounded hG₁ hG₂ hΦF hD
    intro x
    simpa only [k24_slReal_one, k24_mobiusSL_one] using (hreal x).symm
  · intro hbd
    have hbd' : ∀ y ∈ extRealLine, G₁ y = G₂ y := by
      rintro _ (⟨z, hz, rfl⟩ | hy)
      · have hz' : z = ((z.re : ℝ) : ℂ) :=
          Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact hz)
        rw [hz']
        exact hbd z.re
      · rw [mem_singleton_iff.mp hy, hinf₁, hinf₂]
    intro γ hγ τ
    obtain ⟨δ₁, -, hδ₁⟩ := h23l_deck hp₀ hp₁ hF₁ hγ
    obtain ⟨δ₂, -, hδ₂⟩ := h23l_deck hp₀ hp₂ hF₂ hγ
    rw [hδ₁, hδ₂, F₁.apply_symm_apply, F₂.apply_symm_apply]
    exact h36t_deck_agree hG₁ hG₂ hbd' hδ₁ hδ₂ τ

end LowDimensionalTopology.Geometry.Teichmuller
