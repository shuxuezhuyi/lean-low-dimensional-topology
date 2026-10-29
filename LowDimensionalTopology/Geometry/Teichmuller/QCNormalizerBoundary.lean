module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceQCModularAction

/-!
# Boundary classes of actual quasiconformal lifts

The boundary relation uses a deck transformation on the right, on the entire
extended real line. For lifts through an actual compact uniformization, this
relation is exactly free homotopy of the descended surface maps. All upper
half-plane maps remain actual homeomorphisms; no equality of matrix subgroups
is inferred from equality of their actions.

The lift, homotopy and boundary APIs are reused from Wu Xiaobin's
Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0).
See `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.QCNormalizerBoundary

open LiZhongQC

/-- The genuine homeomorphic boundary extension of an upper QC map. Its values
outside the closed upper half-plane are immaterial. -/
def boundaryExtension (F : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hF : IsQuasiconformal (liftToC F) upperHalf) : ExtPlane → ExtPlane :=
  Classical.choose (thm13_3_boundary_correspondence isJordanDomain_upperHalf
    isJordanDomain_upperHalf hF (h36q_liftToC_image F))

/-- The selected extension has the original continuous, injective and onto
closed-half-plane contract. -/
theorem boundaryExtension_spec (F : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hF : IsQuasiconformal (liftToC F) upperHalf) :
    IsHomeoExtension (liftToC F) upperHalf upperHalf (boundaryExtension F hF) :=
  Classical.choose_spec (thm13_3_boundary_correspondence isJordanDomain_upperHalf
    isJordanDomain_upperHalf hF (h36q_liftToC_image F))

/-- The actual right-deck relation on the full boundary, including infinity. -/
def RightDeckBoundaryRel (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (B₁ B₂ : ExtPlane → ExtPlane) : Prop :=
  ∃ γ ∈ Γ, ∀ x ∈ extRealLine,
    B₂ x = B₁ (mobiusSL (slRealToComplex γ) x)

universe u
variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [ConnectedSpace X] [CompactSpace X]
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → X}

/-- Free homotopy of actual descended maps is precisely the right-deck
boundary relation. The compactness is used to control the displacement of
the relative lift; no normalization at three boundary points is imposed. -/
theorem homotopic_iff_rightDeckBoundaryRel
    (hp : IsUniformization Γ p) (f g : X ≃ₜ X)
    {F G : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hF : IsLift p p f F) (hG : IsLift p p g G)
    {B₁ B₂ : ExtPlane → ExtPlane}
    (hB₁ : IsHomeoExtension (liftToC F) upperHalf upperHalf B₁)
    (hB₂ : IsHomeoExtension (liftToC G) upperHalf upperHalf B₂) :
    ContinuousMap.Homotopic (f : C(X, X)) (g : C(X, X)) ↔
      RightDeckBoundaryRel Γ B₁ B₂ := by
  constructor
  · intro hfg
    obtain ⟨δ, hδ, hrel⟩ :=
      (thm23_1_homotopy_iff hp hp f g hF hG).mp hfg
    let Φ : UpperHalfPlane → UpperHalfPlane :=
      fun τ => G.symm (δ⁻¹ • F τ)
    have hΦc : Continuous Φ :=
      G.symm.continuous.comp ((continuous_const_smul δ⁻¹).comp F.continuous)
    have hΦγ : ∀ γ ∈ Γ, ∀ τ, Φ (γ • τ) = γ • Φ τ := by
      intro γ hγ τ
      have h := hrel γ hγ (F τ)
      rw [F.symm_apply_apply] at h
      have he : δ⁻¹ • F (γ • τ) =
          G (γ • G.symm (δ⁻¹ • F τ)) := by
        calc
          δ⁻¹ • F (γ • τ) =
              δ⁻¹ • (δ • G (γ • G.symm (δ⁻¹ • F τ))) :=
            congrArg (fun z : UpperHalfPlane => δ⁻¹ • z) h
          _ = G (γ • G.symm (δ⁻¹ • F τ)) := inv_smul_smul δ _
      change G.symm (δ⁻¹ • F (γ • τ)) = γ • G.symm (δ⁻¹ • F τ)
      rw [he, G.symm_apply_apply]
    obtain ⟨D, hD⟩ := s27l_bounded_displacement hp hΦc hΦγ
    have hΦF : ∀ τ, G (Φ τ) = δ⁻¹ • F τ :=
      fun τ => G.apply_symm_apply _
    obtain ⟨hreal, hinf⟩ := s27l_ext_eq_of_bounded hB₁ hB₂ hΦF hD
    have hbd : ∀ x ∈ extRealLine,
        B₂ x = mobiusSL (slRealToComplex δ⁻¹) (B₁ x) := by
      rintro _ (⟨z, hz, rfl⟩ | hx)
      · have hz' : z = ((z.re : ℝ) : ℂ) :=
          Complex.ext (Complex.ofReal_re _).symm
            (by rw [Complex.ofReal_im]; exact hz)
        rw [hz']
        exact hreal z.re
      · rw [mem_singleton_iff.mp hx]
        exact hinf
    obtain ⟨γ, hγ, hγe⟩ :=
      h23l_deck hp hp (s27g_isLift_symm hF) (Γ.inv_mem hδ)
    have hFγ : ∀ τ, F (γ • τ) = δ⁻¹ • F τ := by
      intro τ
      have h := hγe (F τ)
      rw [F.symm_apply_apply] at h
      calc
        F (γ • τ) = F (F.symm (δ⁻¹ • F τ)) := congrArg F h.symm
        _ = δ⁻¹ • F τ := F.apply_symm_apply _
    refine ⟨γ, hγ, fun x hx => ?_⟩
    exact (hbd x hx).trans
      (h36t_ext_equivariant hB₁ hFγ (h36t_extRealLine_subset_closure hx)).symm
  · rintro ⟨γ, hγ, hbd⟩
    obtain ⟨δ, hδ, hδe⟩ := h23l_deck hp hp hF hγ
    let H : UpperHalfPlane ≃ₜ UpperHalfPlane :=
      F.trans (Homeomorph.smul δ)
    have hH : IsLift p p f H := by
      intro τ
      change p (δ • F τ) = f (p τ)
      calc
        p (δ • F τ) = p (F τ) :=
          ((hp.2.2.2 (F τ) (δ • F τ)).mpr ⟨δ, hδ, rfl⟩).symm
        _ = f (p τ) := hF τ
    have hBH : IsHomeoExtension (liftToC H) upperHalf upperHalf
        (mobiusSL (slRealToComplex δ) ∘ B₁) := s27l_ext_smul hB₁ δ
    have hbdHG : ∀ x ∈ extRealLine,
        (mobiusSL (slRealToComplex δ) ∘ B₁) x = B₂ x := by
      intro x hx
      exact (h36t_ext_equivariant hB₁ hδe
        (h36t_extRealLine_subset_closure hx)).symm.trans (hbd x hx).symm
    apply (thm23_1_homotopy_iff hp hp f g hH hG).mpr
    refine ⟨1, Γ.one_mem, fun a ha τ => ?_⟩
    rw [inv_one, one_smul, one_smul]
    obtain ⟨δH, _, hδH⟩ := h23l_deck hp hp hH ha
    obtain ⟨δG, _, hδG⟩ := h23l_deck hp hp hG ha
    rw [hδH, hδG, H.apply_symm_apply, G.apply_symm_apply]
    exact h36t_deck_agree hBH hB₂ hbdHG hδH hδG τ

/-- For arbitrary upper QC lifts, their actual selected boundary classes are
already equivalent exactly when their original descended maps are homotopic. -/
theorem homotopic_iff_selectedBoundary_rightDeck
    (hp : IsUniformization Γ p) (f g : X ≃ₜ X)
    {F G : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hF : IsLift p p f F) (hG : IsLift p p g G)
    (hFqc : IsQuasiconformal (liftToC F) upperHalf)
    (hGqc : IsQuasiconformal (liftToC G) upperHalf) :
    ContinuousMap.Homotopic (f : C(X, X)) (g : C(X, X)) ↔
      RightDeckBoundaryRel Γ (boundaryExtension F hFqc) (boundaryExtension G hGqc) :=
  homotopic_iff_rightDeckBoundaryRel hp f g hF hG
    (boundaryExtension_spec F hFqc) (boundaryExtension_spec G hGqc)

end LowDimensionalTopology.Geometry.Teichmuller.QCNormalizerBoundary
