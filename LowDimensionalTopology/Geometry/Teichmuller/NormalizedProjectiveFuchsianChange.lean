/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.InducedProjectiveFuchsianHom
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceChangeDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.NativeDeformedCoefficientMap

/-!
# The normalized projective change for every compatible coefficient

Both actual action ranges agree by the two directions of the existing deformed
group specification. The faithful projective action identifies their domains.
No reference surface, covering, genus, compactness or signed matrix section is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
open GammaMeasurableBeltrami Hyperbolic Mobius

variable {Γ : Subgroup Deck}

/-- The existing homeomorphism packages exactly the original normalized equivalence. -/
theorem normalizedUpperHomeomorph_toEquiv (ν : Ball Γ) :
    (normalizedUpperHomeomorph ν).toEquiv = normalizedUpperEquiv ν := rfl

/-- Every original representative has its actual deformed conjugate action. -/
theorem normalizedUpper_deformed_forward (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    {γ : Deck} (hγ : γ ∈ Γ) :
    ∃ δ ∈ deformedGroup hΓ ν, ∀ z : ℍ,
      normalizedUpperEquiv ν (γ • z) = δ • normalizedUpperEquiv ν z := by
  obtain ⟨δ, hδ, he⟩ := (deformedGroup_spec hΓ ν).2.1 γ hγ
  refine ⟨δ, hδ, fun z => ?_⟩
  apply UpperHalfPlane.ext
  simpa only [normalizedUpperEquiv_coe, LiZhongQC.h23l_b_coe_smul,
    LiZhongQC.mobiusFn] using he (z : ℂ) z.im_pos

/-- Every deformed representative arises from an original action under the same map. -/
theorem normalizedUpper_deformed_backward (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    {δ : Deck} (hδ : δ ∈ deformedGroup hΓ ν) :
    ∃ γ ∈ Γ, ∀ z : ℍ,
      normalizedUpperEquiv ν (γ • z) = δ • normalizedUpperEquiv ν z := by
  obtain ⟨γ, hγ, he⟩ := (deformedGroup_spec hΓ ν).2.2 δ hδ
  refine ⟨γ, hγ, fun z => ?_⟩
  apply UpperHalfPlane.ext
  simpa only [normalizedUpperEquiv_coe, LiZhongQC.h23l_b_coe_smul,
    LiZhongQC.mobiusFn] using he (z : ℂ) z.im_pos

/-- Equality of the entire actual action ranges, with both inclusions proved. -/
theorem normalizedProjectiveFuchsianChange_range (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    (projectiveConjugatedCoverAction Γ (normalizedUpperHomeomorph ν)).range =
      (projectiveConjugatedCoverAction (deformedGroup hΓ ν) (Homeomorph.refl ℍ)).range := by
  apply le_antisymm
  · rintro H ⟨g, rfl⟩
    obtain ⟨γ, rfl⟩ := ProjectivePoincare.imageHom_surjective Γ g
    obtain ⟨δ, hδ, he⟩ := normalizedUpper_deformed_forward hΓ ν γ.property
    refine ⟨ProjectivePoincare.imageHom (deformedGroup hΓ ν) ⟨δ, hδ⟩, ?_⟩
    rw [projectiveConjugatedCoverAction_image, projectiveConjugatedCoverAction_image]
    apply Homeomorph.ext
    intro z
    change δ • z = normalizedUpperEquiv ν (γ.val • (normalizedUpperEquiv ν).symm z)
    simpa only [Equiv.apply_symm_apply] using (he ((normalizedUpperEquiv ν).symm z)).symm
  · rintro H ⟨g, rfl⟩
    obtain ⟨δ, rfl⟩ := ProjectivePoincare.imageHom_surjective (deformedGroup hΓ ν) g
    obtain ⟨γ, hγ, he⟩ := normalizedUpper_deformed_backward hΓ ν δ.property
    refine ⟨ProjectivePoincare.imageHom Γ ⟨γ, hγ⟩, ?_⟩
    rw [projectiveConjugatedCoverAction_image, projectiveConjugatedCoverAction_image]
    apply Homeomorph.ext
    intro z
    change normalizedUpperEquiv ν (γ • (normalizedUpperEquiv ν).symm z) = δ.val • z
    simpa only [Equiv.apply_symm_apply] using he ((normalizedUpperEquiv ν).symm z)

/-- The normalized coefficient changes the full actual projective Fuchsian group. -/
def normalizedProjectiveFuchsianEquiv (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    Γ.map realSLMobius ≃* (deformedGroup hΓ ν).map realSLMobius :=
  (MonoidHom.ofInjective
    (projectiveConjugatedCoverAction_injective Γ (normalizedUpperHomeomorph ν))).trans
      ((MulEquiv.subgroupCongr (normalizedProjectiveFuchsianChange_range hΓ ν)).trans
        (MonoidHom.ofInjective
          (projectiveConjugatedCoverAction_injective
            (deformedGroup hΓ ν) (Homeomorph.refl ℍ))).symm)

/-- The equivalence is characterized by the same literal normalized action. -/
theorem normalizedProjectiveFuchsianEquiv_action (hΓ : LiZhongQC.IsFuchsian Γ)
    (ν : Ball Γ) (g : Γ.map realSLMobius) :
    projectiveConjugatedCoverAction (deformedGroup hΓ ν) (Homeomorph.refl ℍ)
        (normalizedProjectiveFuchsianEquiv hΓ ν g) =
      projectiveConjugatedCoverAction Γ (normalizedUpperHomeomorph ν) g := by
  simp only [normalizedProjectiveFuchsianEquiv, MulEquiv.trans_apply,
    MonoidHom.apply_ofInjective_symm, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]

/-- Every source representative has the book's conjugation value at every point. -/
theorem normalizedProjectiveFuchsianEquiv_image_apply (hΓ : LiZhongQC.IsFuchsian Γ)
    (ν : Ball Γ) (γ : Γ) (z : ℍ) :
    (normalizedProjectiveFuchsianEquiv hΓ ν (ProjectivePoincare.imageHom Γ γ)).val.val (z : ℂ) =
      (((normalizedUpperEquiv ν (γ.val • (normalizedUpperEquiv ν).symm z) : ℍ) : ℂ) :
        ExtendedComplex) := by
  rw [projectiveConjugatedCoverAction_id_sphere, normalizedProjectiveFuchsianEquiv_action,
    projectiveConjugatedCoverAction_image]
  rfl

/-- Pointwise conjugacy for every actual source projective element, independently of a lift. -/
theorem normalizedProjectiveFuchsianEquiv_conjugacy (hΓ : LiZhongQC.IsFuchsian Γ)
    (ν : Ball Γ) (g : Γ.map realSLMobius) (z : ℍ) :
    (normalizedProjectiveFuchsianEquiv hΓ ν g).val.val
        ((normalizedUpperEquiv ν z : ℍ) : ℂ) =
      (((normalizedUpperEquiv ν
        (projectiveConjugatedCoverAction Γ (Homeomorph.refl ℍ) g z) : ℍ) : ℂ) :
          ExtendedComplex) := by
  obtain ⟨γ, rfl⟩ := ProjectivePoincare.imageHom_surjective Γ g
  rw [normalizedProjectiveFuchsianEquiv_image_apply, projectiveConjugatedCoverAction_image]
  change (((normalizedUpperEquiv ν
    (γ.val • (normalizedUpperEquiv ν).symm (normalizedUpperEquiv ν z)) : ℍ) : ℂ) :
      ExtendedComplex) = _
  rw [Equiv.symm_apply_apply]
  rfl

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
