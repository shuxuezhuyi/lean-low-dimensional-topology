module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceReferenceChange
public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceLiftNormalization

/-!
# The given reference change and the actual normalized composition lift

Changing the reference keeps the original marked target and precomposes its
marking by the given inverse reference homeomorphism. The lift is literally
composed with the inverse of the given reference lift. After its genuine real
Möbius normalization, the adjusted original covering has the same literal
composition lift. For a coefficient-normalized original marking, this is the
actual symmetric normalized solution of the translated coefficient.

The lifted-coefficient solution and normalized composition identities reuse
Wu Xiaobin's Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.SourceReferenceChange

open GammaMeasurableBeltrami NormalizedCoefficientTransport

universe u
variable {A B : Type u}
    [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A]
    [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B]
    (e : A ≃ₜ B) (he : LiZhongQC.IsQCRS e)
    {p : ℍ → A} {p1 : ℍ → B} (w : ℍ ≃ₜ ℍ)
    (hw : LiZhongQC.IsLift p p1 e w)

include hw in
/-- The inverse-precomposed original marking has the actual inverse-composed lift. -/
theorem marked_isLift (m : LiZhongQC.MarkedRS A) {pS : ℍ → m.X.carrier}
    (F : ℍ ≃ₜ ℍ) (hF : LiZhongQC.IsLift p pS m.marking F) :
    LiZhongQC.IsLift p1 pS (marked e he m).marking (w.symm.trans F) := by
  intro τ
  have hi : p (w.symm τ) = e.symm (p1 τ) := by
    have h := congrArg e.symm (hw (w.symm τ))
    simpa only [w.apply_symm_apply, e.symm_apply_apply] using h.symm
  change pS (F (w.symm τ)) = m.marking (e.symm (p1 τ))
  exact (hF (w.symm τ)).trans (congrArg m.marking hi)

/-- The normalization uses the original given lift and the actual real Möbius map. -/
def normalizedGivenLift (M : Deck) : ℍ ≃ₜ ℍ :=
  w.trans (Homeomorph.smul M)

/-- The actual normalized lift has the same inverse as the native normalized solution. -/
theorem normalizedGivenLift_symm_eq {Γ : Subgroup Deck} (ν : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ) (τ : ℍ) :
    (normalizedGivenLift w M).symm τ = (normalizedUpperEquiv ν).symm τ := by
  apply (normalizedUpperEquiv ν).injective
  rw [hM]
  change (normalizedGivenLift w M) ((normalizedGivenLift w M).symm τ) = _
  rw [Homeomorph.apply_symm_apply, Equiv.apply_symm_apply]

include hw in
/-- The adjusted original cover has the literal inverse-normalized composition lift. -/
theorem marked_adjusted_isLift (M : Deck) (m : LiZhongQC.MarkedRS A)
    {pS : ℍ → m.X.carrier} (F : ℍ ≃ₜ ℍ)
    (hF : LiZhongQC.IsLift p pS m.marking F) :
    LiZhongQC.IsLift (LiZhongQC.adjustProjection p1 M) pS
      (marked e he m).marking ((normalizedGivenLift w M).symm.trans F) := by
  intro τ
  have h := marked_isLift e he w hw m F hF (M⁻¹ • τ)
  change pS (F (w.symm (M⁻¹ • τ))) = m.marking (e.symm (p1 (M⁻¹ • τ)))
  exact h

/-- The same adjusted lift retains the actual pointwise native composition formula. -/
theorem marked_adjusted_lift_native_formula {Γ : Subgroup Deck}
    (ν μ : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ)
    (F : ℍ ≃ₜ ℍ) (hFμ : ∀ τ : ℍ, F τ = normalizedUpperEquiv μ τ) (τ : ℍ) :
    (((normalizedGivenLift w M).symm.trans F) τ : ℂ) =
      normalizedMap μ (normalizedInverse ν τ) := by
  change (F ((normalizedGivenLift w M).symm τ) : ℂ) = _
  rw [normalizedGivenLift_symm_eq w ν M hM, hFμ,
    normalizedUpperEquiv_coe, normalizedUpperEquiv_symm_coe]

/-- For the actual translated source coefficient this composition is its
symmetric normalized solution, rather than a new unrelated representative. -/
theorem marked_adjusted_lift_translated_solution {Γ : Subgroup Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ)
    (F : ℍ ≃ₜ ℍ) (hFμ : ∀ τ : ℍ, F τ = normalizedUpperEquiv μ τ) (τ : ℍ) :
    (((normalizedGivenLift w M).symm.trans F) τ : ℂ) =
      LiZhongQC.fMuSym (translatedSource hΓ ν μ).val.val τ := by
  rw [marked_adjusted_lift_native_formula w ν μ M hM F hFμ τ]
  have ht := congrFun
    (LiZhongQC.b33_t_tb_fMuSym (toSourceGamma ν).val (toSourceGamma μ).val) (τ : ℂ)
  exact ht.symm

end LowDimensionalTopology.Geometry.Teichmuller.SourceReferenceChange
