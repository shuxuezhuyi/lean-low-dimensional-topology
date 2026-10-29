module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceLiftNormalization
public import LowDimensionalTopology.Geometry.Teichmuller.BersRealMobiusIsometry

/-!
# The actual weighted Bers coordinate change for an arbitrary given lift

The normalized deformed group and the adjusted given target group have the
same actions, although their determinant-one representatives can differ by
sign. Fourth-power quadratic pullback is insensitive to this sign. Their
native weighted submodules are therefore equal. Composing that identity with
the actual real Möbius isometry gives the coordinate change to the original
supplied target group, retaining the original weighted norm and every value.

The action rigidity and automorphic-function convention reuse Wu Xiaobin's
Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

open GammaMeasurableBeltrami

/-- The full quadratic pullback is independent of the central matrix sign. -/
theorem realMobiusPullback_eq_of_same_action {A B : Deck}
    (hact : ∀ τ : ℍ, A • τ = B • τ) (φ : ℂ → ℂ) :
    realMobiusPullback A φ = realMobiusPullback B φ := by
  rcases LiZhongQC.b33_d_eq_or_eq_neg hact with he | he
  · rw [he]
  · rw [he]
    funext z
    by_cases hz : z ∈ LiZhongQC.lowerHalf
    · rw [realMobiusPullback_apply _ _ hz, realMobiusPullback_apply _ _ hz]
      have hm : LiZhongQC.utm_b_mob (-B) z = LiZhongQC.utm_b_mob B z :=
        LiZhongQC.b33_d_mobiusFn_neg B z
      have hd : realMobiusDenom (-B) z ^ 4 = realMobiusDenom B z ^ 4 := by
        simp only [realMobiusDenom, Matrix.SpecialLinearGroup.coe_neg,
          Matrix.neg_apply, Complex.ofReal_neg]
        ring
      rw [hm, hd]
    · rw [realMobiusPullback_off _ _ hz, realMobiusPullback_off _ _ hz]

/-- Equality of actual action sets suffices for equality of the entire source
quadratic-differential spaces; no equality of matrix-lift subgroups is required. -/
theorem sourceAutomorphicQD_eq_of_sameActions (G H : Subgroup Deck)
    (hGH : ∀ γ ∈ G, ∃ δ ∈ H, ∀ τ : ℍ, γ • τ = δ • τ)
    (hHG : ∀ δ ∈ H, ∃ γ ∈ G, ∀ τ : ℍ, δ • τ = γ • τ) :
    LiZhongQC.automorphicQD G = LiZhongQC.automorphicQD H := by
  ext φ
  constructor
  · intro hφ
    refine ⟨hφ.1, hφ.2.1, ?_⟩
    intro δ hδ z hz
    obtain ⟨γ, hγ, hact⟩ := hHG δ hδ
    change φ (LiZhongQC.utm_b_mob δ z) / realMobiusDenom δ z ^ 4 = φ z
    rw [← realMobiusPullback_apply δ φ hz, realMobiusPullback_eq_of_same_action hact,
      realMobiusPullback_apply _ _ hz]
    exact hφ.2.2 γ hγ z hz
  · intro hφ
    refine ⟨hφ.1, hφ.2.1, ?_⟩
    intro γ hγ z hz
    obtain ⟨δ, hδ, hact⟩ := hGH γ hγ
    change φ (LiZhongQC.utm_b_mob γ z) / realMobiusDenom γ z ^ 4 = φ z
    rw [← realMobiusPullback_apply γ φ hz, realMobiusPullback_eq_of_same_action hact,
      realMobiusPullback_apply _ _ hz]
    exact hφ.2.2 δ hδ z hz

/-- The same faithful weighted realization is used for both actual action sets. -/
theorem automorphicSubmodule_eq_of_sameActions (G H : Subgroup Deck)
    (hGH : ∀ γ ∈ G, ∃ δ ∈ H, ∀ τ : ℍ, γ • τ = δ • τ)
    (hHG : ∀ δ ∈ H, ∃ γ ∈ G, ∀ τ : ℍ, δ • τ = γ • τ) :
    automorphicSubmodule G = automorphicSubmodule H := by
  unfold automorphicSubmodule
  rw [sourceAutomorphicQD_eq_of_sameActions G H hGH hHG]

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

universe u
variable {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {Γ Γ1 : Subgroup Deck} {p : ℍ → X} {p1 : ℍ → Y}

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
/-- The actual native deformed weighted submodule equals that of the adjusted
original target cover. The premise is the derived normalization of the given lift. -/
theorem givenLift_weightedSubmodule_eq
    (hp : LiZhongQC.IsUniformization Γ p) (hp1 : LiZhongQC.IsUniformization Γ1 p1)
    (hΓ : LiZhongQC.IsFuchsian Γ) (f : X ≃ₜ Y) (w : ℍ ≃ₜ ℍ)
    (hw : LiZhongQC.IsLift p p1 f w) (ν : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ) :
    BersWeighted.automorphicSubmodule (deformedGroup hΓ ν) =
      BersWeighted.automorphicSubmodule (LiZhongQC.conjGroup Γ1 M) := by
  obtain ⟨hGH, hHG⟩ := normalized_given_lift_deck_actions hp hp1 hΓ f w hw ν M hM
  exact BersWeighted.automorphicSubmodule_eq_of_sameActions _ _ hGH hHG

/-- The coordinate change to the supplied original target group is the true
complex-linear isometry, with the unchanged weighted Bers norms on both sides. -/
def givenLiftBersIsometry
    (hp : LiZhongQC.IsUniformization Γ p) (hp1 : LiZhongQC.IsUniformization Γ1 p1)
    (hΓ : LiZhongQC.IsFuchsian Γ) (f : X ≃ₜ Y) (w : ℍ ≃ₜ ℍ)
    (hw : LiZhongQC.IsLift p p1 f w) (ν : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ) :
    BersWeighted.Automorphic (deformedGroup hΓ ν) ≃ₗᵢ[ℂ]
      BersWeighted.Automorphic Γ1 :=
  (LinearIsometryEquiv.ofEq _ _
    (givenLift_weightedSubmodule_eq hp hp1 hΓ f w hw ν M hM)).trans
      (BersWeighted.automorphicRealMobiusIsometry Γ1 M)

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
/-- Every original differential value is transformed by the literal real
Möbius quadratic pullback, including the canonical zero extension. -/
theorem givenLiftBersIsometry_toSource
    (hp : LiZhongQC.IsUniformization Γ p) (hp1 : LiZhongQC.IsUniformization Γ1 p1)
    (hΓ : LiZhongQC.IsFuchsian Γ) (f : X ≃ₜ Y) (w : ℍ ≃ₜ ℍ)
    (hw : LiZhongQC.IsLift p p1 f w) (ν : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) :
    ((givenLiftBersIsometry hp hp1 hΓ f w hw ν M hM φ).toSource : ℂ → ℂ) =
      BersWeighted.realMobiusPullback M (φ.toSource : ℂ → ℂ) := by
  change ((BersWeighted.automorphicRealMobiusIsometry Γ1 M
    (LinearIsometryEquiv.ofEq _ _
      (givenLift_weightedSubmodule_eq hp hp1 hΓ f w hw ν M hM) φ)).toSource : ℂ → ℂ) = _
  rw [BersWeighted.automorphicRealMobiusIsometry_toSource]
  rfl

/-- The normalization and coordinate isometry are obtained from the original
reference homeomorphism and its given lift, with no target-group identification
or coordinate-map premise supplied by the caller. -/
theorem exists_givenLiftBersIsometry
    (hp : LiZhongQC.IsUniformization Γ p) (hp1 : LiZhongQC.IsUniformization Γ1 p1)
    (hΓ : LiZhongQC.IsFuchsian Γ) (f : X ≃ₜ Y) (hf : LiZhongQC.IsQCRS f)
    (w : ℍ ≃ₜ ℍ) (hw : LiZhongQC.IsLift p p1 f w) :
    ∃ (ν : Ball Γ) (M : Deck),
      (planeRepresentative ν.val.val =ᵐ[volume.restrict LiZhongQC.upperHalf]
        LiZhongQC.s27u_liftCoeff p f) ∧
      (∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ) ∧
      LiZhongQC.IsUniformization (LiZhongQC.conjGroup Γ1 M)
        (LiZhongQC.adjustProjection p1 M) ∧
      ∃ e : BersWeighted.Automorphic (deformedGroup hΓ ν) ≃ₗᵢ[ℂ]
          BersWeighted.Automorphic Γ1,
        ∀ φ, ((e φ).toSource : ℂ → ℂ) =
          BersWeighted.realMobiusPullback M (φ.toSource : ℂ → ℂ) := by
  obtain ⟨ν, M, hν, hM, hpM⟩ := exists_native_normalization_of_given_lift hp hp1 f hf w hw
  exact ⟨ν, M, hν, hM, hpM, givenLiftBersIsometry hp hp1 hΓ f w hw ν M hM,
    givenLiftBersIsometry_toSource hp hp1 hΓ f w hw ν M hM⟩

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
