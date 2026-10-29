module

public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity

/-!
# The unique quasiconformal descent of an actual upper-plane normalizer

Both normalizer conditions are literal equations of deck actions on the
upper half-plane, so no equality of determinant-one representatives is
assumed. The existing covering descent supplies the same actual surface
homeomorphism. The existing lift-to-surface theorem proves that its
quasiconformal distortion is the original given constant.

The covering and quasiconformal descent proofs reuse Wu Xiaobin's
Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.QCNormalizerDescent

universe u
variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    (hp : LiZhongQC.IsUniformization Γ p) (w : ℍ ≃ₜ ℍ)
    (hforward : ∀ γ ∈ Γ, ∃ δ ∈ Γ, ∀ τ : ℍ, w (γ • τ) = δ • w τ)
    (hbackward : ∀ δ ∈ Γ, ∃ γ ∈ Γ, ∀ τ : ℍ, w.symm (δ • τ) = γ • w.symm τ)

/-- The actual unique descended homeomorphism, on the original surface. -/
def descendedHomeomorph : X ≃ₜ X :=
  Classical.choose (LiZhongQC.s30b_descend hp hp w hforward hbackward)

/-- The supplied normalizer is literally a lift through the original cover. -/
theorem descendedHomeomorph_isLift :
    LiZhongQC.IsLift p p (descendedHomeomorph hp w hforward hbackward) w :=
  Classical.choose_spec (LiZhongQC.s30b_descend hp hp w hforward hbackward)

/-- Surjectivity of the original cover makes the descended map unique. -/
theorem descendedHomeomorph_eq_of_isLift (e : X ≃ₜ X)
    (he : LiZhongQC.IsLift p p e w) :
    descendedHomeomorph hp w hforward hbackward = e := by
  apply Homeomorph.ext
  intro x
  obtain ⟨τ, rfl⟩ := hp.2.2.1 x
  exact (descendedHomeomorph_isLift hp w hforward hbackward τ).symm.trans (he τ)

/-- The original distortion constant is preserved by actual covering descent. -/
theorem descendedHomeomorph_isKQCRS [IsManifold 𝓘(ℂ) ω X] {K : ℝ}
    (hK : LiZhongQC.IsKQC (LiZhongQC.liftToC w) LiZhongQC.upperHalf K) :
    LiZhongQC.IsKQCRS (descendedHomeomorph hp w hforward hbackward) K :=
  LiZhongQC.s27v_isKQCRS_of_lift hp hp
    (descendedHomeomorph_isLift hp w hforward hbackward) hK

include hp hforward hbackward in
/-- Every actual quasiconformal normalizer descends uniquely to an actual
quasiconformal self-homeomorphism of the original surface. -/
theorem exists_unique_quasiconformal_descent [IsManifold 𝓘(ℂ) ω X]
    (hw : ∃ K : ℝ, LiZhongQC.IsKQC (LiZhongQC.liftToC w) LiZhongQC.upperHalf K) :
    ∃! e : X ≃ₜ X, LiZhongQC.IsQCRS e ∧ LiZhongQC.IsLift p p e w := by
  obtain ⟨K, hK⟩ := hw
  refine ⟨descendedHomeomorph hp w hforward hbackward,
    ⟨⟨K, descendedHomeomorph_isKQCRS hp w hforward hbackward hK⟩,
      descendedHomeomorph_isLift hp w hforward hbackward⟩, ?_⟩
  intro e he
  exact (descendedHomeomorph_eq_of_isLift hp w hforward hbackward e he.2).symm

end LowDimensionalTopology.Geometry.Teichmuller.QCNormalizerDescent
