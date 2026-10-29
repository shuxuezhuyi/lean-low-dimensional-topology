module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalReflectedUniformization

/-!
# The actual upper-half-plane cover of the original mirror

The original covering is precomposed by the supplied minus-conjugation
reflection. Its exact supplied action relations give the new orbit fibres.
Holomorphicity uses the actual lower-plane cover followed by negation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Topology
open scoped Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

/-- Negation identifies the upper half-plane with the actual lower-plane domain. -/
def originalMirrorUpperNegation : UpperHalfPlane ≃ₜ originalMirrorLowerDomain where
  toFun τ := ⟨-(τ : ℂ), by
    change -(τ : ℂ).im < 0
    exact neg_neg_of_pos τ.im_pos⟩
  invFun z := ⟨-(z : ℂ), by
    change 0 < -(z : ℂ).im
    exact neg_pos.mpr z.2⟩
  left_inv τ := UpperHalfPlane.ext (neg_neg (τ : ℂ))
  right_inv z := Subtype.ext (neg_neg (z : ℂ))
  continuous_toFun := UpperHalfPlane.continuous_coe.neg.subtype_mk
    (fun τ => by
      change -(τ : ℂ).im < 0
      exact neg_neg_of_pos τ.im_pos)
  continuous_invFun := UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    continuous_subtype_val.neg

/-- The actual upper-to-lower map retains its literal point coordinate. -/
@[simp] theorem originalMirrorUpperNegation_coe (τ : UpperHalfPlane) :
    (originalMirrorUpperNegation τ : ℂ) = -(τ : ℂ) := rfl

/-- This particular change from upper to lower coordinates is holomorphic. -/
theorem originalMirrorUpperNegation_mdifferentiable :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) originalMirrorUpperNegation := by
  have hneg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (fun z : ℂ => -z) :=
    contMDiff_iff_contDiff.mpr contDiff_neg
  have hcoe : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞
      (Subtype.val ∘ (originalMirrorUpperNegation : UpperHalfPlane → originalMirrorLowerDomain)) := by
    simpa only [Function.comp_def, originalMirrorUpperNegation_coe] using
      hneg.comp UpperHalfPlane.contMDiff_coe
  exact ((ContMDiff.subtypeVal_comp_iff originalMirrorLowerDomain
    (originalMirrorUpperNegation : UpperHalfPlane → originalMirrorLowerDomain)).mp
      hcoe).mdifferentiable (by simp)

/-- The original lower cover composed with negation is exactly the supplied sigma cover. -/
theorem originalMirrorUpperCover_eq (S : LiZhongQC.ClosedRS.{0})
    (p : UpperHalfPlane → S.carrier) (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ)) :
    (fun τ => originalMirrorCover p (originalMirrorUpperNegation τ)) =
      fun τ => p (σ τ) := by
  funext τ
  rw [originalMirrorCover_apply p (originalMirrorUpperNegation τ)]
  apply congrArg p
  apply UpperHalfPlane.ext
  rw [originalMirrorLowerConjugation_coe, originalMirrorUpperNegation_coe, hσ, map_neg]

/-- The literal original sigma cover is holomorphic in the actual native mirror atlas. -/
theorem originalMirrorUpperCover_mdifferentiable (S : LiZhongQC.ClosedRS.{0})
    (p : UpperHalfPlane → S.carrier)
    (hp : letI := S.chartedSpace; MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p)
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ)) :
    @MDifferentiable ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ) UpperHalfPlane _ _
      ℂ _ _ ℂ _ 𝓘(ℂ) S.carrier S.topologicalSpace
      (originalMirrorNative S).toRiemannAtlas.toChartedSpace (fun τ => p (σ τ)) := by
  have hmirror := originalMirrorCover_mdifferentiable S p hp
  have hcomp :
      @MDifferentiable ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ) UpperHalfPlane _ _
        ℂ _ _ ℂ _ 𝓘(ℂ) S.carrier S.topologicalSpace (originalMirrorChartedSpace S)
        ((fun z : originalMirrorLowerDomain => originalMirrorCover p z) ∘
          (originalMirrorUpperNegation : UpperHalfPlane → originalMirrorLowerDomain)) :=
    @MDifferentiable.comp
      ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ) UpperHalfPlane _ _
      ℂ _ _ ℂ _ 𝓘(ℂ) originalMirrorLowerDomain inferInstance inferInstance
      ℂ _ _ ℂ _ 𝓘(ℂ) S.carrier S.topologicalSpace (originalMirrorChartedSpace S)
      originalMirrorUpperNegation
      (fun z : originalMirrorLowerDomain => originalMirrorCover p z)
      hmirror originalMirrorUpperNegation_mdifferentiable
  simp only [Function.comp_def] at hcomp
  rw [originalMirrorUpperCover_eq S p σ hσ] at hcomp
  exact @MDifferentiable.comp
    ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ) UpperHalfPlane _ _
    ℂ _ _ ℂ _ 𝓘(ℂ) S.carrier S.topologicalSpace (originalMirrorChartedSpace S)
    ℂ _ _ ℂ _ 𝓘(ℂ) S.carrier S.topologicalSpace
      (originalMirrorNative S).toRiemannAtlas.toChartedSpace
    (fun τ => p (σ τ)) id
    (closedTarget_identity_biholomorphic (originalMirrorClosedRS S)).1 hcomp

/-- The same original covering and the actual mirror action give its literal mirror uniformization. -/
theorem originalMirrorUpperCover_isUniformization (S : LiZhongQC.ClosedRS.{0})
    {Γ Γσ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (p : UpperHalfPlane → S.carrier)
    (hp : @LiZhongQC.IsUniformization S.carrier S.topologicalSpace S.chartedSpace Γ p)
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    (hs₁ : ∀ γ ∈ Γσ, ∃ γ₀ ∈ Γ, ∀ τ, σ (γ • τ) = γ₀ • σ τ)
    (hs₂ : ∀ γ₀ ∈ Γ, ∃ γ ∈ Γσ, ∀ τ, σ (γ • τ) = γ₀ • σ τ) :
    @LiZhongQC.IsUniformization S.carrier S.topologicalSpace
      (originalMirrorNative S).toRiemannAtlas.toChartedSpace Γσ (fun τ => p (σ τ)) := by
  refine ⟨hp.1.comp_homeomorph σ, ?_, hp.2.2.1.comp σ.surjective, ?_⟩
  · exact originalMirrorUpperCover_mdifferentiable S p hp.2.1 σ hσ
  · intro τ υ
    rw [hp.2.2.2]
    constructor
    · rintro ⟨γ₀, hγ₀, hτυ⟩
      obtain ⟨γ, hγ, hrel⟩ := hs₂ γ₀ hγ₀
      refine ⟨γ, hγ, σ.injective ?_⟩
      rw [hrel]
      exact hτυ
    · rintro ⟨γ, hγ, hτυ⟩
      obtain ⟨γ₀, hγ₀, hrel⟩ := hs₁ γ hγ
      refine ⟨γ₀, hγ₀, ?_⟩
      rw [← hrel, hτυ]

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
