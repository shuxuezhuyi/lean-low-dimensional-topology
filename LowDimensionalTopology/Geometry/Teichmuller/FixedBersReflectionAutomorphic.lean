module

public import LowDimensionalTopology.Geometry.Teichmuller.FixedBersReflectionQuadraticDifferential
public import LowDimensionalTopology.Geometry.Teichmuller.BersWeightedCoordinates
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Literal reflection is an isometry of the actual weighted automorphic spaces

Every canonically extended point value is retained by the existing faithful
weighted realization. The map conjugates complex scalars. Both actual action
relations give its inverse, and the two weighted bounds give norm equality.
No basis or standard finite-coordinate norm is identified with its reflection.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

open LiZhongQC GammaMeasurableBeltrami

/-- Literal minus-conjugation preserves the same square-height bound. -/
theorem fixedBersReflection_weighted_bound {Γ : Subgroup Deck} (φ : Automorphic Γ) :
    ∀ z ∈ lowerHalf,
      ‖fixedBersReflectedPlaneFunction (φ.toSource : ℂ → ℂ) z‖ * z.im ^ 2 ≤ ‖φ‖ := by
  intro z hz
  have hσz : -conj z ∈ lowerHalf := by
    simpa only [lowerHalf, mem_ofPred_eq, neg_im, conj_im, neg_neg] using hz
  change ‖fixedBersReflectedPlaneFunction (φ.toSource : ℂ → ℂ) z‖ * z.im ^ 2 ≤ ‖φ.val‖
  simpa only [fixedBersReflectedPlaneFunction, Automorphic.toSource_apply,
    norm_conj, neg_im, conj_im, neg_neg] using decode_weightedBound φ.val (-conj z) hσz

/-- Encode the SAME reflected source form in the existing weighted normed space. -/
def fixedBersReflectionNative {Γ Γσ : Subgroup Deck}
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    (hs : ∀ γ ∈ Γσ, ∃ γ0 ∈ Γ, ∀ τ, σ (γ • τ) = γ0 • σ τ)
    (φ : Automorphic Γ) : Automorphic Γσ :=
  Automorphic.ofSource
    ⟨fixedBersReflectedPlaneFunction (φ.toSource : ℂ → ℂ),
      fixedBersReflectedPlaneFunction_mem_automorphicQD σ hσ hs φ.toSource⟩
    ⟨‖φ‖, fixedBersReflection_weighted_bound φ⟩

/-- The native map retains every literal source value, including the zero extension. -/
theorem fixedBersReflectionNative_toSource {Γ Γσ : Subgroup Deck}
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    (hs : ∀ γ ∈ Γσ, ∃ γ0 ∈ Γ, ∀ τ, σ (γ • τ) = γ0 • σ τ)
    (φ : Automorphic Γ) :
    ((fixedBersReflectionNative σ hσ hs φ).toSource : ℂ → ℂ) =
      fixedBersReflectedPlaneFunction (φ.toSource : ℂ → ℂ) :=
  congrArg (fun q : automorphicQD Γσ => (q : ℂ → ℂ))
    (Automorphic.toSource_ofSource _ _)

/-- Either pair of compatible directions cancels by the SAME literal reflection. -/
theorem fixedBersReflectionNative_twice {Γ Γσ : Subgroup Deck}
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    (hs : ∀ γ ∈ Γσ, ∃ γ0 ∈ Γ, ∀ τ, σ (γ • τ) = γ0 • σ τ)
    (ht : ∀ γ0 ∈ Γ, ∃ γ ∈ Γσ, ∀ τ, σ (γ0 • τ) = γ • σ τ)
    (φ : Automorphic Γ) :
    fixedBersReflectionNative σ hσ ht (fixedBersReflectionNative σ hσ hs φ) = φ := by
  apply Automorphic.toSource_injective
  apply Subtype.ext
  rw [fixedBersReflectionNative_toSource, fixedBersReflectionNative_toSource]
  funext z
  simp only [fixedBersReflectedPlaneFunction, map_neg, Complex.conj_conj, neg_neg]

/-- Pointwise bounds control the actual inherited weighted supremum norm. -/
theorem fixedBersReflectionNative_norm_le {Γ Γσ : Subgroup Deck}
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    (hs : ∀ γ ∈ Γσ, ∃ γ0 ∈ Γ, ∀ τ, σ (γ • τ) = γ0 • σ τ)
    (φ : Automorphic Γ) : ‖fixedBersReflectionNative σ hσ hs φ‖ ≤ ‖φ‖ := by
  change ‖(fixedBersReflectionNative σ hσ hs φ).val‖ ≤ ‖φ‖
  apply lp.norm_le_of_forall_le (norm_nonneg φ)
  intro z
  rw [← norm_decode_mul_weight]
  change ‖((fixedBersReflectionNative σ hσ hs φ).toSource : ℂ → ℂ) z‖ * z.val.im ^ 2 ≤ ‖φ‖
  rw [fixedBersReflectionNative_toSource]
  exact fixedBersReflection_weighted_bound φ z z.property

/-- The literal map conjugates every complex scalar on the entire actual vector space. -/
def fixedBersReflectionSemilinear {Γ Γσ : Subgroup Deck}
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    (hs : ∀ γ ∈ Γσ, ∃ γ0 ∈ Γ, ∀ τ, σ (γ • τ) = γ0 • σ τ) :
    Automorphic Γ →ₛₗ[starRingEnd ℂ] Automorphic Γσ where
  toFun := fixedBersReflectionNative σ hσ hs
  map_add' φ ψ := by
    apply Automorphic.toSource_injective
    apply Subtype.ext
    have hl : ((φ + ψ).toSource : ℂ → ℂ) =
        (φ.toSource : ℂ → ℂ) + (ψ.toSource : ℂ → ℂ) :=
      congrArg (fun q : automorphicQD Γ => (q : ℂ → ℂ))
        (map_add (toSourceLinear Γ) φ ψ)
    have hr : ((fixedBersReflectionNative σ hσ hs φ +
        fixedBersReflectionNative σ hσ hs ψ).toSource : ℂ → ℂ) =
        ((fixedBersReflectionNative σ hσ hs φ).toSource : ℂ → ℂ) +
          ((fixedBersReflectionNative σ hσ hs ψ).toSource : ℂ → ℂ) :=
      congrArg (fun q : automorphicQD Γσ => (q : ℂ → ℂ))
        (map_add (toSourceLinear Γσ)
          (fixedBersReflectionNative σ hσ hs φ) (fixedBersReflectionNative σ hσ hs ψ))
    rw [hr, fixedBersReflectionNative_toSource, fixedBersReflectionNative_toSource,
      fixedBersReflectionNative_toSource, hl]
    funext z
    exact map_add (starRingEnd ℂ) ((φ.toSource : ℂ → ℂ) (-conj z))
      ((ψ.toSource : ℂ → ℂ) (-conj z))
  map_smul' a φ := by
    change fixedBersReflectionNative σ hσ hs (a • φ) =
      conj a • fixedBersReflectionNative σ hσ hs φ
    apply Automorphic.toSource_injective
    apply Subtype.ext
    have hl : ((a • φ).toSource : ℂ → ℂ) = a • (φ.toSource : ℂ → ℂ) :=
      congrArg (fun q : automorphicQD Γ => (q : ℂ → ℂ))
        (map_smul (toSourceLinear Γ) a φ)
    have hr : ((conj a • fixedBersReflectionNative σ hσ hs φ).toSource : ℂ → ℂ) =
        conj a • ((fixedBersReflectionNative σ hσ hs φ).toSource : ℂ → ℂ) :=
      congrArg (fun q : automorphicQD Γσ => (q : ℂ → ℂ))
        (map_smul (toSourceLinear Γσ) (conj a) (fixedBersReflectionNative σ hσ hs φ))
    rw [hr, fixedBersReflectionNative_toSource, fixedBersReflectionNative_toSource, hl]
    funext z
    exact map_mul (starRingEnd ℂ) a ((φ.toSource : ℂ → ℂ) (-conj z))

/-- The actual two action relations give a genuine conjugate-linear weighted isometry. -/
def automorphicFixedBersReflection {Γ Γσ : Subgroup Deck}
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    (hs₁ : ∀ γ ∈ Γσ, ∃ γ0 ∈ Γ, ∀ τ, σ (γ • τ) = γ0 • σ τ)
    (hs₂ : ∀ γ0 ∈ Γ, ∃ γ ∈ Γσ, ∀ τ, σ (γ • τ) = γ0 • σ τ) :
    Automorphic Γ ≃ₗᵢ⋆[ℂ] Automorphic Γσ where
  toLinearEquiv := LinearEquiv.ofBijective (fixedBersReflectionSemilinear σ hσ hs₁)
    ⟨by
      intro φ ψ he
      change fixedBersReflectionNative σ hσ hs₁ φ =
        fixedBersReflectionNative σ hσ hs₁ ψ at he
      have h := congrArg
        (fixedBersReflectionNative σ hσ (fixedBersReflection_reverse_action σ hσ hs₂)) he
      simpa only [fixedBersReflectionNative_twice] using h,
    by
      intro ψ
      refine ⟨fixedBersReflectionNative σ hσ
        (fixedBersReflection_reverse_action σ hσ hs₂) ψ, ?_⟩
      exact fixedBersReflectionNative_twice σ hσ
        (fixedBersReflection_reverse_action σ hσ hs₂) hs₁ ψ⟩
  norm_map' φ := by
    change ‖fixedBersReflectionNative σ hσ hs₁ φ‖ = ‖φ‖
    apply le_antisymm (fixedBersReflectionNative_norm_le σ hσ hs₁ φ)
    have h := fixedBersReflectionNative_norm_le σ hσ
      (fixedBersReflection_reverse_action σ hσ hs₂) (fixedBersReflectionNative σ hσ hs₁ φ)
    rw [fixedBersReflectionNative_twice] at h
    exact h

/-- The isometry has exactly the required literal function value on every vector. -/
theorem automorphicFixedBersReflection_toSource {Γ Γσ : Subgroup Deck}
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    (hs₁ : ∀ γ ∈ Γσ, ∃ γ0 ∈ Γ, ∀ τ, σ (γ • τ) = γ0 • σ τ)
    (hs₂ : ∀ γ0 ∈ Γ, ∃ γ ∈ Γσ, ∀ τ, σ (γ • τ) = γ0 • σ τ)
    (φ : Automorphic Γ) :
    ((automorphicFixedBersReflection σ hσ hs₁ hs₂ φ).toSource : ℂ → ℂ) =
      fixedBersReflectedPlaneFunction (φ.toSource : ℂ → ℂ) :=
  fixedBersReflectionNative_toSource σ hσ hs₁ φ

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
