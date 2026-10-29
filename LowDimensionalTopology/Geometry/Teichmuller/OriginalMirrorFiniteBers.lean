module

public import LowDimensionalTopology.Geometry.Teichmuller.FixedBersReflectionAutomorphic
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMirrorUpperUniformization
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMirroredMarked
public import LowDimensionalTopology.Geometry.Teichmuller.NativeAhlforsWeillNeighborhood
public import Mathlib.Topology.Algebra.Module.Star

/-!
# The literal mirror in the two actual chosen finite Bers coordinates

The source and mirror coordinates are their independently chosen existing
continuous linear equivalences. Their conversion conjugates complex scalars.
Its linear factor retains both choices on the entire finite vector space.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set
open scoped Manifold ContDiff ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces LiZhongQC GammaMeasurableBeltrami BersWeighted GeneralQC

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)

/-- Inverting the chosen original coordinates retains the entire actual Bers function. -/
theorem gammaBersCoordinates_weighted_source (hfree : ActsFreely Γ) (a : TeichGamma Γ) :
    (((weightedLinearBersCoordinates R hg hgenus
      (canonicalHandleGroupPresentation g) hΓ hp).symm
        (gammaBersCoordinates R hg hgenus hΓ hfree hp a)).toSource : ℂ → ℂ) =
      bersMapGamma Γ a := by
  have h := weightedBersEmbedding_toSource R hg hgenus hΓ hfree hp
    ((gammaEquiv R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp).symm a)
  simpa only [weightedBersEmbedding, gammaBersCoordinates, Equiv.apply_symm_apply] using h

/-- The actual mirror conversion keeps the two independently chosen coordinate maps. -/
def originalMirrorFiniteBersReflection :
    (Fin (3 * g - 3) → ℂ) ≃L⋆[ℂ] (Fin (3 * g - 3) → ℂ) := by
  classical
  letI := R.toRiemannAtlas.toChartedSpace
  let E := bsu24_mirror_group hΓ (s27g_actsFreely hp)
  let Γσ := Classical.choose E
  let Eσ := Classical.choose_spec E
  let σ := Classical.choose Eσ
  let hs := Classical.choose_spec Eσ
  let RStar := originalMirrorNative R.toSourceClosedRS
  let hpSigma := originalMirrorUpperCover_isUniformization
    R.toSourceClosedRS p hp σ hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  let W := weightedLinearBersCoordinates R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hp
  let WStar := weightedLinearBersCoordinates RStar hg
    (originalMirrorNative_hasGenus R hgenus) (canonicalHandleGroupPresentation g) hs.1 hpSigma
  let K : Automorphic Γ ≃ₗᵢ⋆[ℂ] Automorphic Γσ :=
    automorphicFixedBersReflection σ hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  exact W.symm.trans (K.toContinuousLinearEquiv.trans WStar)

/-- Every original coefficient class satisfies the literal chosen-coordinate mirror square. -/
theorem originalMirrorFiniteBersReflection_coefficientSquare :
    letI := R.toRiemannAtlas.toChartedSpace
    let E := bsu24_mirror_group hΓ (s27g_actsFreely hp)
    let Γσ := Classical.choose E
    let Eσ := Classical.choose_spec E
    let σ := Classical.choose Eσ
    let hs := Classical.choose_spec Eσ
    let RStar := originalMirrorNative R.toSourceClosedRS
    let hpSigma := originalMirrorUpperCover_isUniformization
      R.toSourceClosedRS p hp σ hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
    let rho : BeltramiGamma Γ → BeltramiGamma Γσ :=
      fixedBersReflectionGamma σ hs.2.2.1 hs.2.2.2.1
    ∀ μ : BeltramiGamma Γ,
      gammaBersCoordinates RStar hg (originalMirrorNative_hasGenus R hgenus)
        hs.1 hs.2.1 hpSigma (Quotient.mk _ (rho μ)) =
      originalMirrorFiniteBersReflection R hg hgenus hΓ hp
        (gammaBersCoordinates R hg hgenus hΓ (s27g_actsFreely hp) hp (Quotient.mk _ μ)) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let E := bsu24_mirror_group hΓ (s27g_actsFreely hp)
  let Γσ := Classical.choose E
  let Eσ := Classical.choose_spec E
  let σ := Classical.choose Eσ
  let hs := Classical.choose_spec Eσ
  let RStar := originalMirrorNative R.toSourceClosedRS
  let hpSigma := originalMirrorUpperCover_isUniformization
    R.toSourceClosedRS p hp σ hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  let rho : BeltramiGamma Γ → BeltramiGamma Γσ :=
    fixedBersReflectionGamma σ hs.2.2.1 hs.2.2.2.1
  let W := weightedLinearBersCoordinates R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hp
  let WStar := weightedLinearBersCoordinates RStar hg
    (originalMirrorNative_hasGenus R hgenus) (canonicalHandleGroupPresentation g) hs.1 hpSigma
  let K : Automorphic Γ ≃ₗᵢ⋆[ℂ] Automorphic Γσ :=
    automorphicFixedBersReflection σ hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  let G := gammaBersCoordinates R hg hgenus hΓ (s27g_actsFreely hp) hp
  let GStar := gammaBersCoordinates RStar hg (originalMirrorNative_hasGenus R hgenus)
    hs.1 hs.2.1 hpSigma
  change ∀ μ : BeltramiGamma Γ, GStar (Quotient.mk _ (rho μ)) =
    WStar (K (W.symm (G (Quotient.mk _ μ))))
  intro μ
  have hnative : WStar.symm (GStar (Quotient.mk _ (rho μ))) =
      K (W.symm (G (Quotient.mk _ μ))) := by
    apply Automorphic.toSource_injective
    apply Subtype.ext
    erw [gammaBersCoordinates_weighted_source,
      automorphicFixedBersReflection_toSource, gammaBersCoordinates_weighted_source,
      bg_bersMapGamma_eq (μ := rho μ) rfl, bg_bersMapGamma_eq (μ := μ) rfl]
    exact rawBers_fixedBersReflection μ.val
  have h := congrArg WStar hnative
  rw [WStar.apply_symm_apply] at h
  exact h

/-- The actual complex-linear conversion retains both coordinate choices on every vector. -/
def originalMirrorFiniteBersLinear :
    (Fin (3 * g - 3) → ℂ) ≃L[ℂ] (Fin (3 * g - 3) → ℂ) :=
  (starL ℂ : (Fin (3 * g - 3) → ℂ) ≃L⋆[ℂ] (Fin (3 * g - 3) → ℂ)).trans
    (originalMirrorFiniteBersReflection R hg hgenus hΓ hp)

/-- The mirror is this retained linear conversion after coordinate conjugation. -/
theorem originalMirrorFiniteBersReflection_eq_linear (v : Fin (3 * g - 3) → ℂ) :
    originalMirrorFiniteBersReflection R hg hgenus hΓ hp v =
      originalMirrorFiniteBersLinear R hg hgenus hΓ hp (fun j => conj (v j)) := by
  change originalMirrorFiniteBersReflection R hg hgenus hΓ hp v =
    originalMirrorFiniteBersReflection R hg hgenus hΓ hp (fun j => conj (conj (v j)))
  apply congrArg (originalMirrorFiniteBersReflection R hg hgenus hΓ hp)
  funext j
  exact (Complex.conj_conj (v j)).symm

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
