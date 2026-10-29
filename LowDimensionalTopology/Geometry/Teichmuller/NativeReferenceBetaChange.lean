module

public import LowDimensionalTopology.Geometry.Teichmuller.RawBersQuotient

/-!
# The original given-reference map on the nonsymmetric lower-plane model

The given marked-surface change acts on the actual lower-plane equivalence
classes through the proved original group correspondence. Every native
coefficient class changes by the actual normalized composition coefficient.
The true original Bers map intertwines this action with the already proved
whole-domain reference change. Both directions are holomorphic everywhere
for the book topology and the original Bers atlases.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.RawBersQuotient

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport TeichmullerSpace

universe u
variable {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (R : ClosedRiemannSurface A) (R1 : ClosedRiemannSurface B)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hgenus1 : R1.HasGenus g)
    (e : A ≃ₜ B)
    (he : let := R.toRiemannAtlas.toChartedSpace
      let := R1.toRiemannAtlas.toChartedSpace; LiZhongQC.IsQCRS e)
    {Γ Γ1 : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) (hΓ1 : LiZhongQC.IsFuchsian Γ1)
    {p : ℍ → A} {p1 : ℍ → B}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (hp1 : let := R1.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ1 p1)

/-- The actual weighted Bers embedding of the raw lower-plane classes. -/
def betaWeightedBersEmbedding (a : TeichBeta Γ) : BersWeighted.Automorphic Γ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  exact TeichmullerSpace.weightedBersEmbedding R hg hgenus hΓ
    (LiZhongQC.s27g_actsFreely hp) hp
    ((TeichmullerSpace.gammaEquiv R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ (LiZhongQC.s27g_actsFreely hp) hp).symm (betaGammaEquiv Γ a))

/-- This faithful weighted vector is exactly the original Schwarzian of the
actual nonsymmetric normalized solution on every original lower-plane class. -/
theorem betaWeightedBersEmbedding_toSource (a : TeichBeta Γ) :
    ((betaWeightedBersEmbedding R hg hgenus hΓ hp a).toSource : ℂ → ℂ) = bersMap Γ a := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let E := TeichmullerSpace.gammaEquiv R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ (LiZhongQC.s27g_actsFreely hp) hp
  have h := TeichmullerSpace.weightedBersEmbedding_toSource R hg hgenus hΓ
    (LiZhongQC.s27g_actsFreely hp) hp ((E).symm (betaGammaEquiv Γ a))
  exact h.trans (congrArg (LiZhongQC.bersMapGamma Γ) ((E).apply_symm_apply _))

/-- The original reference change on the actual nonsymmetric lower-plane classes. -/
def referenceBetaEquiv : TeichBeta Γ ≃ TeichBeta Γ1 :=
  (betaGammaEquiv Γ).trans
    ((referenceGammaEquiv R R1 hg hgenus hgenus1 e he hΓ hΓ1 hp hp1).trans
      (betaGammaEquiv Γ1).symm)

/-- On every original coefficient this is precisely the class of its actual
normalized composition coefficient, retaining the given lift and its real normalization. -/
theorem referenceBetaEquiv_coefficientProjection
    (w : ℍ ≃ₜ ℍ) (hw : LiZhongQC.IsLift p p1 e w) (ν : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ) (μ : Ball Γ) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R1.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R1.toRiemannAtlas.isManifold
    referenceBetaEquiv R R1 hg hgenus hgenus1 e he hΓ hΓ1 hp hp1
        (Quotient.mk _ (toSourceGamma μ)) =
      Quotient.mk _ (toSourceGamma (givenReferenceChangedBall hp hp1 hΓ e w hw ν M hM μ)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  change (betaGammaEquiv Γ1).symm
    (referenceGammaEquiv R R1 hg hgenus hgenus1 e he hΓ hΓ1 hp hp1
      (Quotient.mk _ (toSourceGamma μ))) = _
  rw [referenceGammaEquiv_coefficientProjection R R1 hg hgenus hgenus1 e he
    hΓ hΓ1 hp hp1 w hw ν M hM μ]
  exact betaGammaEquiv_symm_mk _

/-- The original Bers diagram commutes on EVERY raw lower-plane class:
the fourth map is literally the Bers conjugate of the third original map. -/
theorem referenceBetaEquiv_bersDiagram
    (w : ℍ ≃ₜ ℍ) (hw : LiZhongQC.IsLift p p1 e w) (ν : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ) (a : TeichBeta Γ) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R1.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R1.toRiemannAtlas.isManifold
    betaWeightedBersEmbedding R1 hg hgenus1 hΓ1 hp1
        (referenceBetaEquiv R R1 hg hgenus hgenus1 e he hΓ hΓ1 hp hp1 a) =
      givenReferenceBersMap hp hp1 hΓ e w hw ν M hM
        (betaWeightedBersEmbedding R hg hgenus hΓ hp a) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  let E := TeichmullerSpace.gammaEquiv R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let E1 := TeichmullerSpace.gammaEquiv R1 hg hgenus1 (canonicalHandleGroupPresentation g)
    hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  let a0 := (E).symm (betaGammaEquiv Γ a)
  let W1 := weightedLinearBersCoordinates R1 hg hgenus1
    (canonicalHandleGroupPresentation g) hΓ1 hp1
  have hgamma : betaGammaEquiv Γ1
        (referenceBetaEquiv R R1 hg hgenus hgenus1 e he hΓ hΓ1 hp hp1 a) =
      referenceGammaEquiv R R1 hg hgenus hgenus1 e he hΓ hΓ1 hp hp1
        (betaGammaEquiv Γ a) := by
    change (betaGammaEquiv Γ1) ((betaGammaEquiv Γ1).symm _) = _
    exact (betaGammaEquiv Γ1).apply_symm_apply _
  have href : (E1).symm (betaGammaEquiv Γ1
        (referenceBetaEquiv R R1 hg hgenus hgenus1 e he hΓ hΓ1 hp hp1 a)) =
      referenceChangeEquiv R R1 hg hgenus hgenus1 e he a0 := by
    refine (congrArg (E1).symm hgamma).trans ?_
    change (E1).symm ((E1) (referenceChangeEquiv R R1 hg hgenus hgenus1 e he a0)) = _
    exact (E1).symm_apply_apply _
  change (W1).symm (bersCoordinates R1 hg hgenus1 (canonicalHandleGroupPresentation g)
      hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
      ((E1).symm (betaGammaEquiv Γ1
        (referenceBetaEquiv R R1 hg hgenus hgenus1 e he hΓ hΓ1 hp hp1 a)))) = _
  rw [href, referenceChangeEquiv_bersCoordinates R R1 hg hgenus hgenus1 e he
    hΓ hΓ1 hp hp1 w hw ν M hM a0]
  exact (W1).symm_apply_apply _

/-- The whole actual reference map and its true inverse are holomorphic on
all original lower-plane classes, in their book topologies and Bers atlases. -/
theorem referenceBetaEquiv_contMDiff_bothDirections
    (w : ℍ ≃ₜ ℍ) (hw : LiZhongQC.IsLift p p1 e w) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R1.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R1.toRiemannAtlas.isManifold
    letI := betaMetricSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
    letI := betaMetricSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
    letI := betaBersChartedSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
    letI := betaBersChartedSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
    ContMDiff 𝓘(ℂ, Fin (3*g-3) → ℂ) 𝓘(ℂ, Fin (3*g-3) → ℂ) ω
        (referenceBetaEquiv R R1 hg hgenus hgenus1 e he hΓ hΓ1 hp hp1) ∧
      ContMDiff 𝓘(ℂ, Fin (3*g-3) → ℂ) 𝓘(ℂ, Fin (3*g-3) → ℂ) ω
        (referenceBetaEquiv R R1 hg hgenus hgenus1 e he hΓ hΓ1 hp hp1).symm := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  let := gammaQCMetricSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let := gammaQCMetricSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  let := betaMetricSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let := betaMetricSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  let := gammaBersChartedSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let := gammaBersChartedSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  let := betaBersChartedSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let := betaBersChartedSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  obtain ⟨hE, hEi⟩ := betaGammaEquiv_contMDiff_bothDirections R hg hgenus hΓ
    (LiZhongQC.s27g_actsFreely hp) hp
  obtain ⟨hE1, hE1i⟩ := betaGammaEquiv_contMDiff_bothDirections R1 hg hgenus1 hΓ1
    (LiZhongQC.s27g_actsFreely hp1) hp1
  obtain ⟨hF, hFi⟩ := referenceGammaEquiv_contMDiff_bothDirections R R1 hg hgenus hgenus1
    e he hΓ hΓ1 hp hp1 w hw
  exact ⟨hE1i.comp (hF.comp hE), hEi.comp (hFi.comp hE1)⟩

end LowDimensionalTopology.Geometry.Teichmuller.RawBersQuotient
