module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceBetaChange

/-!
# Reference invariance of the original Teichmuller complex structures

For the original given quasiconformal reference homeomorphism and its given
lift, the original marked-surface map, original symmetric boundary map,
original nonsymmetric lower-plane map, and its true Bers conjugate are all
biholomorphic. The coefficient normalization is derived from that same lift.
The complete coefficient-class formula and the Bers diagram hold, retaining
the original objects and all points of both complete Bers domains.

All topologies below are the original book topologies: the native global
Bers topology, the genuine group QC metric topology, and its explicitly
transported nonsymmetric lower-plane quotient topology. No comparison with
the default realized-coefficient quotient topology is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport RawBersQuotient

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

local notation "Z" => Fin (3*g-3) → ℂ
local notation "I" => 𝓘(ℂ, Z)
local notation "F_R" => referenceChangeEquiv R R1 hg hgenus hgenus1 e he
local notation "F_Γ" => referenceGammaEquiv R R1 hg hgenus hgenus1 e he hΓ hΓ1 hp hp1
local notation "F_β" => referenceBetaEquiv R R1 hg hgenus hgenus1 e he hΓ hΓ1 hp hp1

/-- All four original reference maps are biholomorphic, for any actual given
reference lift. The real normalization is derived, every coefficient class
has the actual composition value, and the Bers conjugacy holds on every class. -/
theorem exists_original_reference_maps_biholomorphic
    (w : ℍ ≃ₜ ℍ) (hw : LiZhongQC.IsLift p p1 e w) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R1.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R1.toRiemannAtlas.isManifold
    let : TopologicalSpace (TeichmullerSpace.{u,u} R) :=
      bersTopology R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ (LiZhongQC.s27g_actsFreely hp) hp
    let : TopologicalSpace (TeichmullerSpace.{u,u} R1) :=
      bersTopology R1 hg hgenus1 (canonicalHandleGroupPresentation g)
        hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
    letI := gammaQCMetricSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
    letI := gammaQCMetricSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
    letI := betaMetricSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
    letI := betaMetricSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
    letI := bersChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ (LiZhongQC.s27g_actsFreely hp) hp
    letI := bersChartedSpace R1 hg hgenus1 (canonicalHandleGroupPresentation g)
      hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
    letI := gammaBersChartedSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
    letI := gammaBersChartedSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
    letI := betaBersChartedSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
    letI := betaBersChartedSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
    ∃ (ν : Ball Γ) (M : Deck)
      (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ),
      (planeRepresentative ν.val.val =ᵐ[volume.restrict LiZhongQC.upperHalf]
        LiZhongQC.s27u_liftCoeff p e) ∧
      (ContMDiff I I ω (F_R) ∧ ContMDiff I I ω (F_R).symm) ∧
      (ContMDiff I I ω (F_Γ) ∧ ContMDiff I I ω (F_Γ).symm) ∧
      (ContMDiff I I ω (F_β) ∧ ContMDiff I I ω (F_β).symm) ∧
      (AnalyticOnNhd ℂ (givenReferenceBersMap hp hp1 hΓ e w hw ν M hM)
          (coefficientBersImage hΓ) ∧
        AnalyticOnNhd ℂ (inverseGivenReferenceBersMap hp hp1 hΓ e w hw ν M hM)
          (coefficientBersImage hΓ1)) ∧
      (∀ φ : coefficientBersImage hΓ,
        (givenReferenceBersEquiv hp hp1 hΓ hΓ1 e w hw ν M hM φ).val =
          givenReferenceBersMap hp hp1 hΓ e w hw ν M hM φ.val) ∧
      (∀ ψ : coefficientBersImage hΓ1,
        ((givenReferenceBersEquiv hp hp1 hΓ hΓ1 e w hw ν M hM).symm ψ).val =
          inverseGivenReferenceBersMap hp hp1 hΓ e w hw ν M hM ψ.val) ∧
      (∀ μ : Ball Γ, F_β (Quotient.mk _ (toSourceGamma μ)) =
        Quotient.mk _ (toSourceGamma (givenReferenceChangedBall hp hp1 hΓ e w hw ν M hM μ))) ∧
      (∀ a : TeichBeta Γ,
        betaWeightedBersEmbedding R1 hg hgenus1 hΓ1 hp1 (F_β a) =
          givenReferenceBersMap hp hp1 hΓ e w hw ν M hM
            (betaWeightedBersEmbedding R hg hgenus hΓ hp a)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  let : TopologicalSpace (TeichmullerSpace.{u,u} R) :=
    bersTopology R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let : TopologicalSpace (TeichmullerSpace.{u,u} R1) :=
    bersTopology R1 hg hgenus1 (canonicalHandleGroupPresentation g)
      hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  let := gammaQCMetricSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let := gammaQCMetricSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  let := betaMetricSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let := betaMetricSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  let := bersChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let := bersChartedSpace R1 hg hgenus1 (canonicalHandleGroupPresentation g)
    hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  let := gammaBersChartedSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let := gammaBersChartedSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  let := betaBersChartedSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let := betaBersChartedSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  obtain ⟨ν, M, hν, hM, _⟩ :=
    exists_native_normalization_of_given_lift hp hp1 e he w hw
  refine ⟨ν, M, hM, hν, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact referenceChangeEquiv_contMDiff_bothDirections R R1 hg hgenus hgenus1
      e he hΓ hΓ1 hp hp1 w hw
  · exact referenceGammaEquiv_contMDiff_bothDirections R R1 hg hgenus hgenus1
      e he hΓ hΓ1 hp hp1 w hw
  · exact referenceBetaEquiv_contMDiff_bothDirections R R1 hg hgenus hgenus1
      e he hΓ hΓ1 hp hp1 w hw
  · exact givenReferenceBersMap_analytic_bothDirections R R1 hg hgenus hΓ hΓ1
      hp hp1 e w hw ν M hM
  · intro φ
    exact givenReferenceBersEquiv_apply hp hp1 hΓ hΓ1 e w hw ν M hM φ
  · intro ψ
    exact givenReferenceBersEquiv_symm_apply hp hp1 hΓ hΓ1 e w hw ν M hM ψ
  · intro μ
    exact referenceBetaEquiv_coefficientProjection R R1 hg hgenus hgenus1
      e he hΓ hΓ1 hp hp1 w hw ν M hM μ
  · intro a
    exact referenceBetaEquiv_bersDiagram R R1 hg hgenus hgenus1
      e he hΓ hΓ1 hp hp1 w hw ν M hM a

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
