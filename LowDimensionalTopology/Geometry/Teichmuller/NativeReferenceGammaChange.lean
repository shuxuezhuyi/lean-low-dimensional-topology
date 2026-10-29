module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceChange
public import LowDimensionalTopology.Geometry.Teichmuller.NativeAhlforsWeillNeighborhood

/-!
# The original reference change on the genuine group Teichmuller spaces

The actual normalized-lift equivalences carry the given marked-surface
reference change to the original compatible-coefficient quotients. Its
value on every coefficient class is proved with the actual changed
coefficient. The existing Bers atlases on the original QC metric spaces
make the equivalence holomorphic in both directions at every point.
No coefficient-quotient topology comparison or new complex atlas is assumed.

The original normalized-lift and coefficient conventions reuse Wu Xiaobin's
Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

universe u

/-- The original normalized-lift equivalence is biholomorphic for the
existing native Bers atlas and the original group QC metric Bers atlas. -/
theorem gammaEquiv_contMDiff_bothDirections
    {A : Type u} [TopologicalSpace A] (R : ClosedRiemannSurface A)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ)
    (hfree : LiZhongQC.ActsFreely Γ) {p : ℍ → A}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p) :
    let : TopologicalSpace (TeichmullerSpace.{u,u} R) :=
      bersTopology R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp
    let : MetricSpace (LiZhongQC.TeichGamma Γ) := gammaQCMetricSpace R hg hgenus hΓ hfree hp
    let : ChartedSpace (Fin (3*g-3) → ℂ) (TeichmullerSpace.{u,u} R) :=
      bersChartedSpace R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp
    let : ChartedSpace (Fin (3*g-3) → ℂ) (LiZhongQC.TeichGamma Γ) :=
      gammaBersChartedSpace R hg hgenus hΓ hfree hp
    ContMDiff 𝓘(ℂ, Fin (3*g-3) → ℂ) 𝓘(ℂ, Fin (3*g-3) → ℂ) ω
        (gammaEquiv R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp) ∧
      ContMDiff 𝓘(ℂ, Fin (3*g-3) → ℂ) 𝓘(ℂ, Fin (3*g-3) → ℂ) ω
        (gammaEquiv R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp).symm := by
  let : TopologicalSpace (TeichmullerSpace.{u,u} R) :=
    bersTopology R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp
  let : MetricSpace (LiZhongQC.TeichGamma Γ) := gammaQCMetricSpace R hg hgenus hΓ hfree hp
  let : ChartedSpace (Fin (3*g-3) → ℂ) (TeichmullerSpace.{u,u} R) :=
    bersChartedSpace R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp
  let : ChartedSpace (Fin (3*g-3) → ℂ) (LiZhongQC.TeichGamma Γ) :=
    gammaBersChartedSpace R hg hgenus hΓ hfree hp
  let : Nonempty (LiZhongQC.TeichGamma Γ) := ⟨LiZhongQC.TeichGamma.origin Γ⟩
  let E := gammaEquiv R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp
  let BC := bersCoordinates R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp
  let G := gammaBersCoordinates R hg hgenus hΓ hfree hp
  have hBC : ContMDiff 𝓘(ℂ, Fin (3*g-3) → ℂ) 𝓘(ℂ, Fin (3*g-3) → ℂ) ω BC :=
    contMDiff_isOpenEmbedding
      (bersCoordinates_isOpenEmbedding R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ hfree hp)
  have hG : ContMDiff 𝓘(ℂ, Fin (3*g-3) → ℂ) 𝓘(ℂ, Fin (3*g-3) → ℂ) ω G :=
    contMDiff_isOpenEmbedding (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp)
  constructor
  · have hcomp : ContMDiff 𝓘(ℂ, Fin (3*g-3) → ℂ) 𝓘(ℂ, Fin (3*g-3) → ℂ) ω
        (G ∘ E) := hBC.congr (fun a => by
      change BC (E.symm (E a)) = BC a
      rw [E.symm_apply_apply])
    exact hcomp.of_comp_isOpenEmbedding
      (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp)
  · have hcomp : ContMDiff 𝓘(ℂ, Fin (3*g-3) → ℂ) 𝓘(ℂ, Fin (3*g-3) → ℂ) ω
        (BC ∘ E.symm) := hG
    exact hcomp.of_comp_isOpenEmbedding
      (bersCoordinates_isOpenEmbedding R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ hfree hp)

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

/-- The original given reference map on the original group coefficient
quotients, using their actual normalized-lift equivalences. -/
def referenceGammaEquiv : LiZhongQC.TeichGamma Γ ≃ LiZhongQC.TeichGamma Γ1 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  exact (gammaEquiv R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ (LiZhongQC.s27g_actsFreely hp) hp).symm.trans
    ((referenceChangeEquiv R R1 hg hgenus hgenus1 e he).trans
      (gammaEquiv R1 hg hgenus1 (canonicalHandleGroupPresentation g)
        hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1))

/-- Every coefficient class is changed by the actual normalized translation
and the literal real Mobius coefficient transport derived from the given lift. -/
theorem referenceGammaEquiv_coefficientProjection
    (w : ℍ ≃ₜ ℍ) (hw : LiZhongQC.IsLift p p1 e w) (ν : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ) (μ : Ball Γ) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R1.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R1.toRiemannAtlas.isManifold
    referenceGammaEquiv R R1 hg hgenus hgenus1 e he hΓ hΓ1 hp hp1
        (Quotient.mk _ (toSourceGamma μ)) =
      Quotient.mk _ (toSourceGamma (givenReferenceChangedBall hp hp1 hΓ e w hw ν M hM μ)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  let E1 := gammaEquiv R1 hg hgenus1 (canonicalHandleGroupPresentation g)
    hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  change E1 (referenceChangeEquiv R R1 hg hgenus hgenus1 e he
    (coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ (LiZhongQC.s27g_actsFreely hp) hp μ)) = _
  rw [referenceChangeEquiv_coefficientProjection R R1 hg hgenus hgenus1 e he
    hΓ hΓ1 hp hp1 w hw ν M hM μ]
  exact E1.apply_symm_apply _

/-- The actual given reference change is biholomorphic on the ENTIRE
original group spaces with their original QC metric topologies and existing
Bers complex atlases. No smoothing or new atlas is used. -/
theorem referenceGammaEquiv_contMDiff_bothDirections
    (w : ℍ ≃ₜ ℍ) (hw : LiZhongQC.IsLift p p1 e w) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R1.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R1.toRiemannAtlas.isManifold
    let : MetricSpace (LiZhongQC.TeichGamma Γ) :=
      gammaQCMetricSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
    let : MetricSpace (LiZhongQC.TeichGamma Γ1) :=
      gammaQCMetricSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
    let : ChartedSpace (Fin (3*g-3) → ℂ) (LiZhongQC.TeichGamma Γ) :=
      gammaBersChartedSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
    let : ChartedSpace (Fin (3*g-3) → ℂ) (LiZhongQC.TeichGamma Γ1) :=
      gammaBersChartedSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
    ContMDiff 𝓘(ℂ, Fin (3*g-3) → ℂ) 𝓘(ℂ, Fin (3*g-3) → ℂ) ω
        (referenceGammaEquiv R R1 hg hgenus hgenus1 e he hΓ hΓ1 hp hp1) ∧
      ContMDiff 𝓘(ℂ, Fin (3*g-3) → ℂ) 𝓘(ℂ, Fin (3*g-3) → ℂ) ω
        (referenceGammaEquiv R R1 hg hgenus hgenus1 e he hΓ hΓ1 hp hp1).symm := by
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
  let : MetricSpace (LiZhongQC.TeichGamma Γ) :=
    gammaQCMetricSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let : MetricSpace (LiZhongQC.TeichGamma Γ1) :=
    gammaQCMetricSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  let : ChartedSpace (Fin (3*g-3) → ℂ) (TeichmullerSpace.{u,u} R) :=
    bersChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let : ChartedSpace (Fin (3*g-3) → ℂ) (TeichmullerSpace.{u,u} R1) :=
    bersChartedSpace R1 hg hgenus1 (canonicalHandleGroupPresentation g)
      hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  let : ChartedSpace (Fin (3*g-3) → ℂ) (LiZhongQC.TeichGamma Γ) :=
    gammaBersChartedSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let : ChartedSpace (Fin (3*g-3) → ℂ) (LiZhongQC.TeichGamma Γ1) :=
    gammaBersChartedSpace R1 hg hgenus1 hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  obtain ⟨hE, hEi⟩ := gammaEquiv_contMDiff_bothDirections R hg hgenus hΓ
    (LiZhongQC.s27g_actsFreely hp) hp
  obtain ⟨hE1, hE1i⟩ := gammaEquiv_contMDiff_bothDirections R1 hg hgenus1 hΓ1
    (LiZhongQC.s27g_actsFreely hp1) hp1
  obtain ⟨hF, hFi⟩ := referenceChangeEquiv_contMDiff_bothDirections R R1 hg hgenus hgenus1
    e he hΓ hΓ1 hp hp1 w hw
  constructor
  · exact hE1.comp (hF.comp hEi)
  · exact hE.comp (hFi.comp hE1i)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
