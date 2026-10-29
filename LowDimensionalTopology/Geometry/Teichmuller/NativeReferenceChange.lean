module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceChangeProjection
public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceBersChange
public import LowDimensionalTopology.Geometry.Teichmuller.ComplexBersMetric
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The original reference map is biholomorphic for the proved Bers complex atlases

The equivalence is the original given reference change on marked quotients,
transported through the proved native-to-QC equivalences. Its coefficient
projection law and its full Bers-coordinate formula are proved first.
The existing global Bers atlases then give holomorphy at every original
point in both directions. These are the existing explicit Bers topologies
on the original native quotients, which are compared with the genuine QC
metric by the existing Bers metric theorem. No equality with the default
realized-coefficient quotient topology is assumed here.

Uses Wu Xiaobin's credited Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami BersWeighted NormalizedCoefficientTransport

universe u
variable {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (R : ClosedRiemannSurface A) (R1 : ClosedRiemannSurface B)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hgenus1 : R1.HasGenus g)
    (e : A ≃ₜ B)
    (he : let := R.toRiemannAtlas.toChartedSpace
      let := R1.toRiemannAtlas.toChartedSpace; LiZhongQC.IsQCRS e)

/-- The actual original marked-quotient reference change on the original native carriers. -/
def referenceChangeEquiv : TeichmullerSpace.{u,u} R ≃ TeichmullerSpace.{u,u} R1 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  exact (sourceEquiv R hg hgenus (canonicalHandleGroupPresentation g)).trans
    ((SourceReferenceChange.quotientEquiv e he).trans
      (sourceEquiv R1 hg hgenus1 (canonicalHandleGroupPresentation g)).symm)

/-- Every original point has exactly the original inverse-precomposed marking class. -/
theorem toSource_referenceChangeEquiv (a : TeichmullerSpace.{u,u} R) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R1.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R1.toRiemannAtlas.isManifold
    toSource R1 (referenceChangeEquiv R R1 hg hgenus hgenus1 e he a) =
      SourceReferenceChange.quotientMap e he (toSource R a) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  change (sourceEquiv R1 hg hgenus1 (canonicalHandleGroupPresentation g))
      ((sourceEquiv R1 hg hgenus1 (canonicalHandleGroupPresentation g)).symm
        (SourceReferenceChange.quotientMap e he (toSource R a))) = _
  exact (sourceEquiv R1 hg hgenus1 (canonicalHandleGroupPresentation g)).apply_symm_apply _

/-- The inverse is the original inverse reference change, retaining every original point. -/
theorem referenceChangeEquiv_symm_apply (b : TeichmullerSpace.{u,u} R1) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R1.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R1.toRiemannAtlas.isManifold
    (referenceChangeEquiv R R1 hg hgenus hgenus1 e he).symm b =
      referenceChangeEquiv R1 R hg hgenus1 hgenus e.symm
        (LiZhongQC.s28q_isQCRS_symm he) b := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  apply toSource_injective R
  have hback := toSource_referenceChangeEquiv R1 R hg hgenus1 hgenus e.symm
    (LiZhongQC.s28q_isQCRS_symm he) b
  refine Eq.trans ?_ hback.symm
  change (sourceEquiv R hg hgenus (canonicalHandleGroupPresentation g))
      ((sourceEquiv R hg hgenus (canonicalHandleGroupPresentation g)).symm
        ((SourceReferenceChange.quotientEquiv e he).symm (toSource R1 b))) = _
  rw [Equiv.apply_symm_apply]
  exact SourceReferenceChange.quotientEquiv_symm_apply e he (toSource R1 b)

variable {Γ Γ1 : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) (hΓ1 : LiZhongQC.IsFuchsian Γ1)
    {p : ℍ → A} {p1 : ℍ → B}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (hp1 : let := R1.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ1 p1)
    (w : ℍ ≃ₜ ℍ) (hw : LiZhongQC.IsLift p p1 e w)
    (ν : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ)

/-- The original native reference map commutes with the original native coefficient projections. -/
theorem referenceChangeEquiv_coefficientProjection (μ : Ball Γ) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R1.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R1.toRiemannAtlas.isManifold
    referenceChangeEquiv R R1 hg hgenus hgenus1 e he
      (coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ (LiZhongQC.s27g_actsFreely hp) hp μ) =
      coefficientProjectionBall R1 hg hgenus1 (canonicalHandleGroupPresentation g)
        hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
          (givenReferenceChangedBall hp hp1 hΓ e w hw ν M hM μ) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  apply toSource_injective R1
  rw [toSource_referenceChangeEquiv]
  exact source_referenceChange_coefficientProjection R R1 hg hgenus hgenus1
    hΓ hΓ1 hp hp1 e he w hw ν M hM μ

/-- The complete original Bers-coordinate diagram holds on EVERY original point. -/
theorem referenceChangeEquiv_bersCoordinates (a : TeichmullerSpace.{u,u} R) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R1.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R1.toRiemannAtlas.isManifold
    bersCoordinates R1 hg hgenus1 (canonicalHandleGroupPresentation g)
        hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
        (referenceChangeEquiv R R1 hg hgenus hgenus1 e he a) =
      weightedLinearBersCoordinates R1 hg hgenus1 (canonicalHandleGroupPresentation g) hΓ1 hp1
        (givenReferenceBersMap hp hp1 hΓ e w hw ν M hM
          ((weightedLinearBersCoordinates R hg hgenus (canonicalHandleGroupPresentation g)
            hΓ hp).symm
            (bersCoordinates R hg hgenus (canonicalHandleGroupPresentation g)
              hΓ (LiZhongQC.s27g_actsFreely hp) hp a))) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  obtain ⟨μ, rfl⟩ := coefficientProjectionBall_surjective R hg hgenus
    hΓ (LiZhongQC.s27g_actsFreely hp) hp a
  rw [referenceChangeEquiv_coefficientProjection R R1 hg hgenus hgenus1 e he
      hΓ hΓ1 hp hp1 w hw ν M hM μ,
    coefficientProjectionBall_coordinates, coefficientProjectionBall_coordinates,
    ContinuousLinearEquiv.symm_apply_apply, givenReferenceBersMap_projection]

include w hw in
/-- In the existing explicit global Bers atlases on the actual original native
quotients, the original given reference map is holomorphic at every point. -/
theorem referenceChangeEquiv_contMDiff :
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
    let : ChartedSpace (Fin (3*g-3) → ℂ) (TeichmullerSpace.{u,u} R) :=
      bersChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ (LiZhongQC.s27g_actsFreely hp) hp
    let : ChartedSpace (Fin (3*g-3) → ℂ) (TeichmullerSpace.{u,u} R1) :=
      bersChartedSpace R1 hg hgenus1 (canonicalHandleGroupPresentation g)
        hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
    ContMDiff 𝓘(ℂ, Fin (3*g-3) → ℂ) 𝓘(ℂ, Fin (3*g-3) → ℂ) ω
      (referenceChangeEquiv R R1 hg hgenus hgenus1 e he) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  let BC := bersCoordinates R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let BC1 := bersCoordinates R1 hg hgenus1 (canonicalHandleGroupPresentation g)
    hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  let W := weightedLinearBersCoordinates R hg hgenus (canonicalHandleGroupPresentation g) hΓ hp
  let W1 := weightedLinearBersCoordinates R1 hg hgenus1 (canonicalHandleGroupPresentation g) hΓ1 hp1
  let : TopologicalSpace (TeichmullerSpace.{u,u} R) :=
    bersTopology R hg hgenus (canonicalHandleGroupPresentation g) hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let : TopologicalSpace (TeichmullerSpace.{u,u} R1) :=
    bersTopology R1 hg hgenus1 (canonicalHandleGroupPresentation g) hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  let : ChartedSpace (Fin (3*g-3) → ℂ) (TeichmullerSpace.{u,u} R) :=
    bersChartedSpace R hg hgenus (canonicalHandleGroupPresentation g) hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let : ChartedSpace (Fin (3*g-3) → ℂ) (TeichmullerSpace.{u,u} R1) :=
    bersChartedSpace R1 hg hgenus1 (canonicalHandleGroupPresentation g) hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  obtain ⟨ν, M, _, hM, _⟩ := exists_native_normalization_of_given_lift hp hp1 e he w hw
  let F := givenReferenceBersMap hp hp1 hΓ e w hw ν M hM
  let G : (Fin (3*g-3) → ℂ) → (Fin (3*g-3) → ℂ) := fun z => W1 (F (W.symm z))
  have hF := (givenReferenceBersMap_analytic_bothDirections R R1 hg hgenus
    hΓ hΓ1 hp hp1 e w hw ν M hM).1
  have hG : AnalyticOnNhd ℂ G (range BC) := by
    rintro z ⟨a, rfl⟩
    have hm : W.symm (BC a) ∈ coefficientBersImage hΓ := by
      obtain ⟨μ, rfl⟩ := coefficientProjectionBall_surjective R hg hgenus
        hΓ (LiZhongQC.s27g_actsFreely hp) hp a
      change W.symm (bersCoordinates R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ (LiZhongQC.s27g_actsFreely hp) hp _) ∈ _
      rw [coefficientProjectionBall_coordinates, ContinuousLinearEquiv.symm_apply_apply]
      exact (mem_coefficientBersImage_iff_coefficient _ _).mpr ⟨μ, rfl⟩
    exact (W1.toContinuousLinearMap.analyticAt _).comp
      ((hF _ hm).comp (W.symm.toContinuousLinearMap.analyticAt (BC a)))
  have hBC : ContMDiff 𝓘(ℂ, Fin (3*g-3) → ℂ) 𝓘(ℂ, Fin (3*g-3) → ℂ) ω BC :=
    contMDiff_isOpenEmbedding
      (bersCoordinates_isOpenEmbedding R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ (LiZhongQC.s27g_actsFreely hp) hp)
  have hcomp : ContMDiff 𝓘(ℂ, Fin (3*g-3) → ℂ) 𝓘(ℂ, Fin (3*g-3) → ℂ) ω (G ∘ BC) :=
    hG.contDiffOn_of_completeSpace.contMDiffOn.comp_contMDiff hBC (fun a => mem_range_self a)
  have htarget : ContMDiff 𝓘(ℂ, Fin (3*g-3) → ℂ) 𝓘(ℂ, Fin (3*g-3) → ℂ) ω
      (BC1 ∘ referenceChangeEquiv R R1 hg hgenus hgenus1 e he) :=
    hcomp.congr (fun a => referenceChangeEquiv_bersCoordinates R R1 hg hgenus hgenus1
      e he hΓ hΓ1 hp hp1 w hw ν M hM a)
  exact htarget.of_comp_isOpenEmbedding
    (bersCoordinates_isOpenEmbedding R1 hg hgenus1 (canonicalHandleGroupPresentation g)
      hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1)

include w hw in
/-- The original given reference map and its actual inverse are holomorphic
on the entire original native quotients, for their existing global Bers atlases. -/
theorem referenceChangeEquiv_contMDiff_bothDirections :
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
    let : ChartedSpace (Fin (3*g-3) → ℂ) (TeichmullerSpace.{u,u} R) :=
      bersChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ (LiZhongQC.s27g_actsFreely hp) hp
    let : ChartedSpace (Fin (3*g-3) → ℂ) (TeichmullerSpace.{u,u} R1) :=
      bersChartedSpace R1 hg hgenus1 (canonicalHandleGroupPresentation g)
        hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
    ContMDiff 𝓘(ℂ, Fin (3*g-3) → ℂ) 𝓘(ℂ, Fin (3*g-3) → ℂ) ω
        (referenceChangeEquiv R R1 hg hgenus hgenus1 e he) ∧
      ContMDiff 𝓘(ℂ, Fin (3*g-3) → ℂ) 𝓘(ℂ, Fin (3*g-3) → ℂ) ω
        (referenceChangeEquiv R R1 hg hgenus hgenus1 e he).symm := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  let : TopologicalSpace (TeichmullerSpace.{u,u} R) :=
    bersTopology R hg hgenus (canonicalHandleGroupPresentation g) hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let : TopologicalSpace (TeichmullerSpace.{u,u} R1) :=
    bersTopology R1 hg hgenus1 (canonicalHandleGroupPresentation g) hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  let : ChartedSpace (Fin (3*g-3) → ℂ) (TeichmullerSpace.{u,u} R) :=
    bersChartedSpace R hg hgenus (canonicalHandleGroupPresentation g) hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let : ChartedSpace (Fin (3*g-3) → ℂ) (TeichmullerSpace.{u,u} R1) :=
    bersChartedSpace R1 hg hgenus1 (canonicalHandleGroupPresentation g) hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
  constructor
  · exact referenceChangeEquiv_contMDiff R R1 hg hgenus hgenus1 e he hΓ hΓ1 hp hp1 w hw
  · have hwi : LiZhongQC.IsLift p1 p e.symm w.symm := by
      intro τ
      have h := congrArg e.symm (hw (w.symm τ))
      simpa only [w.apply_symm_apply, e.symm_apply_apply] using h.symm
    have hback := referenceChangeEquiv_contMDiff R1 R hg hgenus1 hgenus e.symm
      (LiZhongQC.s28q_isQCRS_symm he) hΓ1 hΓ hp1 hp w.symm hwi
    exact hback.congr (fun b => referenceChangeEquiv_symm_apply R R1 hg hgenus hgenus1 e he b)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
