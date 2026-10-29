module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceChange
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCClosedAtlasTransport
public import LowDimensionalTopology.Geometry.Teichmuller.NativeNonzeroTangentNaturality
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The actual reference-change differential at a normalized deformed surface

The map is the existing inverse-precomposition map on the full original
marked quotients. Its actual normalized lift gives the full coefficient
square. The same Bers coordinates, in the canonical quotient atlases, give
its actual manifold differential at every original marked point.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Surfaces

/-- The original normalized upper-half-plane equivalence, with the
continuity of the same genuine QC map and inverse. -/
def normalizedUpperHomeomorph {Γ : Subgroup Deck} (ν : Ball Γ) : ℍ ≃ₜ ℍ where
  toEquiv := normalizedUpperEquiv ν
  continuous_toFun := by
    obtain ⟨K, hK, _⟩ := normalizedMap_spec ν
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    exact (continuousOn_univ.mp hK.2.2.1.1).comp UpperHalfPlane.continuous_coe
  continuous_invFun := by
    obtain ⟨K, hK, _⟩ := normalizedInverse_spec ν
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    exact (continuousOn_univ.mp hK.2.2.1.1).comp UpperHalfPlane.continuous_coe

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hgenus : R.HasGenus g) (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)

/-- Repacking the actual target's complete atlas preserves QC of the actual
chosen marking; it does not assert equality of preferred chart choices. -/
theorem deformedTargetMarking_nativeQC :
    let := R.toRiemannAtlas.toChartedSpace
    let := (deformedNativeSurface R hgenus hΓ hp ν).toRiemannAtlas.toChartedSpace
    LiZhongQC.IsQCRS (deformedTargetMarking R hgenus hΓ hp ν) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  exact (GeneralQC.qc_target_toNative (deformedTargetSource R hgenus hΓ hp ν)
    (deformedTargetMarking R hgenus hΓ hp ν)
      ⟨_, (deformedTargetSource_spec R hgenus hΓ hp ν).1⟩).1

/-- The cover used by the actual deformed native surface has exactly the
original normalized homeomorphism as lift of its actual marking. -/
theorem deformedTargetMarking_normalized_isLift :
    LiZhongQC.IsLift p (deformedTargetCover R hgenus hΓ hp ν)
      (deformedTargetMarking R hgenus hΓ hp ν) (normalizedUpperHomeomorph ν) := by
  intro z
  change deformedTargetMarking R hgenus hΓ hp ν
      (p ((normalizedUpperEquiv ν).symm (normalizedUpperEquiv ν z))) =
    deformedTargetMarking R hgenus hΓ hp ν (p z)
  rw [Equiv.symm_apply_apply]

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open GammaMeasurableBeltrami NormalizedCoefficientTransport Surfaces

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ) (ν : Ball Γ)

local notation "Y" => deformedNativeSurface R hgenus hΓ hp ν
local notation "hY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "Δ" => deformedGroup hΓ ν
local notation "hΔ" => And.left (deformedGroup_spec hΓ ν)
local notation "hfY" => deformedNativeSurface_actsFreely R hgenus hΓ hp ν
local notation "E" => Fin (3 * g - 3) → ℂ
local notation "β" => coefficientProjection R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp
local notation "BC" => bersCoordinates R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp
local notation "BCY" => bersCoordinates Y hg hY
  (canonicalHandleGroupPresentation g) hΔ hfY hpY
local notation "W" => weightedLinearBersCoordinates R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hp
local notation "WY" => weightedLinearBersCoordinates Y hg hY
  (canonicalHandleGroupPresentation g) hΔ hpY

/-- The existing original reference change, specialized to the actual
normalized deformed target and the actual chosen marking. -/
def deformedReferenceChangeEquiv : TeichmullerSpace.{0,0} R ≃ TeichmullerSpace.{0,0} Y :=
  referenceChangeEquiv R Y hg hgenus hY (deformedTargetMarking R hgenus hΓ hp ν)
    (deformedTargetMarking_nativeQC R hp hgenus hΓ ν)

local notation "Aν" => deformedReferenceChangeEquiv R hp hg hgenus hΓ ν

/-- Every original coefficient is changed by the genuine normalized
translation, in the exact original and actual deformed native groups. -/
theorem deformedReferenceChangeEquiv_coefficientProjection (μ : Ball Γ) :
    Aν (coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp μ) =
      coefficientProjectionBall Y hg hY (canonicalHandleGroupPresentation g)
        hΔ hfY hpY (translatedBall hΓ ν μ) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := (Y).toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := (Y).toRiemannAtlas.isManifold
  let e := deformedTargetMarking R hgenus hΓ hp ν
  let w := normalizedUpperHomeomorph ν
  have hw := deformedTargetMarking_normalized_isLift R hp hgenus hΓ ν
  have hM : ∀ z : ℍ, normalizedUpperEquiv ν z = (1 : Deck) • w z := by
    intro z
    rw [one_smul]
    rfl
  have hc : givenReferenceChangedBall hp hpY hΓ e w hw ν 1 hM μ =
      translatedBall hΓ ν μ := by
    apply Subtype.ext
    apply Subtype.ext
    rw [givenReferenceChangedBall_val, GammaMeasurableBeltrami.pullback_one]
    rfl
  have h := referenceChangeEquiv_coefficientProjection R Y hg hgenus hY e
    (deformedTargetMarking_nativeQC R hp hgenus hΓ ν) hΓ hΔ hp hpY w hw ν 1 hM μ
  rw [hc] at h
  exact h

/-- The actual reference change has the full normalized Bers-coordinate
formula on every original marked point. -/
theorem deformedReferenceChangeEquiv_bersCoordinates (a : TeichmullerSpace.{0,0} R) :
    BCY (Aν a) = WY (bersTranslation hΓ ν ((W).symm (BC a))) := by
  obtain ⟨μ, rfl⟩ := coefficientProjectionBall_surjective R hg hgenus hΓ hfree hp a
  rw [deformedReferenceChangeEquiv_coefficientProjection R hp hg hgenus hΓ hfree ν μ,
    coefficientProjectionBall_coordinates, coefficientProjectionBall_coordinates,
    ContinuousLinearEquiv.symm_apply_apply]
  have hprojection :
      BersWeighted.automorphicProjection hΔ (translatedBall hΓ ν μ).val =
        bersTranslation hΓ ν (BersWeighted.automorphicProjection hΓ μ.val) :=
    (bersTranslation_automorphicProjection hΓ ν μ).symm
  exact congrArg (fun φ : BersWeighted.Automorphic Δ => WY φ) hprojection

/-- The actual normalized marked point maps to the identity marking of the
same actual target. This is the point equality used in the tangent comparison. -/
theorem deformedReferenceChangeEquiv_base : Aν (β ν.val) = basePoint Y := by
  rw [coefficientProjection_ball,
    deformedReferenceChangeEquiv_coefficientProjection R hp hg hgenus hΓ hfree ν ν]
  rw [← coefficientProjection_ball Y hg hY hΔ hfY hpY (translatedBall hΓ ν ν)]
  have hz : (translatedBall hΓ ν ν).val = 0 := by
    apply Subtype.ext
    exact translation_base ν
  rw [hz, coefficientProjection_zero]

private theorem deformedReference_sourceCoordinate_mem (a : TeichmullerSpace.{0,0} R) :
    (W).symm (BC a) ∈ coefficientBersImage hΓ := by
  obtain ⟨μ, rfl⟩ := coefficientProjectionBall_surjective R hg hgenus hΓ hfree hp a
  rw [coefficientProjectionBall_coordinates, ContinuousLinearEquiv.symm_apply_apply]
  exact (mem_coefficientBersImage_iff_coefficient hΓ _).mpr ⟨μ, rfl⟩

variable (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

/-- Holomorphy is in the canonical atlases on the original realized quotient
topologies used by the actual WP tangent fibres. -/
theorem deformedReferenceChangeEquiv_canonical_contMDiff :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    letI := canonicalComplexChartedSpace Y hg hY (canonicalHandleGroupPresentation g)
      hΔ hfY hpY hsmooth
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω Aν := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  let := canonicalComplexChartedSpace Y hg hY (canonicalHandleGroupPresentation g)
    hΔ hfY hpY hsmooth
  let G : E → E := fun z => WY (bersTranslation hΓ ν ((W).symm z))
  have hG : AnalyticOnNhd ℂ G (range BC) := by
    rintro z ⟨a, rfl⟩
    exact ((WY).toContinuousLinearMap.analyticAt _).comp
      (((analyticOnNhd_bersTranslation_coefficientBersImage R hp hg hgenus hΓ ν) _
        (deformedReference_sourceCoordinate_mem R hp hg hgenus hΓ hfree a)).comp
          ((W).symm.toContinuousLinearMap.analyticAt (BC a)))
  have hBC : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω BC :=
    contMDiff_isOpenEmbedding
      (canonicalBersCoordinates_isOpenEmbedding R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ hfree hp hsmooth)
  have hcomp : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (G ∘ BC) :=
    hG.contDiffOn_of_completeSpace.contMDiffOn.comp_contMDiff hBC (fun a => mem_range_self a)
  have htarget : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (BCY ∘ Aν) :=
    hcomp.congr (fun a => deformedReferenceChangeEquiv_bersCoordinates
      R hp hg hgenus hΓ hfree ν a)
  exact htarget.of_comp_isOpenEmbedding
    (canonicalBersCoordinates_isOpenEmbedding Y hg hY (canonicalHandleGroupPresentation g)
      hΔ hfY hpY hsmooth)

/-- In the actual canonical Bers tangent frames, the derivative of the
original reference map is the true derivative of its fixed Bers translation
at every original marked point. -/
theorem deformedReferenceChangeEquiv_mfderiv_bersCoordinates :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    letI := canonicalComplexChartedSpace Y hg hY (canonicalHandleGroupPresentation g)
      hΔ hfY hpY hsmooth
    ∀ (a : TeichmullerSpace.{0,0} R) (v : TangentSpace 𝓘(ℂ, E) a),
      canonicalBersTangentEquiv Y hg hY (canonicalHandleGroupPresentation g)
          hΔ hfY hpY hsmooth (Aν a) (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) Aν a v) =
        fderiv ℂ (bersTranslation hΓ ν) ((W).symm (BC a))
          (canonicalBersTangentEquiv R hg hgenus (canonicalHandleGroupPresentation g)
            hΓ hfree hp hsmooth a v) := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  let := canonicalComplexChartedSpace Y hg hY (canonicalHandleGroupPresentation g)
    hΔ hfY hpY hsmooth
  let : IsManifold 𝓘(ℂ, E) ω (TeichmullerSpace.{0,0} R) :=
    canonicalComplex_isManifold R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
  let : IsManifold 𝓘(ℂ, E) ω (TeichmullerSpace.{0,0} Y) :=
    canonicalComplex_isManifold Y hg hY (canonicalHandleGroupPresentation g)
      hΔ hfY hpY hsmooth
  intro a v
  let G : E → E := fun z => WY (bersTranslation hΓ ν ((W).symm z))
  have hχ := ((analyticOnNhd_bersTranslation_coefficientBersImage R hp hg hgenus hΓ ν) _
    (deformedReference_sourceCoordinate_mem R hp hg hgenus hΓ hfree a)).differentiableAt
  have hG : HasFDerivAt G
      (((WY).toContinuousLinearMap.comp (fderiv ℂ (bersTranslation hΓ ν) ((W).symm (BC a)))).comp
        (W).symm.toContinuousLinearMap) (BC a) :=
    ((WY).toContinuousLinearMap.hasFDerivAt.comp _ hχ.hasFDerivAt).comp _
      (W).symm.toContinuousLinearMap.hasFDerivAt
  have hBC : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) BC a :=
    (contMDiff_isOpenEmbedding (n := ω)
      (canonicalBersCoordinates_isOpenEmbedding R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ hfree hp hsmooth)).mdifferentiableAt (by simp)
  have hBCY : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) BCY (Aν a) :=
    (contMDiff_isOpenEmbedding (n := ω)
      (canonicalBersCoordinates_isOpenEmbedding Y hg hY (canonicalHandleGroupPresentation g)
        hΔ hfY hpY hsmooth)).mdifferentiableAt (by simp)
  have hA := (deformedReferenceChangeEquiv_canonical_contMDiff
    R hp hg hgenus hΓ hfree ν hsmooth).mdifferentiableAt (x := a) (by simp)
  have heq : BCY ∘ Aν = G ∘ BC :=
    funext (deformedReferenceChangeEquiv_bersCoordinates R hp hg hgenus hΓ hfree ν)
  have hleft := mfderiv_comp_apply a hBCY hA v
  have hright := mfderiv_comp_apply a hG.differentiableAt.mdifferentiableAt hBC v
  have hc := hleft.symm.trans
    ((congrArg (fun f => mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) f a v) heq).trans hright)
  rw [hG.hasMFDerivAt.mfderiv] at hc
  have hframeR := canonicalBersTangentEquiv_coordinate_apply R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth a v
  have hframeY := canonicalBersTangentEquiv_coordinate_apply Y hg hY
    (canonicalHandleGroupPresentation g) hΔ hfY hpY hsmooth (Aν a)
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) Aν a v)
  apply (WY).injective
  change WY _ = mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) BCY (Aν a)
    (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) Aν a v) at hframeY
  change W _ = mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) BC a v at hframeR
  exact hframeY.trans (hc.trans (by
    change WY (fderiv ℂ (bersTranslation hΓ ν) ((W).symm (BC a))
      ((W).symm (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) BC a v))) = _
    rw [← hframeR, ContinuousLinearEquiv.symm_apply_apply]))

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
