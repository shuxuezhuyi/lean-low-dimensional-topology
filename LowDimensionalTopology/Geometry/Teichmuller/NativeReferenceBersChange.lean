module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceBersEquiv
public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceCoefficientChange
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersTranslationGlobalInverseAnalytic

/-!
# The actual given-reference change on the entire Bers domains

The fixed normalized coefficient translation is followed by the literal
real Möbius identification with the original supplied target group. Both
actual coefficient and quadratic-differential realizations use the same
proved action correspondence, with no equality of matrix-lift groups assumed.
The resulting whole-domain equivalence commutes with the actual coefficient
projections. Its inverse is the original full inverse Bers translation after
the inverse real Möbius isometry.

Uses Wu Xiaobin's Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami BersWeighted

universe u
variable {A B : Type u}
    [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A]
    [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B]
    {Γ Γ1 : Subgroup Deck} {p : ℍ → A} {p1 : ℍ → B}
    (hp : LiZhongQC.IsUniformization Γ p) (hp1 : LiZhongQC.IsUniformization Γ1 p1)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hΓ1 : LiZhongQC.IsFuchsian Γ1)
    (e : A ≃ₜ B) (w : ℍ ≃ₜ ℍ) (hw : LiZhongQC.IsLift p p1 e w)
    (ν : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ)

omit [IsManifold 𝓘(ℂ) ω A] [IsManifold 𝓘(ℂ) ω B]

/-- Both genuine given-lift isometries commute with the full native projection,
for every deformed coefficient in the entire unit ball. -/
theorem givenLiftBersIsometry_projection (κ : Ball (deformedGroup hΓ ν)) :
    givenLiftBersIsometry hp hp1 hΓ e w hw ν M hM
        (automorphicProjection (deformedGroup_spec hΓ ν).1 κ.val) =
      automorphicProjection hΓ1
        (givenLiftCoefficientIsometry hp hp1 hΓ e w hw ν M hM κ.val) := by
  let i : Space (deformedGroup hΓ ν) ≃ₗᵢ[ℂ] Space (LiZhongQC.conjGroup Γ1 M) :=
    LinearIsometryEquiv.ofEq _ _
      (givenLift_compatibleSubmodule_eq hp hp1 hΓ e w hw ν M hM)
  let κM : Ball (LiZhongQC.conjGroup Γ1 M) := ⟨i κ.val, by
    rw [Metric.mem_ball, dist_zero_right, i.norm_map]
    exact Ball.norm_lt_one κ⟩
  have hsource :
      ((automorphicProjection (isFuchsian_realConjugate hΓ1 M) κM.val).toSource : ℂ → ℂ) =
      ((automorphicProjection (deformedGroup_spec hΓ ν).1 κ.val).toSource : ℂ → ℂ) := by
    rw [automorphicProjection_toSource_eq _ _ (Ball.norm_lt_one κM),
      automorphicProjection_toSource_eq _ _ (Ball.norm_lt_one κ)]
    rfl
  have hc := congrArg (fun q : Automorphic Γ1 => (q.toSource : ℂ → ℂ))
    (automorphicRealMobiusIsometry_projection hΓ1 M κM)
  rw [automorphicRealMobiusIsometry_toSource] at hc
  apply Automorphic.toSource_injective
  apply Subtype.ext
  rw [givenLiftBersIsometry_toSource]
  exact (congrArg (realMobiusPullback M) hsource.symm).trans hc

/-- The global coordinate map uses the original given-lift real normalization. -/
def givenReferenceBersMap (φ : Automorphic Γ) : Automorphic Γ1 :=
  givenLiftBersIsometry hp hp1 hΓ e w hw ν M hM (bersTranslation hΓ ν φ)

/-- The true complete inverse uses the same original full inverse translation. -/
def inverseGivenReferenceBersMap (ψ : Automorphic Γ1) : Automorphic Γ :=
  inverseBersTranslation hΓ ν ((givenLiftBersIsometry hp hp1 hΓ e w hw ν M hM).symm ψ)

/-- The entire actual coefficient projection square is retained literally in Bers coordinates. -/
theorem givenReferenceBersMap_projection (μ : Ball Γ) :
    givenReferenceBersMap hp hp1 hΓ e w hw ν M hM (automorphicProjection hΓ μ.val) =
      automorphicProjection hΓ1 (givenReferenceChangedBall hp hp1 hΓ e w hw ν M hM μ).val := by
  unfold givenReferenceBersMap
  rw [bersTranslation_automorphicProjection]
  exact givenLiftBersIsometry_projection hp hp1 hΓ hΓ1 e w hw ν M hM (translatedBall hΓ ν μ)

/-- Every coefficient of the supplied original target group is reached by the
same original full-ball reference change. -/
theorem givenReferenceChangedBall_surjective :
    Function.Surjective (givenReferenceChangedBall hp hp1 hΓ e w hw ν M hM) := by
  intro κ
  let i := givenLiftCoefficientIsometry hp hp1 hΓ e w hw ν M hM
  let κ0 : Ball (deformedGroup hΓ ν) := ⟨i.symm κ.val, by
    rw [Metric.mem_ball, dist_zero_right, i.symm.norm_map]
    exact Ball.norm_lt_one κ⟩
  refine ⟨pulledBackBall hΓ ν κ0, ?_⟩
  apply Subtype.ext
  change i (gammaTranslation hΓ ν (pulledBackBall hΓ ν κ0).val) = κ.val
  rw [gammaTranslation_pulledBackBall]
  exact i.apply_symm_apply κ.val

/-- The actual real Möbius identification maps the entire deformed Bers domain
onto the Bers domain of the original supplied target group. -/
theorem givenLiftBersIsometry_image :
    givenLiftBersIsometry hp hp1 hΓ e w hw ν M hM ''
      coefficientBersImage (deformedGroup_spec hΓ ν).1 = coefficientBersImage hΓ1 := by
  let i := givenLiftCoefficientIsometry hp hp1 hΓ e w hw ν M hM
  ext ψ
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨κ, rfl⟩ := (mem_coefficientBersImage_iff_coefficient _ φ).mp hφ
    let κ1 : Ball Γ1 := ⟨i κ.val, by
      rw [Metric.mem_ball, dist_zero_right, i.norm_map]
      exact Ball.norm_lt_one κ⟩
    apply (mem_coefficientBersImage_iff_coefficient hΓ1 _).mpr
    exact ⟨κ1, (givenLiftBersIsometry_projection hp hp1 hΓ hΓ1 e w hw ν M hM κ).symm⟩
  · intro hψ
    obtain ⟨κ1, rfl⟩ := (mem_coefficientBersImage_iff_coefficient hΓ1 ψ).mp hψ
    let κ : Ball (deformedGroup hΓ ν) := ⟨i.symm κ1.val, by
      rw [Metric.mem_ball, dist_zero_right, i.symm.norm_map]
      exact Ball.norm_lt_one κ1⟩
    refine ⟨automorphicProjection (deformedGroup_spec hΓ ν).1 κ.val, ?_, ?_⟩
    · exact (mem_coefficientBersImage_iff_coefficient _ _).mpr ⟨κ, rfl⟩
    · rw [givenLiftBersIsometry_projection]
      exact congrArg (automorphicProjection hΓ1) (i.apply_symm_apply κ1.val)

/-- The actual inverse isometry returns every original target-domain point
to the entire actual deformed Bers domain. -/
theorem givenLiftBersIsometry_symm_mem {ψ : Automorphic Γ1}
    (hψ : ψ ∈ coefficientBersImage hΓ1) :
    (givenLiftBersIsometry hp hp1 hΓ e w hw ν M hM).symm ψ ∈
      coefficientBersImage (deformedGroup_spec hΓ ν).1 := by
  have h : ψ ∈ givenLiftBersIsometry hp hp1 hΓ e w hw ν M hM ''
      coefficientBersImage (deformedGroup_spec hΓ ν).1 := by
    rw [givenLiftBersIsometry_image hp hp1 hΓ hΓ1 e w hw ν M hM]
    exact hψ
  obtain ⟨φ, hφ, heq⟩ := h
  rw [← heq, LinearIsometryEquiv.symm_apply_apply]
  exact hφ

/-- The isometric coordinate identification restricts to exactly the two full domains. -/
def givenLiftBersImageEquiv :
    coefficientBersImage (deformedGroup_spec hΓ ν).1 ≃ coefficientBersImage hΓ1 where
  toFun φ := ⟨givenLiftBersIsometry hp hp1 hΓ e w hw ν M hM φ.val, by
    rw [← givenLiftBersIsometry_image hp hp1 hΓ hΓ1 e w hw ν M hM]
    exact ⟨φ.val, φ.property, rfl⟩⟩
  invFun ψ := ⟨(givenLiftBersIsometry hp hp1 hΓ e w hw ν M hM).symm ψ.val,
    givenLiftBersIsometry_symm_mem hp hp1 hΓ hΓ1 e w hw ν M hM ψ.property⟩
  left_inv φ := Subtype.ext ((givenLiftBersIsometry hp hp1 hΓ e w hw ν M hM).symm_apply_apply φ.val)
  right_inv ψ := Subtype.ext ((givenLiftBersIsometry hp hp1 hΓ e w hw ν M hM).apply_symm_apply ψ.val)

/-- The original given-reference map is a genuine equivalence of the entire Bers domains. -/
def givenReferenceBersEquiv : coefficientBersImage hΓ ≃ coefficientBersImage hΓ1 :=
  (coefficientBersTranslationEquiv hΓ ν).trans
    (givenLiftBersImageEquiv hp hp1 hΓ hΓ1 e w hw ν M hM)

/-- Its forward map is exactly the actual coordinate map already identified with projection. -/
theorem givenReferenceBersEquiv_apply (φ : coefficientBersImage hΓ) :
    (givenReferenceBersEquiv hp hp1 hΓ hΓ1 e w hw ν M hM φ).val =
      givenReferenceBersMap hp hp1 hΓ e w hw ν M hM φ.val := by
  change givenLiftBersIsometry hp hp1 hΓ e w hw ν M hM
      (coefficientBersTranslationEquiv hΓ ν φ).val = _
  exact congrArg (givenLiftBersIsometry hp hp1 hΓ e w hw ν M hM)
    (coefficientBersTranslationEquiv_apply hΓ ν φ)

/-- Its inverse retains the literal full inverse translation after the actual inverse isometry. -/
theorem givenReferenceBersEquiv_symm_apply (ψ : coefficientBersImage hΓ1) :
    ((givenReferenceBersEquiv hp hp1 hΓ hΓ1 e w hw ν M hM).symm ψ).val =
      inverseGivenReferenceBersMap hp hp1 hΓ e w hw ν M hM ψ.val := by
  change ((coefficientBersTranslationEquiv hΓ ν).symm
    ((givenLiftBersImageEquiv hp hp1 hΓ hΓ1 e w hw ν M hM).symm ψ)).val = _
  exact (inverseBersTranslation_eq_equiv_symm hΓ ν
    ((givenLiftBersImageEquiv hp hp1 hΓ hΓ1 e w hw ν M hM).symm ψ)).symm

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami BersWeighted NormalizedCoefficientTransport

universe u
variable {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (R : ClosedRiemannSurface A) (R1 : ClosedRiemannSurface B)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ Γ1 : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) (hΓ1 : LiZhongQC.IsFuchsian Γ1)
    {p : ℍ → A} {p1 : ℍ → B}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (hp1 : let := R1.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ1 p1)
    (e : A ≃ₜ B) (w : ℍ ≃ₜ ℍ) (hw : LiZhongQC.IsLift p p1 e w)
    (ν : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ)

include hg hgenus in
/-- The actual given-reference coordinate equivalence and its literal inverse
are analytic at EVERY point of the two original complete Bers domains. -/
theorem givenReferenceBersMap_analytic_bothDirections :
    let := R.toRiemannAtlas.toChartedSpace
    let := R1.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R1.toRiemannAtlas.isManifold
    AnalyticOnNhd ℂ (givenReferenceBersMap hp hp1 hΓ e w hw ν M hM)
        (coefficientBersImage hΓ) ∧
      AnalyticOnNhd ℂ (inverseGivenReferenceBersMap hp hp1 hΓ e w hw ν M hM)
        (coefficientBersImage hΓ1) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  let E := givenLiftBersIsometry hp hp1 hΓ e w hw ν M hM
  have hforward := analyticOnNhd_bersTranslation_coefficientBersImage R hp hg hgenus hΓ ν
  have hinverse := analyticOnNhd_inverseBersTranslation_coefficientBersImage R hp hg hgenus hΓ ν
  constructor
  · intro φ hφ
    exact (E.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
      (hforward φ hφ)
  · intro ψ hψ
    have hm := givenLiftBersIsometry_symm_mem hp hp1 hΓ hΓ1 e w hw ν M hM hψ
    exact (hinverse _ hm).comp
      (E.symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt ψ)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
