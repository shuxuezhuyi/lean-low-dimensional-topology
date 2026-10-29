module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceReferenceChangeLifts
public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceCoefficientChange
public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientProjection

/-!
# The actual given reference change commutes with coefficient projection

The map on original marked quotients is inverse precomposition by the given
quasiconformal homeomorphism. Its actual given lift is normalized by the
proved real Möbius factor. For every original coefficient, the changed
marking's lift is the normalized translated lift followed by that same real
Möbius map. Its actual lifted coefficient is precisely the source Möbius
pullback of the translated coefficient. Thus the original marked-quotient
map commutes with the genuine native coefficient projections on the entire
unit ball. No desired quotient square is supplied as an assumption.

The original lifted-coefficient and uniformization APIs reuse Wu Xiaobin's
Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.SourceReferenceChange

open GammaMeasurableBeltrami NormalizedCoefficientTransport

universe u
variable {A B : Type u}
    [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A]
    [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B]
    (e : A ≃ₜ B) (he : LiZhongQC.IsQCRS e)
    {p : ℍ → A} {p1 : ℍ → B} (w : ℍ ≃ₜ ℍ)
    (hw : LiZhongQC.IsLift p p1 e w)

/-- Returning from the normalized target cover to the supplied target cover
precomposes the actual translated lift by the same real Möbius map. -/
theorem marked_original_lift_translated_formula {Γ : Subgroup Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ)
    (F : ℍ ≃ₜ ℍ) (hFμ : ∀ τ : ℍ, F τ = normalizedUpperEquiv μ τ) (τ : ℍ) :
    ((w.symm.trans F) τ : ℂ) =
      LiZhongQC.fMuSym (translatedSource hΓ ν μ).val.val (M • τ : ℍ) := by
  have hi : (normalizedGivenLift w M).symm (M • τ) = w.symm τ := by
    apply (normalizedGivenLift w M).injective
    change (normalizedGivenLift w M) ((normalizedGivenLift w M).symm (M • τ)) =
      M • w (w.symm τ)
    rw [Homeomorph.apply_symm_apply, w.apply_symm_apply]
  have h := marked_adjusted_lift_translated_solution w hΓ ν μ M hM F hFμ (M • τ)
  change (F ((normalizedGivenLift w M).symm (M • τ)) : ℂ) = _ at h
  rw [hi] at h
  exact h

include hw in
/-- The actual changed marking's lifted coefficient is the literal source
Möbius pullback, at every original upper-plane point. -/
theorem marked_liftCoeff_eq_mobiusTranslated
    {Γ Γ1 : Subgroup Deck} (hp1 : LiZhongQC.IsUniformization Γ1 p1)
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ)
    (m : LiZhongQC.MarkedRS A) {G : Subgroup Deck} {pS : ℍ → m.X.carrier}
    (hpS : LiZhongQC.IsUniformization G pS) (F : ℍ ≃ₜ ℍ)
    (hF : LiZhongQC.IsLift p pS m.marking F)
    (hFμ : ∀ τ : ℍ, F τ = normalizedUpperEquiv μ τ) :
    EqOn (LiZhongQC.s27u_liftCoeff p1 (marked e he m).marking)
      (LiZhongQC.b33_e_pb (translatedSource hΓ ν μ).val M).val LiZhongQC.upperHalf := by
  have hL := marked_isLift e he w hw m F hF
  have hEq : EqOn (LiZhongQC.liftToC (w.symm.trans F))
      (LiZhongQC.fMuSym (translatedSource hΓ ν μ).val.val ∘
        LiZhongQC.mobiusFn (M 0 0) (M 0 1) (M 1 0) (M 1 1)) LiZhongQC.upperHalf := by
    intro z hz
    rw [LiZhongQC.h23l_liftToC_eq _ hz,
      UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    simpa only [Function.comp_apply, LiZhongQC.h23l_b_coe_smul, LiZhongQC.mobiusFn] using
      marked_original_lift_translated_formula w hΓ ν μ M hM F hFμ (⟨z, hz⟩ : ℍ)
  intro z hz
  refine (LiZhongQC.s27u_liftCoeff_eq_dilatation hp1 hpS hL hz).symm.trans ?_
  change LiZhongQC.complexDilatation (LiZhongQC.liftToC (w.symm.trans F)) z =
    LiZhongQC.upperHalf.indicator
      (LiZhongQC.complexDilatation
        (LiZhongQC.fMuSym (translatedSource hΓ ν μ).val.val ∘
          LiZhongQC.mobiusFn (M 0 0) (M 0 1) (M 1 0) (M 1 1))) z
  exact (LiZhongQC.abR_t_complexDilatation_congr LiZhongQC.isOpen_upperHalf hEq hz).trans
    (indicator_of_mem hz _).symm

end LowDimensionalTopology.Geometry.Teichmuller.SourceReferenceChange

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

universe u
variable {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (R : ClosedRiemannSurface A) (R1 : ClosedRiemannSurface B)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hgenus1 : R1.HasGenus g)
    {Γ Γ1 : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) (hΓ1 : LiZhongQC.IsFuchsian Γ1)
    {p : ℍ → A} {p1 : ℍ → B}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (hp1 : let := R1.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ1 p1)
    (e : A ≃ₜ B)
    (he : let := R.toRiemannAtlas.toChartedSpace
      let := R1.toRiemannAtlas.toChartedSpace; LiZhongQC.IsQCRS e)
    (w : ℍ ≃ₜ ℍ) (hw : LiZhongQC.IsLift p p1 e w)
    (ν : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ)

/-- The original source marked-quotient reference map commutes with the
actual coefficient projection at EVERY original coefficient in the full ball. -/
theorem source_referenceChange_coefficientProjection (μ : Ball Γ) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R1.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R1.toRiemannAtlas.isManifold
    SourceReferenceChange.quotientMap e he
      (toSource R (coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ (LiZhongQC.s27g_actsFreely hp) hp μ)) =
      toSource R1 (coefficientProjectionBall R1 hg hgenus1
        (canonicalHandleGroupPresentation g) hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
          (givenReferenceChangedBall hp hp1 hΓ e w hw ν M hM μ)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  obtain ⟨m, _, hm, hq⟩ := exists_coefficientProjectionBall_realization R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ (LiZhongQC.s27g_actsFreely hp) hp μ
  obtain ⟨F, hF, hpS, hN, _, _⟩ :=
    LiZhongQC.s27u_uniformization_transport hp m.marking m.qc
  obtain ⟨k, hk0, hk1, hmbound⟩ := LiZhongQC.s27v_liftCoeff_bound hp m
  have hsym := LiZhongQC.s27u_fSym_congr_ae hk0 hk1 hmbound
    (norm_nonneg μ.val.val) (Ball.norm_lt_one μ)
    (planeRepresentative_isBeltramiCoeff μ.val.val) hm
  have hFμ : ∀ τ : ℍ, F τ = normalizedUpperEquiv μ τ := by
    intro τ
    apply UpperHalfPlane.ext
    change (F τ : ℂ) = LiZhongQC.fMuSym (planeRepresentative μ.val.val) τ
    rw [← LiZhongQC.s33v_fSym_eq]
    exact (hF τ).trans (congrFun hsym (τ : ℂ))
  have hc := SourceReferenceChange.marked_liftCoeff_eq_mobiusTranslated e he w hw
    hp1 hΓ ν μ M hM m hpS F hN.1 hFμ
  have hm1 : LiZhongQC.s27u_liftCoeff p1 (SourceReferenceChange.marked e he m).marking
      =ᵐ[volume.restrict LiZhongQC.upperHalf]
        planeRepresentative (givenReferenceChangedBall hp hp1 hΓ e w hw ν M hM μ).val.val := by
    filter_upwards [givenReferenceChangedBall_source_ae hp hp1 hΓ e w hw ν M hM μ,
      ae_restrict_mem LiZhongQC.isOpen_upperHalf.measurableSet] with z hz hzU
    exact (hc hzU).trans hz.symm
  have htarget := coefficientProjectionBall_realization R1 hg hgenus1
    (canonicalHandleGroupPresentation g) hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
      (givenReferenceChangedBall hp hp1 hΓ e w hw ν M hM μ)
      (SourceReferenceChange.marked e he m) hm1
  exact (congrArg (SourceReferenceChange.quotientMap e he) hq).trans
    ((SourceReferenceChange.quotientMap_mk e he m).trans htarget.symm)

/-- The normalizer and the entire projection square are derived from the
original reference homeomorphism and its actual given lift. -/
theorem exists_source_referenceChange_coefficientProjection :
    let := R.toRiemannAtlas.toChartedSpace
    let := R1.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R1.toRiemannAtlas.isManifold
    ∃ (ν : Ball Γ) (M : Deck)
      (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ),
      (planeRepresentative ν.val.val =ᵐ[volume.restrict LiZhongQC.upperHalf]
        LiZhongQC.s27u_liftCoeff p e) ∧
      ∀ μ : Ball Γ,
        SourceReferenceChange.quotientMap e he
          (toSource R (coefficientProjectionBall R hg hgenus
            (canonicalHandleGroupPresentation g) hΓ (LiZhongQC.s27g_actsFreely hp) hp μ)) =
          toSource R1 (coefficientProjectionBall R1 hg hgenus1
            (canonicalHandleGroupPresentation g) hΓ1 (LiZhongQC.s27g_actsFreely hp1) hp1
              (givenReferenceChangedBall hp hp1 hΓ e w hw ν M hM μ)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  obtain ⟨ν, M, hν, hM, _⟩ :=
    exists_native_normalization_of_given_lift hp hp1 e he w hw
  exact ⟨ν, M, hM, hν, fun μ => source_referenceChange_coefficientProjection R R1
    hg hgenus hgenus1 hΓ hΓ1 hp hp1 e he w hw ν M hM μ⟩

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
