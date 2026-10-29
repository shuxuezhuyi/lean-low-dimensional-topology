module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizerModularIsometry
public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceBetaChange
public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceChangeProjection
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# The original Fuchsian modular action and its normalized composition

The arbitrary QC normalizer, its derived real base normalization and the real
postnormalizer are distinct. The same changed coefficient supplies the actual
upper composition, original quotient action, true Bers diagram and normalized
sphere homeomorphism. Uses the credited LiZhongQC APIs, Apache-2.0, pinned at
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
open GammaMeasurableBeltrami
universe u
/-- The actual given lift has a real postnormalizer for any specified native
coefficient representing that same marking, with its original normalization. -/
theorem givenLift_sameCoefficient_real_normalizer
    {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {Γ Γ1 : Subgroup Deck} {p : ℍ → X} {p1 : ℍ → Y}
    (hp : LiZhongQC.IsUniformization Γ p) (hp1 : LiZhongQC.IsUniformization Γ1 p1)
    (f : X ≃ₜ Y) (hf : LiZhongQC.IsQCRS f) (w : ℍ ≃ₜ ℍ)
    (hw : LiZhongQC.IsLift p p1 f w) (μnew : Ball Γ)
    (hμnew : planeRepresentative μnew.val.val =ᵐ[volume.restrict LiZhongQC.upperHalf]
      LiZhongQC.s27u_liftCoeff p f) :
    ∃ α : Deck, (∀ τ : ℍ, normalizedUpperEquiv μnew τ = α • w τ) ∧
      normalizedMap μnew 0 = 0 ∧ normalizedMap μnew 1 = 1 := by
  obtain ⟨ν, α, hν, hα, _⟩ := exists_native_normalization_of_given_lift hp hp1 f hf w hw
  have hl : ‖μnew.val.val‖ < 1 := by rw [ClosedSubmodule.norm_coe]; exact Ball.norm_lt_one μnew
  have hn : ‖ν.val.val‖ < 1 := by rw [ClosedSubmodule.norm_coe]; exact Ball.norm_lt_one ν
  have he := LiZhongQC.s27u_fSym_congr_ae (norm_nonneg μnew.val.val) hl
    (planeRepresentative_isBeltramiCoeff μnew.val.val) (norm_nonneg ν.val.val) hn
    (planeRepresentative_isBeltramiCoeff ν.val.val) (hμnew.trans hν.symm)
  have hm : normalizedMap μnew = normalizedMap ν := by
    simpa only [normalizedMap, LiZhongQC.s33v_fSym_eq] using he
  refine ⟨α, ?_, (normalizedMap_spec μnew).choose_spec.2.2.1,
    (normalizedMap_spec μnew).choose_spec.2.2.2.1⟩
  intro τ
  apply UpperHalfPlane.ext
  simpa only [normalizedUpperEquiv_coe, hm] using
    congrArg (fun z : ℍ => (z : ℂ)) (hα τ)
end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport


namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport RawBersQuotient

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

/-- Every original normalizer acts by the same genuinely normalized composition,
on the original quotient and its entire true Bers image. -/
theorem exists_upperModularRepresentation_normalizedFormula :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    ∀ w : QCNormalizerModular.Normalizer hp,
      let f := QCNormalizerModular.descendedAut hp w.val w.property
      let hw := QCNormalizerModular.descendedAut_isLift hp w.val w.property
      ∃ (ν : Ball Γ) (M : Deck)
        (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w.val τ),
        (∀ a : TeichBeta Γ,
          betaWeightedBersEmbedding R hg hgenus hΓ hp
              (referenceBetaEquiv R R hg hgenus hgenus f.val f.property hΓ hΓ hp hp a) =
            givenReferenceBersMap hp hp hΓ f.val w.val hw ν M hM
              (betaWeightedBersEmbedding R hg hgenus hΓ hp a)) ∧
        ∀ μ : Ball Γ,
          let μnew := givenReferenceChangedBall hp hp hΓ f.val w.val hw ν M hM μ
          upperModularRepresentation R hg hgenus hΓ hp (QCNormalizerModular.mk hp w)
              (Quotient.mk _ (toSourceGamma μ)) = Quotient.mk _ (toSourceGamma μnew) ∧
          referenceBetaEquiv R R hg hgenus hgenus f.val f.property hΓ hΓ hp hp
              (Quotient.mk _ (toSourceGamma μ)) = Quotient.mk _ (toSourceGamma μnew) ∧
          ∃ (α : Deck) (E : ℂ ≃ₜ ℂ),
            (∀ τ : ℍ, normalizedUpperEquiv μnew τ =
              α • normalizedUpperEquiv μ (w.val.symm τ)) ∧
            (⇑E = normalizedMap μnew) ∧
            E.onePointCongr (OnePoint.infty : OnePoint ℂ) = OnePoint.infty ∧
            E.onePointCongr ((0 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) ∧
            E.onePointCongr ((1 : ℂ) : OnePoint ℂ) = ((1 : ℂ) : OnePoint ℂ) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  intro w
  let f := QCNormalizerModular.descendedAut hp w.val w.property
  let hw := QCNormalizerModular.descendedAut_isLift hp w.val w.property
  obtain ⟨ν, M, hM, hAction⟩ :=
    exists_upperModularRepresentation_coefficientFormula R hg hgenus hΓ hp w
  refine ⟨ν, M, hM, ?_, ?_⟩
  · intro a
    exact referenceBetaEquiv_bersDiagram R R hg hgenus hgenus f.val f.property
      hΓ hΓ hp hp w.val hw ν M hM a
  · intro μ
    let μnew := givenReferenceChangedBall hp hp hΓ f.val w.val hw ν M hM μ
    refine ⟨hAction μ, ?_, ?_⟩
    · exact referenceBetaEquiv_coefficientProjection R R hg hgenus hgenus f.val f.property
        hΓ hΓ hp hp w.val hw ν M hM μ
    · obtain ⟨m, _, hm, _⟩ := exists_coefficientProjectionBall_realization R hg hgenus
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
      have hc := SourceReferenceChange.marked_liftCoeff_eq_mobiusTranslated
        f.val f.property w.val hw hp hΓ ν μ M hM m hpS F hN.1 hFμ
      have hμnew : planeRepresentative μnew.val.val =ᵐ[volume.restrict LiZhongQC.upperHalf]
          LiZhongQC.s27u_liftCoeff p (SourceReferenceChange.marked f.val f.property m).marking := by
        filter_upwards [givenReferenceChangedBall_source_ae hp hp hΓ f.val w.val hw ν M hM μ,
          ae_restrict_mem LiZhongQC.isOpen_upperHalf.measurableSet] with z hz hzU
        exact hz.trans (hc hzU).symm
      obtain ⟨α, hα, h0, h1⟩ := givenLift_sameCoefficient_real_normalizer hp hpS
        (SourceReferenceChange.marked f.val f.property m).marking
        (SourceReferenceChange.marked f.val f.property m).qc (w.val.symm.trans F)
        (SourceReferenceChange.marked_isLift f.val f.property w.val hw m F hN.1) μnew hμnew
      obtain ⟨K, hK, hs, _, _, _, _, _⟩ := normalizedMap_spec μnew
      obtain ⟨E, hE⟩ := LiZhongQC.t1_homeomorph hK hs
      refine ⟨α, E, ?_, hE, rfl, ?_, ?_⟩
      · intro τ
        simpa only [Homeomorph.trans_apply, hFμ] using hα τ
      · change ((E 0 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ)
        exact congrArg (fun z : ℂ => (z : OnePoint ℂ)) ((congrFun hE 0).trans h0)
      · change ((E 1 : ℂ) : OnePoint ℂ) = ((1 : ℂ) : OnePoint ℂ)
        exact congrArg (fun z : ℂ => (z : OnePoint ℂ)) ((congrFun hE 1).trans h1)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
