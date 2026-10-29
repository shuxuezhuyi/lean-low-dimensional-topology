module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMirrorLiftCoefficient
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMirrorUpperUniformization
public import LowDimensionalTopology.Geometry.Teichmuller.FixedBersMirrorCoefficient
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCCoefficientRealization
public import LowDimensionalTopology.Geometry.Teichmuller.CompactQCMetricTopologyTransport

/-!
# The same original mirror-class coefficient square

A prescribed coefficient supplies its actual chosen marked representative.
The original normalized-lift specification identifies that representative's
class. Literal lifted-coefficient covariance identifies its actual mirror.
Injectivity transfers only the marked class, never an arbitrary raw coefficient.
The existing given-J reference change is a separate direct consumer.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter MeasureTheory
open scoped Manifold ContDiff ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open Surfaces LiZhongQC TeichmullerSpace GammaMeasurableBeltrami BersWeighted

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)

/-- The existing actual normalized-lift law identifies this same original class. -/
theorem originalMirror_classOf_normalizedLift (μ : BeltramiGamma Γ) (m : ClosedMarked R)
    (Γ' : Subgroup Deck) (p' : UpperHalfPlane → m.target.carrier)
    (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (G : ExtPlane → ExtPlane)
    (hp' : IsUniformization Γ' p') (hN : IsNormalizedLift p p' m.marking F G)
    (hG : ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = ((fMuSym μ.val.val x : ℂ) : ExtPlane)) :
    closedGammaHomeomorph R hg hgenus hΓ hp (mk m) = Quotient.mk _ μ := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let E := sourceGammaEquiv R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ (s27g_actsFreely hp) hp
  have hspec := Classical.choose_spec (teichGamma_equiv_teichSpace hg
    (R.sourceHasGenus hgenus (canonicalHandleGroupPresentation g))
    hΓ (s27g_actsFreely hp) hp)
  have hclass : E (Quotient.mk _ μ) = Quot.mk _ (toClosedMarked R m) :=
    (hspec μ (toClosedMarked R m)).2 ⟨Γ', p', F, G, hp', hN, hG⟩
  change E.symm (toClosedSource R (mk m)) = Quotient.mk _ μ
  apply E.injective
  rw [E.apply_symm_apply]
  exact hclass.symm

/-- An actually supplied AE coefficient identity gives the same actual class. -/
theorem originalMirror_classOf_liftCoeff_ae (μ : BeltramiGamma Γ) (m : ClosedMarked R)
    (hμ : ∀ᵐ z ∂(volume.restrict upperHalf), s27u_liftCoeff p m.marking z = μ.val.val z) :
    closedGammaHomeomorph R hg hgenus hΓ hp (mk m) = Quotient.mk _ μ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨ν, hν, -⟩ := s27u_liftCoeff_beltramiH hp m.qc
  obtain ⟨k, hk0, hk1, hνk⟩ := bg_beltramiH_upper ν
  rw [hν] at hνk
  obtain ⟨k', hk0', hk1', hμk⟩ := bg_beltramiH_upper μ.val
  have hSym := s27u_fSym_congr_ae hk0 hk1 hνk hk0' hk1' hμk hμ
  obtain ⟨Γ', p', F, G, hp', hN, -, hG⟩ :=
    s27u_exists_uniformization hp (toClosedMarked R m)
  refine originalMirror_classOf_normalizedLift R hg hgenus hΓ hp μ m
    Γ' p' F G hp' hN ?_
  intro x
  rw [hG x]
  change ((s27u_fSym (s27u_liftCoeff p m.marking) x : ℂ) : ExtPlane) =
    ((fMuSym μ.val.val x : ℂ) : ExtPlane)
  exact congrArg (fun w : ℂ => (w : ExtPlane)) (congrFun hSym (x : ℂ))

/-- The exact closed mirror-class comparison uses only the original source data. -/
theorem originalMirroredClass_coefficientSquare :
    letI := R.toRiemannAtlas.toChartedSpace
    let hfree := s27g_actsFreely hp
    let E := bsu24_mirror_group hΓ hfree
    let Γσ := Classical.choose E
    let Eσ := Classical.choose_spec E
    let σ := Classical.choose Eσ
    let hs := Classical.choose_spec Eσ
    let hΓσ := hs.1
    let hσ := hs.2.2.1
    let hs₁ := hs.2.2.2.1
    let hs₂ := hs.2.2.2.2
    let RStar := originalMirrorNative R.toSourceClosedRS
    let pSigma : UpperHalfPlane → X := fun τ => p (σ τ)
    let hgenusStar := originalMirrorNative_hasGenus R hgenus
    let hpSigma := originalMirrorUpperCover_isUniformization
      R.toSourceClosedRS p hp σ hσ hs₁ hs₂
    let rho : BeltramiGamma Γ → BeltramiGamma Γσ := fixedBersReflectionGamma σ hσ hs₁
    let mSigma : ClosedMarked R → ClosedMarked RStar := originalMirroredClosedMarked R
    let HR : ClosedSpace R → TeichGamma Γ := closedGammaHomeomorph R hg hgenus hΓ hp
    let HStar : ClosedSpace RStar → TeichGamma Γσ :=
      closedGammaHomeomorph RStar hg hgenusStar hΓσ (p := pSigma) hpSigma
    ∀ (μ : BeltramiGamma Γ) (m : ClosedMarked R),
      HR (mk m) = Quotient.mk _ μ →
      HStar (mk (mSigma m)) = Quotient.mk _ (rho μ) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let hfree := s27g_actsFreely hp
  let E := bsu24_mirror_group hΓ hfree
  let Γσ := Classical.choose E
  let Eσ := Classical.choose_spec E
  let σ := Classical.choose Eσ
  let hs := Classical.choose_spec Eσ
  let hΓσ := hs.1
  let hσ := hs.2.2.1
  let hs₁ := hs.2.2.2.1
  let hs₂ := hs.2.2.2.2
  let RStar := originalMirrorNative R.toSourceClosedRS
  let pSigma : UpperHalfPlane → X := fun τ => p (σ τ)
  let hgenusStar := originalMirrorNative_hasGenus R hgenus
  let hpSigma := originalMirrorUpperCover_isUniformization
    R.toSourceClosedRS p hp σ hσ hs₁ hs₂
  let rho : BeltramiGamma Γ → BeltramiGamma Γσ := fixedBersReflectionGamma σ hσ hs₁
  let mSigma : ClosedMarked R → ClosedMarked RStar := originalMirroredClosedMarked R
  let HR : ClosedSpace R → TeichGamma Γ := closedGammaHomeomorph R hg hgenus hΓ hp
  let HStar : ClosedSpace RStar → TeichGamma Γσ :=
    closedGammaHomeomorph RStar hg hgenusStar hΓσ hpSigma
  change ∀ (μ : BeltramiGamma Γ) (m : ClosedMarked R),
    HR (mk m) = Quotient.mk _ μ → HStar (mk (mSigma m)) = Quotient.mk _ (rho μ)
  intro μ m hclass
  obtain ⟨k, hk0, hk1, hμ⟩ := bg_beltramiH_upper μ.val
  obtain ⟨mMu, F, _hF, hU, _hΓMu, _hfreeMu, hN, _hK, hAE⟩ :=
    exists_marked_of_compatible_coefficient
      (Surface.ofRiemannSurface R.toRiemannSurface) hp hk0 hk1 hμ μ.property
  have hMuClass : HR (mk mMu) = Quotient.mk _ μ := by
    exact originalMirror_classOf_normalizedLift R hg hgenus hΓ hp μ mMu
      (s27u_conjGroup Γ F) (s27u_proj p mMu.marking F) F
      (OnePoint.map (s27u_fSym μ.val.val)) hU hN (fun _ => rfl)
  let : TopologicalSpace (ClosedSpace R) :=
    distanceTopology (Surface.ofRiemannSurface R.toRiemannSurface)
  let : MetricSpace (TeichGamma Γ) :=
    gammaQCMetricSpace R hg hgenus hΓ (s27g_actsFreely hp) hp
  have hMarked : mk m = mk mMu :=
    (closedGammaHomeomorph R hg hgenus hΓ hp).injective (hclass.trans hMuClass.symm)
  have hAEStar : ∀ᵐ z ∂(volume.restrict upperHalf),
      s27u_liftCoeff pSigma (mSigma mMu).marking z = (rho μ).val.val z := by
    change ∀ᵐ z ∂(volume.restrict upperHalf),
      s27u_liftCoeff (fun τ => p (σ τ)) (originalMirroredClosedMarked R mMu).marking z =
        conj (μ.val.val (-conj z))
    exact originalMirroredClosedMarked_liftCoeff_ae R p hp.1.continuous σ hσ
      mMu μ.val.val hAE
  have hMuMirrorClass : HStar (mk (mSigma mMu)) = Quotient.mk _ (rho μ) :=
    originalMirror_classOf_liftCoeff_ae RStar hg hgenusStar hΓσ hpSigma
      (rho μ) (mSigma mMu) hAEStar
  have hMirrorMarked := congrArg (originalMirroredClass R) hMarked
  change mk (mSigma m) = mk (mSigma mMu) at hMirrorMarked
  exact (congrArg HStar hMirrorMarked).trans hMuMirrorClass

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
