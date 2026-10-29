module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMirrorClassSquare
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMarkedReflection
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCReferenceChange
public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceGammaChange

/-!
# The same given-J class square

The original source-quotient reference change retains its inverse-precomposed
marking. Cancelling the existing native/source equivalences gives the same
referenceGammaEquiv on actual group classes. For e=J.symm its inverse is the
same J, so this operation is exactly the original reflected marking.
This class identity does not invoke analytic regularity or choose a new lift.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set
open scoped Manifold ContDiff ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open Surfaces LiZhongQC TeichmullerSpace GammaMeasurableBeltrami BersWeighted

/-- Existing reference-change equivalences retain the actual general marked class. -/
theorem originalMirror_referenceGamma_class
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (R0 : ClosedRiemannSurface A) (R1 : ClosedRiemannSurface B)
    {g : ℕ} (hg : 1 < g) (hgenus0 : R0.HasGenus g) (hgenus1 : R1.HasGenus g)
    (e : A ≃ₜ B)
    (he : @IsQCRS A inferInstance R0.toRiemannAtlas.toChartedSpace
      B inferInstance R1.toRiemannAtlas.toChartedSpace e)
    {Γ0 Γ1 : Subgroup Deck} (hΓ0 : IsFuchsian Γ0) (hΓ1 : IsFuchsian Γ1)
    {p0 : UpperHalfPlane → A} {p1 : UpperHalfPlane → B}
    (hp0 : letI := R0.toRiemannAtlas.toChartedSpace; IsUniformization Γ0 p0)
    (hp1 : letI := R1.toRiemannAtlas.toChartedSpace; IsUniformization Γ1 p1)
    (m : ClosedMarked R0) :
    closedGammaHomeomorph R1 hg hgenus1 hΓ1 hp1
      (mk (referenceMarked
        (R := Surface.ofRiemannSurface R0.toRiemannSurface)
        (R1 := Surface.ofRiemannSurface R1.toRiemannSurface) e he m)) =
      referenceGammaEquiv R0 R1 hg hgenus0 hgenus1 e he hΓ0 hΓ1 hp0 hp1
        (closedGammaHomeomorph R0 hg hgenus0 hΓ0 hp0 (mk m)) := by
  let := R0.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R0.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  let E0 := sourceGammaEquiv R0 hg hgenus0 (canonicalHandleGroupPresentation g)
    hΓ0 (s27g_actsFreely hp0) hp0
  let E1 := sourceGammaEquiv R1 hg hgenus1 (canonicalHandleGroupPresentation g)
    hΓ1 (s27g_actsFreely hp1) hp1
  let N0 := sourceEquiv R0 hg hgenus0 (canonicalHandleGroupPresentation g)
  let N1 := sourceEquiv R1 hg hgenus1 (canonicalHandleGroupPresentation g)
  have hMarked : toClosedSource R1 (mk (referenceMarked e he m)) =
      SourceReferenceChange.quotientMap e he (toClosedSource R0 (mk m)) := by
    rfl
  change E1.symm (toClosedSource R1 (mk (referenceMarked e he m))) =
    E1.symm (N1 (N1.symm (SourceReferenceChange.quotientMap e he
      (N0 (N0.symm (E0 (E0.symm (toClosedSource R0 (mk m)))))))))
  rw [E0.apply_symm_apply, N0.apply_symm_apply, N1.apply_symm_apply, hMarked]

/-- The same inverse J is QC from the actual native mirror reference back to R. -/
theorem originalMirror_referenceInverse_isQCRS {X : Type} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) (J : X ≃ₜ X)
    (hJ : @IsAnticonformalInvolution X inferInstance R.toRiemannAtlas.toChartedSpace J) :
    @IsQCRS X inferInstance (originalMirrorNative R.toSourceClosedRS).toRiemannAtlas.toChartedSpace
      X inferInstance R.toRiemannAtlas.toChartedSpace J.symm := by
  let A := R.toSourceClosedRS
  have hJnative : @IsQCRS X inferInstance A.chartedSpace
      X inferInstance (originalMirrorNative A).toRiemannAtlas.toChartedSpace J :=
    (@qc_target_toNative X inferInstance A.chartedSpace A.isManifold
      (originalMirrorClosedRS A) J
      ⟨1, originalInvolution_isKQCRS_toMirror A J hJ⟩).1
  exact @s28q_isQCRS_symm X X inferInstance A.chartedSpace
    inferInstance (originalMirrorNative A).toRiemannAtlas.toChartedSpace J hJnative

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (J : X ≃ₜ X)
    (hJ : @IsAnticonformalInvolution X inferInstance R.toRiemannAtlas.toChartedSpace J)

/-- The SAME given J has the exact original marked/group coefficient square. -/
theorem originalTeichmullerReflection_coefficientSquare :
    letI := R.toRiemannAtlas.toChartedSpace
    let E := bsu24_mirror_group hΓ (s27g_actsFreely hp)
    let Γσ := Classical.choose E
    let Eσ := Classical.choose_spec E
    let σ := Classical.choose Eσ
    let hs := Classical.choose_spec Eσ
    let RStar := originalMirrorNative R.toSourceClosedRS
    let hgenusStar := originalMirrorNative_hasGenus R hgenus
    let hpSigma := originalMirrorUpperCover_isUniformization
      R.toSourceClosedRS p hp σ hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
    let rho : BeltramiGamma Γ → BeltramiGamma Γσ :=
      fixedBersReflectionGamma σ hs.2.2.1 hs.2.2.2.1
    let HR : ClosedSpace R → TeichGamma Γ := closedGammaHomeomorph R hg hgenus hΓ hp
    let heJ := originalMirror_referenceInverse_isQCRS R J hJ
    let RefJ := referenceGammaEquiv RStar R hg hgenusStar hgenus
      J.symm heJ hs.1 hΓ hpSigma hp
    ∀ (μ : BeltramiGamma Γ) (m : ClosedMarked R),
      HR (mk m) = Quotient.mk _ μ →
      HR (originalTeichmullerReflection R J hJ (mk m)) = RefJ (Quotient.mk _ (rho μ)) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let E := bsu24_mirror_group hΓ (s27g_actsFreely hp)
  let Γσ := Classical.choose E
  let Eσ := Classical.choose_spec E
  let σ := Classical.choose Eσ
  let hs := Classical.choose_spec Eσ
  let RStar := originalMirrorNative R.toSourceClosedRS
  let hgenusStar := originalMirrorNative_hasGenus R hgenus
  let hpSigma := originalMirrorUpperCover_isUniformization
    R.toSourceClosedRS p hp σ hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  let rho : BeltramiGamma Γ → BeltramiGamma Γσ :=
    fixedBersReflectionGamma σ hs.2.2.1 hs.2.2.2.1
  let HR : ClosedSpace R → TeichGamma Γ := closedGammaHomeomorph R hg hgenus hΓ hp
  let HStar : ClosedSpace RStar → TeichGamma Γσ :=
    closedGammaHomeomorph RStar hg hgenusStar hs.1 hpSigma
  let heJ := originalMirror_referenceInverse_isQCRS R J hJ
  let RefJ := referenceGammaEquiv RStar R hg hgenusStar hgenus
    J.symm heJ hs.1 hΓ hpSigma hp
  change ∀ (μ : BeltramiGamma Γ) (m : ClosedMarked R),
    HR (mk m) = Quotient.mk _ μ →
    HR (originalTeichmullerReflection R J hJ (mk m)) = RefJ (Quotient.mk _ (rho μ))
  intro μ m hclass
  have hStar := originalMirroredClass_coefficientSquare R hg hgenus hΓ hp μ m hclass
  change HStar (mk (originalMirroredClosedMarked R m)) = Quotient.mk _ (rho μ) at hStar
  have hNatural := originalMirror_referenceGamma_class RStar R hg hgenusStar hgenus
    J.symm heJ hs.1 hΓ hpSigma hp (originalMirroredClosedMarked R m)
  change HR (originalTeichmullerReflection R J hJ (mk m)) =
    RefJ (HStar (mk (originalMirroredClosedMarked R m))) at hNatural
  rw [hStar] at hNatural
  exact hNatural

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
