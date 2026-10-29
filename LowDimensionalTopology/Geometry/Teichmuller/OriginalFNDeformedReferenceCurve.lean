module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNDeformedReferenceMarking
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistSameCanonicalGammaCurve
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistOriginalGammaHarmonicSeries
public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientRealMobiusNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientProjection

/-!
# The genuine coefficient tangent of the same rebased physical FN curve

The actual QC marking and its raw angular coefficient identify the existing
original unit curve after the actual deformed reference change. A single
whole angular direction supplies both its genuine weighted Bers derivative
and the literal harmonic endpoint series on that same deformed surface.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces Surfaces.HandlePresentation GammaMeasurableBeltrami
open NormalizedCoefficientTransport AngularTwist

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc)
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun x => Θ x j) = fun x => φ x j)
    (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      R hg hgenus hA hAlt D₀ φ Θ)
    (left : Fin (3 * g - 3) → Fin 2)

local notation "sigma" => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
  hU φ Θ hφ hΘ hRigid hRealize
local notation "Rebase" => Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
  R hp hg hgenus hΓ hfree hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left

variable (ν : Ball Γ)

local notation "Y" => deformedNativeSurface R hgenus hΓ hp ν
local notation "pY" => deformedTargetCover R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "eY" => deformedTargetMarking R hgenus hΓ hp ν
local notation "Δ" => deformedGroup hΓ ν
local notation "hΔ" => And.left (deformedGroup_spec hΓ ν)
local notation "hfY" => deformedNativeSurface_actsFreely R hgenus hΓ hp ν
local notation "hgY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν
local notation "a" => coefficientProjectionBall R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp ν
local notation "Aν" => deformedReferenceChangeEquiv R hp hg hgenus hΓ ν
local notation "hP" => canonicalHandleGroupPresentation g
local notation "BCY" => bersCoordinates Y hg hgY hP hΔ hfY hpY
local notation "WY" => weightedLinearBersCoordinates Y hg hgY hP hΔ hpY

/-- The same rebased physical unit curve has an actual coefficient direction
whose harmonic representative is its prescribed full-cuff endpoint series.
The geometric hypothesis supplies only the QC marking and raw coefficient. -/
theorem sameOriginalFN_deformedReference_curve_harmonic
    (hRebase : Rebase) (j : Fin (3 * g - 3))
    (A Q : Deck) (s : ℝ) (hs : 0 < s) (hAΔ : A ∈ Δ)
    (hcov : LiZhongQC.Covers pY A
      ⟨eY (D₀.cuff j).toLoop.1, (D₀.cuff j).toLoop.2.map (eY).continuous⟩)
    (hQA : Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))
    (hA0 : Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    (hsep :
      let ΔQ := (Δ).map (MulAut.conj Q).toMonoidHom
      ∀ ζ : ℂ,
        ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup ΔQ s)),
          rightCosetInfinitesimalZeroExtension (canonicalBandWidth s hs) ΔQ s u ζ ≠ 0 →
            rightCosetInfinitesimalZeroExtension (canonicalBandWidth s hs) ΔQ s v ζ ≠ 0 →
              u = v) :
    letI := (Y).toRiemannAtlas.toChartedSpace
    let := NormedSpace.restrictScalars ℝ ℂ (BersWeighted.Automorphic Δ)
    let := IsScalarTower.restrictScalars ℝ ℂ (BersWeighted.Automorphic Δ)
    let : ContinuousSMul ℝ (BersWeighted.Automorphic Δ) := IsScalarTower.continuousSMul ℂ
    ∃ η : Space Δ,
      HasDerivAt (fun t : ℝ => (WY).symm (BCY (Aν (sigma a j (left j) t))))
        (fderiv ℂ (BersWeighted.automorphicProjection hΔ) 0 η) 0 ∧
      ∀ (P : Fuchsian.HalfPlaneFuchsianGroup ((Δ).map Hyperbolic.realSLMobius))
        (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F),
        let CA := Quotient (QuotientGroup.rightRel
          (Subgroup.comap (Hyperbolic.realSLMobius.comp (Δ).subtype)
            (Subgroup.zpowers (Hyperbolic.realSLMobius A))))
        ∃ Ψ : HolomorphicQuadraticDifferential (Y).toRiemannAtlas,
          (∀ (ρ : CA → Δ), (∀ u : CA, Quotient.mk _ (ρ u) = u) →
            ∀ z : ℂ, z ∈ LiZhongQC.upperHalf →
              QuadraticBergman.uniformizedQuadratic Y pY Ψ z =
                GeodesicSeries.peterssonSeries Δ A hA0 ht ρ z) ∧
          NativePetersson.harmonicProjection Y P pY hpY F hF η =
            (-(Complex.I / (Real.pi : ℂ))) •
              NativeHarmonicBeltrami.ofQuadratic Y pY hpY Ψ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := (Y).toRiemannAtlas.toChartedSpace
  let := (Y).toRiemannAtlas.isManifold
  let := (Y).t2Space
  let := (Y).connectedSpace
  let := (Y).compactSpace
  let ΔQ := (Δ).map (MulAut.conj Q).toMonoidHom
  let pQ := LiZhongQC.adjustProjection pY Q
  let hpQ : LiZhongQC.IsUniformization ΔQ pQ :=
    LiZhongQC.adjustProjection_isUniformization hpY Q
  let hΔQ := LiZhongQC.utm_x_isFuchsian hpQ
  let : Countable ΔQ := (LiZhongQC.h36p_countable hΔQ).to_subtype
  let θ := canonicalBandWidth s hs
  obtain ⟨ηQ, hηQ, _hηQnorm⟩ := exists_rightCosetInfinitesimalSum_native θ ΔQ s hsep
  obtain ⟨_v, μP, _ε, _hv, _hvnorm, hμP, _hdecomp, _hε, _hzero, _hvar, _hderiv⟩ :=
    exists_rightCosetCoefficientSum_canonical_variation θ ΔQ s hsep
  obtain ⟨m, hmclass, hmcoeff⟩ := hRebase ν j A Q s hs hAΔ hcov hQA hsep
  let := NormedSpace.restrictScalars ℝ ℂ (Space ΔQ)
  let := NormedSpace.restrictScalars ℝ ℂ (Space Δ)
  let := NormedSpace.restrictScalars ℝ ℂ (BersWeighted.Automorphic ΔQ)
  let := NormedSpace.restrictScalars ℝ ℂ (BersWeighted.Automorphic Δ)
  let := IsScalarTower.restrictScalars ℝ ℂ (Space ΔQ)
  let := IsScalarTower.restrictScalars ℝ ℂ (Space Δ)
  let := IsScalarTower.restrictScalars ℝ ℂ (BersWeighted.Automorphic ΔQ)
  let := IsScalarTower.restrictScalars ℝ ℂ (BersWeighted.Automorphic Δ)
  let : ContinuousSMul ℝ (BersWeighted.Automorphic ΔQ) := IsScalarTower.continuousSMul ℂ
  let : ContinuousSMul ℝ (BersWeighted.Automorphic Δ) := IsScalarTower.continuousSMul ℂ
  obtain ⟨μQ, hsame, _hclass, hzero, hderiv, _hBcurve⟩ :=
    exists_same_canonical_gamma_curve θ ΔQ s hΔQ ηQ hηQ μP hμP
  let γ := fun t : ℝ => Aν (sigma a j (left j) t)
  have hraw (t : ℝ) : planeRepresentative (μQ t).val.val
      =ᵐ[volume.restrict LiZhongQC.upperHalf] rightCosetCoefficientSum θ ΔQ s t :=
    (hsame t).trans (ae_restrict_of_ae (hμP t))
  have hpointQ (t : ℝ) :
      coefficientProjectionBall Y hg hgY hP hΔQ (LiZhongQC.s27g_actsFreely hpQ)
        hpQ (μQ t) = γ t := by
    apply toSource_injective Y
    exact (coefficientProjectionBall_realization Y hg hgY hP hΔQ
      (LiZhongQC.s27g_actsFreely hpQ) hpQ (μQ t) (m t)
      ((hmcoeff t).trans (hraw t).symm)).trans (hmclass t)
  let I := coefficientRealMobiusIsometry Δ Q
  let μOriginal : ℝ → Ball Δ := fun t => coefficientRealMobiusBallEquiv Δ Q (μQ t)
  let η : Space Δ := I ηQ
  let IR : Space ΔQ →L[ℝ] Space Δ :=
    I.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have hOriginalZero : (μOriginal 0).val = 0 := by
    exact (congrArg I hzero).trans I.map_zero
  have hOriginalDeriv : HasDerivAt (fun t : ℝ => (μOriginal t).val) η 0 :=
    IR.hasFDerivAt.comp_hasDerivAt 0 hderiv
  have hOriginalPoint (t : ℝ) :
      coefficientProjectionBall Y hg hgY hP hΔ hfY hpY (μOriginal t) = γ t := by
    have h := coefficientProjectionBall_realMobius_conjugate Y hg hgY hΔ hpY Q (μOriginal t)
    have hball : (coefficientRealMobiusBallEquiv Δ Q).symm (μOriginal t) = μQ t :=
      (coefficientRealMobiusBallEquiv Δ Q).symm_apply_apply (μQ t)
    rw [hball] at h
    exact h.trans (hpointQ t)
  have hcoord (t : ℝ) : (WY).symm (BCY (γ t)) =
      BersWeighted.automorphicProjection hΔ (μOriginal t).val := by
    have hc := coefficientProjectionBall_coordinates Y hg hgY hP hΔ hfY hpY (μOriginal t)
    exact (congrArg (WY).symm ((congrArg BCY (hOriginalPoint t)).symm.trans hc)).trans
      ((WY).symm_apply_apply _)
  refine ⟨η, ?_, ?_⟩
  · have hB := (BersWeighted.hasFDerivAt_automorphicProjection hΔ).restrictScalars ℝ
    have hd := hB.comp_hasDerivAt_of_eq (0 : ℝ) hOriginalDeriv hOriginalZero.symm
    rw [BersWeighted.fderiv_automorphicProjection]
    exact hd.congr_of_eventuallyEq (Eventually.of_forall hcoord)
  · intro P F hF
    obtain ⟨Ψ, hΨ, hH, _hN⟩ :=
      givenAngularInfinitesimal_originalGamma_harmonic_series Y Δ hΔ pY hpY
        A hAΔ hA0 ht Q s hs hQA ηQ hηQ hsep P F hF
    refine ⟨Ψ, ?_, hH⟩
    intro ρ hρ z hz
    exact (hΨ ρ hρ z hz).1

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
