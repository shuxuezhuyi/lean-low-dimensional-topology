module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistOriginalGeodesicSameCurve
public import LowDimensionalTopology.Geometry.Teichmuller.ArbitraryOriginalGeodesicSignedFN
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCanonicalCoefficientCurve
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistNativeInfinitesimal

/-!
# The signed FN series of one prescribed original geodesic

One complete reference cuff equals the prescribed original geodesic. Its
normalizer, compatible whole direction and full-plane coefficient family
are chosen once, and the same signed marked curve gives both the original
Bers derivative and the original harmonic representative.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped unitInterval UpperHalfPlane ComplexConjugate Topology
namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
open Surfaces Surfaces.HandlePresentation GammaMeasurableBeltrami
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- A prescribed original simple geodesic has one signed FN coefficient
curve whose original Bers derivative and harmonic class are its literal
full-period Petersson series under the explicit geometric FN inputs. -/
theorem originalGeodesic_exists_same_signedFN_original_series
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface}
    (q : OriginalClosedGeodesic M)
    (hcircle : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X))
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (hReference : Unproved.Teichmuller.OriginalFNReferenceContainingGeodesic R g M q) :
    ∃ (inc : OriginalFNCuffIncidence g) (D0 : OriginalFNRealization M inc)
      (j : Fin (3 * g - 3)) (hC : D0.cuff j = q),
      ∃ (A Q : Deck) (s : ℝ) (hs : 0 < s) (hAΓ : A ∈ Γ)
        (hcov : LiZhongQC.Covers M.halfPlaneCover A q.toLoop)
        (hQA : Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
          Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s)),
        let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
        let θ := canonicalBandWidth s hs
        ∃ ν : Space ΓQ,
          ((ν.val : ℍ → ℂ) =ᵐ[volume]
            (fun z : ℍ => rightCosetInfinitesimalSum θ ΓQ s (z : ℂ))) ∧
          ‖ν‖ ≤ 1 / (4 * (θ : ℝ)) ∧
          ∃ μP : ℝ → MeasurableBeltramiBall,
            (∀ t : ℝ, ((μP t).val : ℂ → ℂ) =ᵐ[volume]
              rightCosetCoefficientSum θ ΓQ s t) ∧
            (∀ ζ : ℂ,
              ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup ΓQ s)),
                rightCosetInfinitesimalZeroExtension θ ΓQ s u ζ ≠ 0 →
                rightCosetInfinitesimalZeroExtension θ ΓQ s v ζ ≠ 0 → u = v) ∧
            ∀
              (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D0)
              (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
              (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
              (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
                (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
                (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D0 m D)
                (j : Fin (3 * g - 3)),
                φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
                  ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j)
              (hΘ : ∀ j, Circle.exp ∘ (fun x => Θ x j) = fun x => φ x j)
              (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
                R hg hgenus hA hAlt D0 φ Θ)
              (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
                R hg hgenus hA hAlt D0 φ Θ)
              (hGeom : Unproved.Teichmuller.OriginalSignedAngularTwistMarkingRealization
                R hg hgenus hA hAlt D0 φ Θ hφ hΘ
                (originalFNRealCoordinateMap_isHomeomorph R hg hgenus hA hAlt D0
                  hU φ Θ hφ hΘ hRigid hRealize)
                hp j A Q s hs hAΓ (by simpa only [hC] using hcov) hQA),
              let := R.toRiemannAtlas.toChartedSpace
              let := R.toRiemannAtlas.isManifold
              let := R.t2Space
              let := R.connectedSpace
              let := R.compactSpace
              let := nativeFrickeTopology hA
              let L := q.length.toReal
              let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
              let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
              let hpQ : LiZhongQC.IsUniformization ΓQ pQ :=
                LiZhongQC.adjustProjection_isUniformization hp Q
              let hΓ := LiZhongQC.utm_x_isFuchsian hp
              let hΓQ : LiZhongQC.IsFuchsian ΓQ := LiZhongQC.utm_x_isFuchsian hpQ
              let hfree := LiZhongQC.s27g_actsFreely hp
              let hP := canonicalHandleGroupPresentation g
              let θ := canonicalBandWidth s hs
              let CQ := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup ΓQ s))
              let mQ : ΓQ → ℂ → ℂ := fun δ => LiZhongQC.h36p_m δ.val
              let F := originalFNRealCoordinateMap R hg hgenus hA hAlt D0 Θ
              let x₀ := nativeFrickeHomeomorph hA hAlt (TeichmullerSpace.basePoint R)
              let lengths₀ := (F x₀).1
              let angles₀ := (F x₀).2
              let πOriginal := TeichmullerSpace.coefficientProjectionBall
                R hg hgenus hP hΓ hfree hp
              let BCOriginal := TeichmullerSpace.bersCoordinates
                R hg hgenus hP hΓ hfree hp
              let WOriginal := TeichmullerSpace.weightedLinearBersCoordinates R hg hgenus hP hΓ hp
              let coefficientIso := coefficientRealMobiusIsometry Γ Q
              let U := BersWeighted.automorphicRealMobiusIsometry Γ Q
              let νOriginal := coefficientIso ν
              let DQ := fderiv ℂ (BersWeighted.automorphicProjection hΓQ) 0 ν
              let DOriginal := fderiv ℂ (BersWeighted.automorphicProjection hΓ) 0 νOriginal
              let := NormedSpace.restrictScalars ℝ ℂ (Space ΓQ)
              let := NormedSpace.restrictScalars ℝ ℂ (Space Γ)
              let := NormedSpace.restrictScalars ℝ ℂ (BersWeighted.Automorphic ΓQ)
              let := NormedSpace.restrictScalars ℝ ℂ (BersWeighted.Automorphic Γ)
              let := IsScalarTower.restrictScalars ℝ ℂ (Space ΓQ)
              let := IsScalarTower.restrictScalars ℝ ℂ (Space Γ)
              let := IsScalarTower.restrictScalars ℝ ℂ (BersWeighted.Automorphic ΓQ)
              let := IsScalarTower.restrictScalars ℝ ℂ (BersWeighted.Automorphic Γ)
              let : ContinuousSMul ℝ (BersWeighted.Automorphic ΓQ) := IsScalarTower.continuousSMul ℂ
              let : ContinuousSMul ℝ (BersWeighted.Automorphic Γ) := IsScalarTower.continuousSMul ℂ
              ∃ (hNontrivial : Hyperbolic.realSLMobius A ≠ 1)
                (hTrace : 4 < (Matrix.trace A.val) ^ 2),
                ∃ γ : C(ℝ, TeichmullerSpace.{0, 0} R),
                  (∀ ξ : ℝ, F (nativeFrickeHomeomorph hA hAlt (γ ξ)) =
                    (lengths₀, Function.update angles₀ j ξ)) ∧
                  ∃ (b : Fin 2) (v : C(I, ℍ)),
                    (∀ u : I, pQ (v u) =
                      (D0.pants (inc.copy (j, b)).1).projection ((D0.seam (j, b)).curve u)) ∧
                    (v 0 : ℂ).re = 0 ∧
                    (∃ δ : ℝ, 0 < δ ∧
                      ∀ u : I, 0 < (u : ℝ) → (u : ℝ) < δ → (v u : ℂ).re < 0) ∧
                    let sideSign : ℝ := if b = 0 then 1 else -1
                    let ξ : ℝ → ℝ := fun t => angles₀ j + sideSign * (2 * Real.pi / L) * t
                    ∃ (m : ℝ → LiZhongQC.MarkedRS X) (μG : ℝ → Ball ΓQ),
                      let μOriginal : ℝ → Ball Γ := fun t => coefficientRealMobiusBallEquiv Γ Q (μG t)
                      (∀ t : ℝ,
                        Quot.mk (LiZhongQC.MarkedRS.Equiv (S₀ := X)) (m t) =
                          TeichmullerSpace.toSource R (γ (ξ t))) ∧
                      (∀ t : ℝ, LiZhongQC.s27u_liftCoeff pQ (m t).marking =ᵐ[
                          volume.restrict LiZhongQC.upperHalf] rightCosetCoefficientSum θ ΓQ s t) ∧
                      (∀ t : ℝ, planeRepresentative (μG t).val.val
                        =ᵐ[volume.restrict LiZhongQC.upperHalf] ((μP t).val : ℂ → ℂ)) ∧
                      (∀ t : ℝ, (μG t).val =
                        ((t : ℂ) / (1 - (t : ℂ) * infinitesimalScale θ)) • ν) ∧
                      (∀ t : ℝ, (μOriginal t).val =
                        ((t : ℂ) / (1 - (t : ℂ) * infinitesimalScale θ)) • νOriginal) ∧
                      (μOriginal 0).val = 0 ∧
                      HasDerivAt (fun t : ℝ => (μOriginal t).val) νOriginal 0 ∧
                      (∀ t : ℝ, πOriginal (μOriginal t) = γ (ξ t)) ∧
                      γ (angles₀ j) = TeichmullerSpace.basePoint R ∧
                      (∀ t : ℝ, WOriginal.symm (BCOriginal (γ (ξ t))) =
                        BersWeighted.automorphicProjection hΓ (μOriginal t).val) ∧
                      HasDerivAt (fun t : ℝ => WOriginal.symm (BCOriginal (γ (ξ t)))) DOriginal 0 ∧
                      U DQ = DOriginal ∧
                      (∀ ρ : CQ → ΓQ, (∀ u : CQ, Quotient.mk _ (ρ u) = u) →
                        TendstoLocallyUniformlyOn
                          (fun (E : Finset CQ) (z : ℂ) => (Complex.I / (2 * (Real.pi : ℂ))) *
                            ∑ u ∈ E, (deriv (mQ (ρ u)) z / mQ (ρ u) z) ^ 2)
                          ((DQ.toSource) : ℂ → ℂ)
                          (atTop : Filter (Finset CQ)) LiZhongQC.lowerHalf ∧
                        ∀ z : ℂ, z ∈ LiZhongQC.lowerHalf →
                          HasSum (fun u : CQ => (Complex.I / (2 * (Real.pi : ℂ))) *
                            (deriv (mQ (ρ u)) z / mQ (ρ u) z) ^ 2) ((DQ.toSource : ℂ → ℂ) z) ∧
                          (DQ.toSource : ℂ → ℂ) z = (Complex.I / (2 * (Real.pi : ℂ))) *
                            ∑' u : CQ, (deriv (mQ (ρ u)) z / mQ (ρ u) z) ^ 2) ∧
                      let CA := Quotient (QuotientGroup.rightRel
                        (Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
                          (Subgroup.zpowers (Hyperbolic.realSLMobius A))))
                      (∀ (ρ : CA → Γ), (∀ u : CA, Quotient.mk _ (ρ u) = u) →
                        ∀ z : ℂ, z ∈ LiZhongQC.lowerHalf →
                          (DOriginal.toSource : ℂ → ℂ) z = (Complex.I / (2 * (Real.pi : ℂ))) *
                            conj (GeodesicSeries.peterssonSeries Γ A hNontrivial hTrace ρ (conj z))) ∧
                      ∀ (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
                        (FOriginal : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P FOriginal),
                        ∃ Ψ : HolomorphicQuadraticDifferential R.toRiemannAtlas,
                          (∀ (ρ : CA → Γ), (∀ u : CA, Quotient.mk _ (ρ u) = u) →
                            ∀ z : ℂ, z ∈ LiZhongQC.upperHalf →
                              QuadraticBergman.uniformizedQuadratic R M.halfPlaneCover Ψ z =
                                  GeodesicSeries.peterssonSeries Γ A hNontrivial hTrace ρ z ∧
                                HasSum (fun u : CA =>
                                  GeodesicSeries.seed (Hyperbolic.hHyperbolicAxis A hNontrivial hTrace)
                                      (LiZhongQC.h36p_m (ρ u).val z) *
                                    (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2)
                                  (QuadraticBergman.uniformizedQuadratic R M.halfPlaneCover Ψ z) ∧
                                Summable (fun u : CA =>
                                  ‖GeodesicSeries.seed (Hyperbolic.hHyperbolicAxis A hNontrivial hTrace)
                                      (LiZhongQC.h36p_m (ρ u).val z) *
                                    (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2‖)) ∧
                          NativePetersson.harmonicProjection R P M.halfPlaneCover hp FOriginal hF νOriginal =
                            (-(Complex.I / (Real.pi : ℂ))) •
                              NativeHarmonicBeltrami.ofQuadratic R M.halfPlaneCover hp Ψ ∧
                          νOriginal - (-(Complex.I / (Real.pi : ℂ))) •
                              NativeHarmonicBeltrami.ofQuadratic R M.halfPlaneCover hp Ψ ∈
                            NativePetersson.infinitesimalSubmodule Γ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  obtain ⟨inc, D0, j, hC⟩ := hReference
  obtain ⟨A, Q, s, hs, hAΓ, hcov, hQA, hsep⟩ :=
    originalClosedGeodesic_exists_normalized_angular_one_support q hp hcircle
  refine ⟨inc, D0, j, hC, A, Q, s, hs, hAΓ, hcov, hQA, ?_⟩
  let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
  let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
  let hpQ : LiZhongQC.IsUniformization ΓQ pQ :=
    LiZhongQC.adjustProjection_isUniformization hp Q
  let hΓQ := LiZhongQC.utm_x_isFuchsian hpQ
  let : Countable ΓQ := (LiZhongQC.h36p_countable hΓQ).to_subtype
  let θ := canonicalBandWidth s hs
  obtain ⟨ν, hν, hνnorm⟩ := exists_rightCosetInfinitesimalSum_native θ ΓQ s hsep
  obtain ⟨_v, μP, _ε, _hv, _hvnorm, hμP, _hdecomp, _hε, _hzero, _hvar, _hderiv⟩ :=
    exists_rightCosetCoefficientSum_canonical_variation θ ΓQ s hsep
  refine ⟨ν, hν, hνnorm, μP, hμP, hsep, ?_⟩
  intro hU φ Θ hφ hΘ hRigid hRealize hGeom
  exact given_originalGeodesic_same_signed_curve_original_series R hg hgenus hA hAlt D0
    hU φ Θ hφ hΘ hRigid hRealize hp j q hC A Q s hs hAΓ hcov hQA hGeom
    ν hν μP hμP hsep

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
