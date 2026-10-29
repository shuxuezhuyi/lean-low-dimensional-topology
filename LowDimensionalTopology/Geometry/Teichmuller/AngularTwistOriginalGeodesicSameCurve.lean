module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistSameWitnessBersHarmonic
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistOriginalGammaHarmonicSeries
public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientRealMobiusNaturality
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.PureHyperbolicSharpness
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The same signed geodesic curve in the original covering

A fixed normalization and the same whole coefficient determine the signed
FN family in both covering coordinates. Its original weighted Bers derivative
is the reflected endpoint series, and the original Riesz quadratic gives
the harmonic representative of that same transported direction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped unitInterval UpperHalfPlane ComplexConjugate Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

open Surfaces Surfaces.HandlePresentation GammaMeasurableBeltrami

local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
variable (D₀ : OriginalFNRealization M inc)

set_option maxHeartbeats 800000 in
/-- The chosen original geodesic, its exact reference cuff and its given
coefficient retain one signed physical-length curve and one original harmonic
direction. The covering matrix is unchanged throughout. -/
theorem given_originalGeodesic_same_signed_curve_original_series
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
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (j : Fin (3 * g - 3)) (q : OriginalClosedGeodesic M) (hC : D₀.cuff j = q)
    (A Q : Deck) (s : ℝ) (hs : 0 < s)
    (hAΓ : A ∈ Γ)
    (hcov : LiZhongQC.Covers M.halfPlaneCover A q.toLoop)
    (hQA : Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))
    (hGeom : Unproved.Teichmuller.OriginalSignedAngularTwistMarkingRealization
      R hg hgenus hA hAlt D₀ φ Θ hφ hΘ
      (originalFNRealCoordinateMap_isHomeomorph R hg hgenus hA hAlt D₀
        hU φ Θ hφ hΘ hRigid hRealize)
      hp j A Q s hs hAΓ (by simpa only [hC] using hcov) hQA)
    (ν : GammaMeasurableBeltrami.Space (Γ.map (MulAut.conj Q).toMonoidHom))
    (hν : (ν.val : ℍ → ℂ) =ᵐ[volume]
      (fun z : ℍ => rightCosetInfinitesimalSum (canonicalBandWidth s hs)
        (Γ.map (MulAut.conj Q).toMonoidHom) s (z : ℂ)))
    (μP : ℝ → MeasurableBeltramiBall)
    (hμP : ∀ t : ℝ, ((μP t).val : ℂ → ℂ) =ᵐ[volume]
      rightCosetCoefficientSum (canonicalBandWidth s hs)
        (Γ.map (MulAut.conj Q).toMonoidHom) s t)
    (hsep : ∀ ζ : ℂ,
      ∀ u v : Quotient (QuotientGroup.rightRel
          (projectiveDilationSubgroup (Γ.map (MulAut.conj Q).toMonoidHom) s)),
        rightCosetInfinitesimalZeroExtension (canonicalBandWidth s hs)
          (Γ.map (MulAut.conj Q).toMonoidHom) s u ζ ≠ 0 →
        rightCosetInfinitesimalZeroExtension (canonicalBandWidth s hs)
          (Γ.map (MulAut.conj Q).toMonoidHom) s v ζ ≠ 0 → u = v) :
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
    let F := originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
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
            (D₀.pants (inc.copy (j, b)).1).projection ((D₀.seam (j, b)).curve u)) ∧
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
  let := nativeFrickeTopology hA
  let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
  let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
  let hpQ : LiZhongQC.IsUniformization ΓQ pQ :=
    LiZhongQC.adjustProjection_isUniformization hp Q
  let hΓ := LiZhongQC.utm_x_isFuchsian hp
  let hΓQ : LiZhongQC.IsFuchsian ΓQ := LiZhongQC.utm_x_isFuchsian hpQ
  let hfree := LiZhongQC.s27g_actsFreely hp
  let hP := canonicalHandleGroupPresentation g
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
  have hNoCentral (hcentral : A = 1 ∨ A = -1) : False := by
    have hzero := LiZhongQC.s30a_len_zero hp hAΓ
      (hcentral.elim Or.inl (fun h => Or.inr (Or.inl h))) hcov
    exact (ne_of_gt q.length_pos_and_ne_top.1) (q.length_eq_freeHomotopyLength.trans hzero)
  have hhyper : LiZhongQC.IsHyperbolic A := LiZhongQC.s27f_hyp hp hAΓ
    (fun h => hNoCentral (Or.inl h)) (fun h => hNoCentral (Or.inr h))
  have habs : 2 < |Matrix.trace A.val| := by
    simpa only [LiZhongQC.IsHyperbolic, LiZhongQC.slTrace, Matrix.trace_fin_two] using hhyper
  have hTrace : 4 < (Matrix.trace A.val) ^ 2 := by
    nlinarith [sq_abs (Matrix.trace A.val)]
  have hNontrivial := Fuchsian.realSLMobius_ne_one_of_trace_sq_gt_four A hTrace
  have hcovD : LiZhongQC.Covers M.halfPlaneCover A (D₀.cuff j).toLoop := by
    simpa only [hC] using hcov
  have hLength : (D₀.cuff j).length.toReal = q.length.toReal :=
    congrArg (fun c : OriginalClosedGeodesic M => c.length.toReal) hC
  have hJoin := given_originalSignedAngularTwist_same_bers_harmonic_series
    R hg hgenus hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hp j A Q s hs
    hAΓ hcovD hQA hGeom ν hν μP hμP hsep
  obtain ⟨γ, hγ, b, v, hv, haxis, hleft, m, μG, hmclass, hmcoeff, hsame,
    hclass, hzero, hderiv, hnative, horigin, hcoord, hBcurve, hLower, _hNormalizedHarmonic⟩ := hJoin
  let F := originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
  let x₀ := nativeFrickeHomeomorph hA hAlt (TeichmullerSpace.basePoint R)
  let angles₀ := (F x₀).2
  let sideSign : ℝ := if b = 0 then 1 else -1
  let ξ : ℝ → ℝ := fun t => angles₀ j + sideSign * (2 * Real.pi / q.length.toReal) * t
  have hξ (t : ℝ) :
      angles₀ j + sideSign * (2 * Real.pi / (D₀.cuff j).length.toReal) * t = ξ t := by
    dsimp only [ξ]
    rw [hLength]
  let μOriginal : ℝ → Ball Γ := fun t => coefficientRealMobiusBallEquiv Γ Q (μG t)
  let πOriginal := TeichmullerSpace.coefficientProjectionBall R hg hgenus hP hΓ hfree hp
  let BCOriginal := TeichmullerSpace.bersCoordinates R hg hgenus hP hΓ hfree hp
  let WOriginal := TeichmullerSpace.weightedLinearBersCoordinates R hg hgenus hP hΓ hp
  let WQ := TeichmullerSpace.weightedLinearBersCoordinates R hg hgenus hP hΓQ hpQ
  let BCQ := TeichmullerSpace.bersCoordinates R hg hgenus hP hΓQ
    (LiZhongQC.s27g_actsFreely hpQ) hpQ
  have hmclassOriginal (t : ℝ) :
      Quot.mk (LiZhongQC.MarkedRS.Equiv (S₀ := X)) (m t) =
        TeichmullerSpace.toSource R (γ (ξ t)) :=
    (hmclass t).trans (congrArg (fun r => TeichmullerSpace.toSource R (γ r)) (hξ t))
  have hcoordQ (t : ℝ) : WQ.symm (BCQ (γ (ξ t))) =
      BersWeighted.automorphicProjection hΓQ (μG t).val :=
    (congrArg (fun r => WQ.symm (BCQ (γ r))) (hξ t)).symm.trans (hcoord t)
  have hBcurveQ :
      HasDerivAt (fun t : ℝ => WQ.symm (BCQ (γ (ξ t)))) DQ 0 :=
    hBcurve.congr_of_eventuallyEq (Eventually.of_forall fun t =>
      (congrArg (fun r => WQ.symm (BCQ (γ r))) (hξ t)).symm)
  let IR : Space ΓQ →L[ℝ] Space Γ :=
    coefficientIso.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  let UR : BersWeighted.Automorphic ΓQ →L[ℝ] BersWeighted.Automorphic Γ :=
    U.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have hOriginalClass (t : ℝ) : (μOriginal t).val =
      ((t : ℂ) / (1 - (t : ℂ) * infinitesimalScale (canonicalBandWidth s hs))) • νOriginal := by
    exact (congrArg coefficientIso (hclass t)).trans (coefficientIso.map_smul _ _)
  have hOriginalZero : (μOriginal 0).val = 0 := by
    exact (congrArg coefficientIso hzero).trans coefficientIso.map_zero
  have hOriginalDeriv : HasDerivAt (fun t : ℝ => (μOriginal t).val) νOriginal 0 :=
    IR.hasFDerivAt.comp_hasDerivAt 0 hderiv
  have hOriginalPoint (t : ℝ) : πOriginal (μOriginal t) = γ (ξ t) := by
    have h := TeichmullerSpace.coefficientProjectionBall_realMobius_conjugate
      R hg hgenus hΓ hp Q (μOriginal t)
    have he : πOriginal (μOriginal t) =
        TeichmullerSpace.coefficientProjectionBall R hg hgenus hP hΓQ
          (LiZhongQC.s27g_actsFreely hpQ) hpQ (μG t) := by
      have hball : (coefficientRealMobiusBallEquiv Γ Q).symm (μOriginal t) = μG t :=
        (coefficientRealMobiusBallEquiv Γ Q).symm_apply_apply (μG t)
      rw [hball] at h
      exact h
    exact he.trans ((hnative t).trans (congrArg γ (hξ t)))
  have hOriginalCoord (t : ℝ) : WOriginal.symm (BCOriginal (γ (ξ t))) =
      BersWeighted.automorphicProjection hΓ (μOriginal t).val := by
    rw [← hOriginalPoint t]
    dsimp only [BCOriginal, πOriginal]
    rw [TeichmullerSpace.coefficientProjectionBall_coordinates R hg hgenus hP hΓ hfree hp]
    exact WOriginal.symm_apply_apply _
  have hCov := givenAngularInfinitesimal_originalGamma_bers_series
    Γ hΓ A hAΓ hNontrivial hTrace Q s hs hQA ν hν hsep
  have hBTransport (t : ℝ) : WOriginal.symm (BCOriginal (γ (ξ t))) =
      UR (WQ.symm (BCQ (γ (ξ t)))) := by
    rw [hOriginalCoord t, hcoordQ t]
    exact (BersWeighted.automorphicRealMobiusIsometry_projection hΓ Q (μG t)).symm
  have hOriginalBersDeriv :
      HasDerivAt (fun t : ℝ => WOriginal.symm (BCOriginal (γ (ξ t)))) DOriginal 0 := by
    have h := UR.hasFDerivAt.comp_hasDerivAt 0 hBcurveQ
    exact (h.congr_deriv hCov.1).congr_of_eventuallyEq (Eventually.of_forall hBTransport)
  refine ⟨hNontrivial, hTrace, γ, hγ, b, v, hv, haxis, hleft, m, μG,
    hmclassOriginal, hmcoeff, hsame, hclass, hOriginalClass, hOriginalZero, hOriginalDeriv,
    hOriginalPoint, horigin, hOriginalCoord, hOriginalBersDeriv, hCov.1, hLower, hCov.2, ?_⟩
  intro P FOriginal hF
  exact givenAngularInfinitesimal_originalGamma_harmonic_series R Γ hΓ M.halfPlaneCover hp
    A hAΓ hNontrivial hTrace Q s hs hQA ν hν hsep P FOriginal hF

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
