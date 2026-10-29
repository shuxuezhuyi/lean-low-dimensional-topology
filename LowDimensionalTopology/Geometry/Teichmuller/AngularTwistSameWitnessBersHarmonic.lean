module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistGivenHarmonicSeries
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistOriginalFNBersCurve

/-!
# One signed angular curve and its same harmonic series

A fixed whole compatible coefficient and plane family determine the same
signed FN curve, its actual Bers derivative and both convergent half-plane
series. The harmonic projection uses this given coefficient throughout.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped unitInterval UpperHalfPlane Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

open Surfaces Surfaces.HandlePresentation

local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
variable (D₀ : OriginalFNRealization M inc)

/-- The actual signed curve and the harmonic calculation retain the same
given direction, normalized covering and physical length parameter. -/
theorem given_originalSignedAngularTwist_same_bers_harmonic_series
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
    (j : Fin (3 * g - 3)) (A Q : Deck) (s : ℝ) (hs : 0 < s)
    (hAΓ : A ∈ Γ)
    (hcov : LiZhongQC.Covers M.halfPlaneCover A (D₀.cuff j).toLoop)
    (hQA : Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))
    (hGeom : Unproved.Teichmuller.OriginalSignedAngularTwistMarkingRealization
      R hg hgenus hA hAlt D₀ φ Θ hφ hΘ
      (originalFNRealCoordinateMap_isHomeomorph R hg hgenus hA hAlt D₀
        hU φ Θ hφ hΘ hRigid hRealize)
      hp j A Q s hs hAΓ hcov hQA)
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
    let q := D₀.cuff j
    let L := q.length.toReal
    let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
    let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
    let hpQ : LiZhongQC.IsUniformization ΓQ pQ :=
      LiZhongQC.adjustProjection_isUniformization hp Q
    let hΓQ : LiZhongQC.IsFuchsian ΓQ := LiZhongQC.utm_x_isFuchsian hpQ
    let hfreeQ : LiZhongQC.ActsFreely ΓQ := LiZhongQC.s27g_actsFreely hpQ
    let hP := canonicalHandleGroupPresentation g
    let θ := canonicalBandWidth s hs
    let CQ := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup ΓQ s))
    let mQ : ΓQ → ℂ → ℂ := fun δ =>
      LiZhongQC.mobiusFn (δ.val 0 0) (δ.val 0 1) (δ.val 1 0) (δ.val 1 1)
    let F := originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
    let x₀ := nativeFrickeHomeomorph hA hAlt (TeichmullerSpace.basePoint R)
    let lengths₀ := (F x₀).1
    let angles₀ := (F x₀).2
    let πQ := TeichmullerSpace.coefficientProjectionBall
      R hg hgenus hP hΓQ hfreeQ hpQ
    let BCQ := TeichmullerSpace.bersCoordinates
      R hg hgenus hP hΓQ hfreeQ hpQ
    let WQ := TeichmullerSpace.weightedLinearBersCoordinates R hg hgenus hP hΓQ hpQ
    let := NormedSpace.restrictScalars ℝ ℂ (GammaMeasurableBeltrami.Space ΓQ)
    let := NormedSpace.restrictScalars ℝ ℂ (BersWeighted.Automorphic ΓQ)
    let := IsScalarTower.restrictScalars ℝ ℂ (GammaMeasurableBeltrami.Space ΓQ)
    let := IsScalarTower.restrictScalars ℝ ℂ (BersWeighted.Automorphic ΓQ)
    let : ContinuousSMul ℝ (BersWeighted.Automorphic ΓQ) := IsScalarTower.continuousSMul ℂ
    ∃ γ : C(ℝ, TeichmullerSpace.{0, 0} R),
      (∀ ξ : ℝ,
        F (nativeFrickeHomeomorph hA hAlt (γ ξ)) =
          (lengths₀, Function.update angles₀ j ξ)) ∧
      ∃ (b : Fin 2) (v : C(I, ℍ)),
        (∀ u : I, pQ (v u) =
          (D₀.pants (inc.copy (j, b)).1).projection ((D₀.seam (j, b)).curve u)) ∧
        (v 0 : ℂ).re = 0 ∧
        (∃ δ : ℝ, 0 < δ ∧
          ∀ u : I, 0 < (u : ℝ) → (u : ℝ) < δ → (v u : ℂ).re < 0) ∧
        let sideSign : ℝ := if b = 0 then 1 else -1
        let ξ : ℝ → ℝ := fun t => angles₀ j + sideSign * (2 * Real.pi / L) * t
        ∃ (m : ℝ → LiZhongQC.MarkedRS X) (μG : ℝ → GammaMeasurableBeltrami.Ball ΓQ),
          (∀ t : ℝ,
            Quot.mk (LiZhongQC.MarkedRS.Equiv (S₀ := X)) (m t) =
              TeichmullerSpace.toSource R (γ (ξ t))) ∧
          (∀ t : ℝ,
            LiZhongQC.s27u_liftCoeff pQ (m t).marking =ᵐ[
                volume.restrict LiZhongQC.upperHalf]
              rightCosetCoefficientSum θ ΓQ s t) ∧
          (∀ t : ℝ,
            GammaMeasurableBeltrami.planeRepresentative (μG t).val.val
              =ᵐ[volume.restrict LiZhongQC.upperHalf] ((μP t).val : ℂ → ℂ)) ∧
          (∀ t : ℝ, (μG t).val =
            ((t : ℂ) / (1 - (t : ℂ) * infinitesimalScale θ)) • ν) ∧
          (μG 0).val = 0 ∧
          HasDerivAt (fun t : ℝ => (μG t).val) ν 0 ∧
          (∀ t : ℝ, πQ (μG t) = γ (ξ t)) ∧
          γ (angles₀ j) = TeichmullerSpace.basePoint R ∧
          (∀ t : ℝ, WQ.symm (BCQ (γ (ξ t))) =
            BersWeighted.automorphicProjection hΓQ (μG t).val) ∧
          HasDerivAt (fun t : ℝ => WQ.symm (BCQ (γ (ξ t))))
            (fderiv ℂ (BersWeighted.automorphicProjection hΓQ) 0 ν) 0 ∧
          (∀ ρ : CQ → ΓQ, (∀ u : CQ, Quotient.mk _ (ρ u) = u) →
            TendstoLocallyUniformlyOn
              (fun (E : Finset CQ) (z : ℂ) =>
                (Complex.I / (2 * (Real.pi : ℂ))) *
                  ∑ u ∈ E, (deriv (mQ (ρ u)) z / mQ (ρ u) z) ^ 2)
              (((fderiv ℂ (BersWeighted.automorphicProjection hΓQ) 0 ν).toSource) : ℂ → ℂ)
              (atTop : Filter (Finset CQ)) LiZhongQC.lowerHalf ∧
            ∀ z : ℂ, z ∈ LiZhongQC.lowerHalf →
              HasSum (fun u : CQ => (Complex.I / (2 * (Real.pi : ℂ))) *
                (deriv (mQ (ρ u)) z / mQ (ρ u) z) ^ 2)
                (((fderiv ℂ (BersWeighted.automorphicProjection hΓQ) 0 ν).toSource : ℂ → ℂ) z) ∧
              (((fderiv ℂ (BersWeighted.automorphicProjection hΓQ) 0 ν).toSource : ℂ → ℂ) z) =
                (Complex.I / (2 * (Real.pi : ℂ))) *
                  ∑' u : CQ, (deriv (mQ (ρ u)) z / mQ (ρ u) z) ^ 2) ∧
          ∀ (P : Fuchsian.HalfPlaneFuchsianGroup (ΓQ.map Hyperbolic.realSLMobius))
            (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F),
            ∃ Ψ : HolomorphicQuadraticDifferential R.toRiemannAtlas,
              (∀ ρ : CQ → ΓQ, (∀ u : CQ, Quotient.mk _ (ρ u) = u) →
                (∀ z : ℂ, z ∈ LiZhongQC.upperHalf →
                  HasSum (fun u : CQ => (deriv (mQ (ρ u)) z / mQ (ρ u) z) ^ 2)
                    (QuadraticBergman.uniformizedQuadratic R pQ Ψ z) ∧
                  Summable (fun u : CQ => ‖(deriv (mQ (ρ u)) z / mQ (ρ u) z) ^ 2‖)) ∧
                TendstoLocallyUniformlyOn
                  (fun (E : Finset CQ) (z : ℂ) =>
                    ∑ u ∈ E, (deriv (mQ (ρ u)) z / mQ (ρ u) z) ^ 2)
                  (QuadraticBergman.uniformizedQuadratic R pQ Ψ)
                  (atTop : Filter (Finset CQ)) LiZhongQC.upperHalf) ∧
              NativePetersson.harmonicProjection R P pQ hpQ F hF ν =
                (-(Complex.I / (Real.pi : ℂ))) •
                  NativeHarmonicBeltrami.ofQuadratic R pQ hpQ Ψ ∧
              ν - (-(Complex.I / (Real.pi : ℂ))) •
                  NativeHarmonicBeltrami.ofQuadratic R pQ hpQ Ψ ∈
                NativePetersson.infinitesimalSubmodule ΓQ := by
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
  let hΓQ : LiZhongQC.IsFuchsian ΓQ := LiZhongQC.utm_x_isFuchsian hpQ
  let θ := canonicalBandWidth s hs
  have hcount : (ΓQ : Set Deck).Countable := by
    rw [Subgroup.coe_map]
    exact (LiZhongQC.h36p_countable (LiZhongQC.utm_x2_isFuchsian hp)).image _
  let : Countable ΓQ := hcount.to_subtype
  let := NormedSpace.restrictScalars ℝ ℂ (GammaMeasurableBeltrami.Space ΓQ)
  let := NormedSpace.restrictScalars ℝ ℂ (BersWeighted.Automorphic ΓQ)
  let := IsScalarTower.restrictScalars ℝ ℂ (GammaMeasurableBeltrami.Space ΓQ)
  let := IsScalarTower.restrictScalars ℝ ℂ (BersWeighted.Automorphic ΓQ)
  let : ContinuousSMul ℝ (BersWeighted.Automorphic ΓQ) := IsScalarTower.continuousSMul ℂ
  obtain ⟨γ, hγ, b, v, hv, haxis, hleft, m, μG, hmclass, hmcoeff, hsame,
      hclass, hzero, hderiv, hnative, horigin, hcoord, hBcurve⟩ :=
    exists_same_originalSignedAngularTwist_bers_curve R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize hp j A Q s hs hAΓ hcov hQA hGeom ν hν μP hμP
  refine ⟨γ, hγ, b, v, hv, haxis, hleft, m, μG, hmclass, hmcoeff, hsame,
    hclass, hzero, hderiv, hnative, horigin, hcoord, hBcurve, ?_, ?_⟩
  · have hD := rightCosetInfinitesimalSum_fderiv_bers θ ΓQ s hΓQ hsep ν hν
    simp +unfoldPartialApp only [rightCosetInfinitesimalSum] at hD
    intro ρ hρ
    obtain ⟨hlocal, hpoint⟩ := (rightCosetCauchySeries_thirdDerivative θ ΓQ s hsep).2 ρ hρ
    refine ⟨hlocal.congr_right ?_, ?_⟩
    · intro z hz
      exact (hD hz).symm
    · intro z hz
      have hvalue := hpoint z hz
      rw [← hD hz] at hvalue
      exact hvalue
  · intro P F hF
    exact givenAngularInfinitesimal_exists_harmonic_series R θ ΓQ s pQ hpQ hsep ν hν P F hF

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
