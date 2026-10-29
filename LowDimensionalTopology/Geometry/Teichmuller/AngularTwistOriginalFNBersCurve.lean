module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistSameCanonicalGammaCurve
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalSignedAngularTwistMarkedCurve
public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientProjection
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge

/-!
# The same signed FN class in the actual coefficient and Bers projections

The original QC marking and its actual lifted coefficient identify the
same signed FN class with the compatible coefficient projection. The same
given coefficient family therefore gives its genuine weighted Bers curve
derivative, with the original side certificate and length parameter retained.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
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

/-- The same signed original FN curve is the actual compatible coefficient
projection, so its weighted Bers derivative is the native derivative on
the same given infinitesimal class. -/
theorem exists_same_originalSignedAngularTwist_bers_curve
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
        (Γ.map (MulAut.conj Q).toMonoidHom) s t) :
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
    let hpQ := LiZhongQC.adjustProjection_isUniformization hp Q
    let hΓQ : LiZhongQC.IsFuchsian ΓQ := LiZhongQC.utm_x_isFuchsian hpQ
    let hfreeQ : LiZhongQC.ActsFreely ΓQ := LiZhongQC.s27g_actsFreely hpQ
    let hP := canonicalHandleGroupPresentation g
    let θ := canonicalBandWidth s hs
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
            (fderiv ℂ (BersWeighted.automorphicProjection hΓQ) 0 ν) 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let := nativeFrickeTopology hA
  let L := (D₀.cuff j).length.toReal
  let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
  let hpQ := LiZhongQC.adjustProjection_isUniformization hp Q
  let hΓQ : LiZhongQC.IsFuchsian ΓQ := LiZhongQC.utm_x_isFuchsian hpQ
  let hfreeQ : LiZhongQC.ActsFreely ΓQ := LiZhongQC.s27g_actsFreely hpQ
  let hP := canonicalHandleGroupPresentation g
  let θ := canonicalBandWidth s hs
  let F := originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
  let x₀ := nativeFrickeHomeomorph hA hAlt (TeichmullerSpace.basePoint R)
  let lengths₀ := (F x₀).1
  let angles₀ := (F x₀).2
  let πQ := TeichmullerSpace.coefficientProjectionBall
    R hg hgenus hP hΓQ hfreeQ hpQ
  let BCQ := TeichmullerSpace.bersCoordinates R hg hgenus hP hΓQ hfreeQ hpQ
  let WQ := TeichmullerSpace.weightedLinearBersCoordinates R hg hgenus hP hΓQ hpQ
  let := NormedSpace.restrictScalars ℝ ℂ (GammaMeasurableBeltrami.Space ΓQ)
  let := NormedSpace.restrictScalars ℝ ℂ (BersWeighted.Automorphic ΓQ)
  let := IsScalarTower.restrictScalars ℝ ℂ (GammaMeasurableBeltrami.Space ΓQ)
  let := IsScalarTower.restrictScalars ℝ ℂ (BersWeighted.Automorphic ΓQ)
  let : ContinuousSMul ℝ (BersWeighted.Automorphic ΓQ) := IsScalarTower.continuousSMul ℂ
  obtain ⟨γ, hγ, b, v, hv, haxis, hleft, m, hmclass, hmcoeff⟩ :=
    exists_originalSignedAngularTwistMarkedCurve R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize hp j A Q s hs hAΓ hcov hQA hGeom
  obtain ⟨μG, hsame, hclass, hzero, hderiv, hBcurve⟩ :=
    exists_same_canonical_gamma_curve θ ΓQ s hΓQ ν hν μP hμP
  let sideSign : ℝ := if b = 0 then 1 else -1
  let ξ : ℝ → ℝ := fun t => angles₀ j + sideSign * (2 * Real.pi / L) * t
  have hrawG (t : ℝ) : GammaMeasurableBeltrami.planeRepresentative (μG t).val.val
      =ᵐ[volume.restrict LiZhongQC.upperHalf] rightCosetCoefficientSum θ ΓQ s t :=
    (hsame t).trans (ae_restrict_of_ae (hμP t))
  have hnative (t : ℝ) : πQ (μG t) = γ (ξ t) := by
    apply TeichmullerSpace.toSource_injective R
    exact (TeichmullerSpace.coefficientProjectionBall_realization
      R hg hgenus hP hΓQ hfreeQ hpQ (μG t) (m t)
      ((hmcoeff t).trans (hrawG t).symm)).trans (hmclass t)
  have horigin : γ (angles₀ j) = TeichmullerSpace.basePoint R := by
    apply (nativeFrickeHomeomorph hA hAlt).injective
    apply ((originalFNRealCoordinateMap_isHomeomorph R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize).homeomorph F).injective
    change F (nativeFrickeHomeomorph hA hAlt (γ (angles₀ j))) = F x₀
    exact ((hγ (angles₀ j)).trans
      (congrArg (fun a => (lengths₀, a)) (Function.update_eq_self j angles₀))).trans
        (Prod.eta (F x₀))
  have hcoord (t : ℝ) : WQ.symm (BCQ (γ (ξ t))) =
      BersWeighted.automorphicProjection hΓQ (μG t).val := by
    have hc := TeichmullerSpace.coefficientProjectionBall_coordinates
      R hg hgenus hP hΓQ hfreeQ hpQ (μG t)
    exact (congrArg WQ.symm ((congrArg BCQ (hnative t)).symm.trans hc)).trans
      (WQ.symm_apply_apply _)
  refine ⟨γ, hγ, b, v, hv, haxis, hleft, m, μG, hmclass, hmcoeff, hsame,
    hclass, hzero, hderiv, hnative, horigin, hcoord, ?_⟩
  exact hBcurve.congr_of_eventuallyEq (Filter.Eventually.of_forall hcoord)

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
