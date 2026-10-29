module

public import LowDimensionalTopology.Geometry.Teichmuller.ArbitraryOriginalGeodesicSignedFN
public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientProjection
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge

/-!
# The same original signed FN marked family

A prescribed geodesic and its exact reference cuff determine one selected
QC marked family under the explicit FN geometric inputs. Its faithful
coordinate curve keeps the signed physical length parameter, and every
compatible coefficient with the same raw tensor gives that same native point.
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

theorem exists_originalGeodesicSignedFNDeformation_data
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
      hp j A Q s hs hAΓ (by simpa only [hC] using hcov) hQA) :
    let := R.toRiemannAtlas.toChartedSpace
    let := nativeFrickeTopology hA
    let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
    let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
    let θ := canonicalBandWidth s hs
    let F := originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
    let x₀ := nativeFrickeHomeomorph hA hAlt (TeichmullerSpace.basePoint R)
    let lengths₀ := (F x₀).1
    let angles₀ := (F x₀).2
    ∃ m : ℝ → LiZhongQC.MarkedRS X,
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
          let ξ : ℝ → ℝ := fun t => angles₀ j + sideSign * (2 * Real.pi / q.length.toReal) * t
          (∀ t : ℝ, Quot.mk (LiZhongQC.MarkedRS.Equiv (S₀ := X)) (m t) =
            TeichmullerSpace.toSource R (γ (ξ t))) ∧
          ∀ t : ℝ, LiZhongQC.s27u_liftCoeff pQ (m t).marking =ᵐ[
              volume.restrict LiZhongQC.upperHalf] rightCosetCoefficientSum θ ΓQ s t := by
  let := R.toRiemannAtlas.toChartedSpace
  let := nativeFrickeTopology hA
  have hcovD : LiZhongQC.Covers M.halfPlaneCover A (D₀.cuff j).toLoop := by
    simpa only [hC] using hcov
  have h := exists_originalSignedAngularTwistMarkedCurve R hg hgenus hA hAlt D₀
    hU φ Θ hφ hΘ hRigid hRealize hp j A Q s hs hAΓ hcovD hQA hGeom
  simp only [hC] at h
  obtain ⟨γ, hγ, b, v, hv, haxis, hleft, m, hmclass, hmcoeff⟩ := h
  exact ⟨m, γ, hγ, b, v, hv, haxis, hleft, hmclass, hmcoeff⟩

/-- The actual QC marked family of the chosen original geodesic, retaining
its full-period reference cuff and the signed physical-length parameter. -/
def originalGeodesicSignedFNDeformation
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
      hp j A Q s hs hAΓ (by simpa only [hC] using hcov) hQA) :
    let := R.toRiemannAtlas.toChartedSpace
    ℝ → LiZhongQC.MarkedRS X := by
  let := R.toRiemannAtlas.toChartedSpace
  exact Classical.choose (exists_originalGeodesicSignedFNDeformation_data R hg hgenus hA hAlt D₀
    hU φ Θ hφ hΘ hRigid hRealize hp j q hC A Q s hs hAΓ hcov hQA hGeom)

/-- The selected family has the same faithful FN coordinate curve, seam side,
basepoint and literal coefficient. Every actual compatible realization of that
coefficient is precisely this same native marked point. -/
theorem originalGeodesicSignedFNDeformation_spec
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
      hp j A Q s hs hAΓ (by simpa only [hC] using hcov) hQA) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R.t2Space
    let := R.connectedSpace
    let := R.compactSpace
    let := nativeFrickeTopology hA
    let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
    let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
    let hpQ : LiZhongQC.IsUniformization ΓQ pQ :=
      LiZhongQC.adjustProjection_isUniformization hp Q
    let hΓQ := LiZhongQC.utm_x_isFuchsian hpQ
    let hfreeQ := LiZhongQC.s27g_actsFreely hpQ
    let θ := canonicalBandWidth s hs
    let F := originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
    let x₀ := nativeFrickeHomeomorph hA hAlt (TeichmullerSpace.basePoint R)
    let lengths₀ := (F x₀).1
    let angles₀ := (F x₀).2
    let m := originalGeodesicSignedFNDeformation R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize hp j q hC A Q s hs hAΓ hcov hQA hGeom
    ∃ γ : C(ℝ, TeichmullerSpace.{0, 0} R),
      (∀ ξ : ℝ, F (nativeFrickeHomeomorph hA hAlt (γ ξ)) =
        (lengths₀, Function.update angles₀ j ξ)) ∧
      γ (angles₀ j) = TeichmullerSpace.basePoint R ∧
      ∃ (b : Fin 2) (v : C(I, ℍ)),
        (∀ u : I, pQ (v u) =
          (D₀.pants (inc.copy (j, b)).1).projection ((D₀.seam (j, b)).curve u)) ∧
        (v 0 : ℂ).re = 0 ∧
        (∃ δ : ℝ, 0 < δ ∧
          ∀ u : I, 0 < (u : ℝ) → (u : ℝ) < δ → (v u : ℂ).re < 0) ∧
        let sideSign : ℝ := if b = 0 then 1 else -1
        let ξ : ℝ → ℝ := fun t => angles₀ j + sideSign * (2 * Real.pi / q.length.toReal) * t
        (∀ t : ℝ, Quot.mk (LiZhongQC.MarkedRS.Equiv (S₀ := X)) (m t) =
          TeichmullerSpace.toSource R (γ (ξ t))) ∧
        (∀ t : ℝ, LiZhongQC.s27u_liftCoeff pQ (m t).marking =ᵐ[
            volume.restrict LiZhongQC.upperHalf] rightCosetCoefficientSum θ ΓQ s t) ∧
        ∀ (t : ℝ) (μ : GammaMeasurableBeltrami.Ball ΓQ),
          GammaMeasurableBeltrami.planeRepresentative μ.val.val =ᵐ[
              volume.restrict LiZhongQC.upperHalf] rightCosetCoefficientSum θ ΓQ s t →
          TeichmullerSpace.coefficientProjectionBall R hg hgenus
            (canonicalHandleGroupPresentation g) hΓQ hfreeQ hpQ μ = γ (ξ t) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let := nativeFrickeTopology hA
  let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
  let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
  let hpQ : LiZhongQC.IsUniformization ΓQ pQ :=
    LiZhongQC.adjustProjection_isUniformization hp Q
  let hΓQ := LiZhongQC.utm_x_isFuchsian hpQ
  let hfreeQ := LiZhongQC.s27g_actsFreely hpQ
  let F := originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
  let x₀ := nativeFrickeHomeomorph hA hAlt (TeichmullerSpace.basePoint R)
  let angles₀ := (F x₀).2
  obtain ⟨γ, hγ, b, v, hv, haxis, hleft, hmclass, hmcoeff⟩ :=
    Classical.choose_spec (exists_originalGeodesicSignedFNDeformation_data R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize hp j q hC A Q s hs hAΓ hcov hQA hGeom)
  let family := originalGeodesicSignedFNDeformation R hg hgenus hA hAlt D₀
    hU φ Θ hφ hΘ hRigid hRealize hp j q hC A Q s hs hAΓ hcov hQA hGeom
  have hFamily : family =
      Classical.choose (exists_originalGeodesicSignedFNDeformation_data R hg hgenus hA hAlt D₀
        hU φ Θ hφ hΘ hRigid hRealize hp j q hC A Q s hs hAΓ hcov hQA hGeom) := rfl
  rw [← hFamily] at hmclass hmcoeff
  refine ⟨γ, hγ, ?_, b, v, hv, haxis, hleft, hmclass, hmcoeff, ?_⟩
  · apply (nativeFrickeHomeomorph hA hAlt).injective
    have hF := originalFNRealCoordinateMap_isHomeomorph R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize
    apply (hF.homeomorph F).injective
    change F ((nativeFrickeHomeomorph hA hAlt) (γ (angles₀ j))) = F x₀
    simpa only [angles₀, F, x₀, Function.update_eq_self] using hγ (angles₀ j)
  · intro t μ hμ
    apply TeichmullerSpace.toSource_injective R
    exact (TeichmullerSpace.coefficientProjectionBall_realization R hg hgenus
      (canonicalHandleGroupPresentation g) hΓQ hfreeQ hpQ μ
      (family t) ((hmcoeff t).trans hμ.symm)).trans (hmclass t)

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
