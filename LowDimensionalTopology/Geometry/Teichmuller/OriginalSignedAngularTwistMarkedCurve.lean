module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalSignedAngularTwistMarking
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNTwistCurve

/-!
# A QC representative of the same original signed FN curve

The existing faithful FN coordinate curve is selected with its actual
reference lengths and branch values. The explicit geometric interface then
supplies a QC marking with that same class and the same lifted raw angular
coefficient. No normalized-plane variation or series conclusion is repeated.
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

/-- The same original FN coordinate curve, reparametrized by the source
signed hyperbolic length, admits an actual QC representative with the
literal angular coefficient, under precisely the omitted geometry interface.
The same geometric interface supplies and retains the actual seam-side certificate. -/
theorem exists_originalSignedAngularTwistMarkedCurve
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
      hp j A Q s hs hAΓ hcov hQA) :
    let := R.toRiemannAtlas.toChartedSpace
    let := nativeFrickeTopology hA
    let q := D₀.cuff j
    let L := q.length.toReal
    let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
    let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
    let θ := canonicalBandWidth s hs
    let F := originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
    let x₀ := nativeFrickeHomeomorph hA hAlt (TeichmullerSpace.basePoint R)
    let lengths₀ := (F x₀).1
    let angles₀ := (F x₀).2
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
        ∃ m : ℝ → LiZhongQC.MarkedRS X,
          (∀ t : ℝ,
            Quot.mk (LiZhongQC.MarkedRS.Equiv (S₀ := X)) (m t) =
              TeichmullerSpace.toSource R
                (γ (angles₀ j + sideSign * (2 * Real.pi / L) * t))) ∧
          ∀ t : ℝ,
            LiZhongQC.s27u_liftCoeff pQ (m t).marking =ᵐ[
                volume.restrict LiZhongQC.upperHalf]
              rightCosetCoefficientSum θ ΓQ s t := by
  let := R.toRiemannAtlas.toChartedSpace
  let := nativeFrickeTopology hA
  let F := originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
  let x₀ := nativeFrickeHomeomorph hA hAlt (TeichmullerSpace.basePoint R)
  let lengths₀ := (F x₀).1
  let angles₀ := (F x₀).2
  obtain ⟨γ, hγ⟩ := exists_originalFNTwistCurve R hg hgenus hA hAlt D₀
    hU φ Θ hφ hΘ hRigid hRealize lengths₀ angles₀ j
  obtain ⟨b, v, hv, haxis, hleft, m, hmclass, hmcoeff⟩ := hGeom γ hγ
  exact ⟨γ, hγ, b, v, hv, haxis, hleft, m, hmclass, hmcoeff⟩

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
