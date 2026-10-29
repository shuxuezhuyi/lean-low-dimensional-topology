module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNReferenceContainingGeodesic
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalSignedAngularTwistMarkedCurve
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistOriginalCollarSupport

/-!
# The signed FN marking along the same original simple geodesic

An exact cuff equality in the given reference realization retains the
original geodesic's orientation, full period and length. Its actual normalized
covering supplies the same angular support. The fixed-cuff marking interface
then gives the actual QC marked family and its literal lifted coefficient
at the same signed hyperbolic-length parameter.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped unitInterval UpperHalfPlane Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

open Surfaces Surfaces.HandlePresentation

local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- A prescribed original simple geodesic has the same signed QC marking
family under the explicit reference-data and existing FN geometric inputs. -/
theorem arbitraryOriginalGeodesic_signedFN_realization
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
    (hp : let := R.toRiemannAtlas.toChartedSpace;
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
        (∀ ζ : ℂ,
          ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup ΓQ s)),
            rightCosetInfinitesimalZeroExtension θ ΓQ s u ζ ≠ 0 →
            rightCosetInfinitesimalZeroExtension θ ΓQ s v ζ ≠ 0 → u = v) ∧
        ∀ (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D0)
          (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
          (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
          (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
            (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
            (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D0 m D)
            (k : Fin (3 * g - 3)),
            φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
              ⟨TeichmullerSpace.mk m, rfl⟩⟩ k = D.phase k)
          (hΘ : ∀ k, Circle.exp ∘ (fun x => Θ x k) = fun x => φ x k)
          (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
            R hg hgenus hA hAlt D0 φ Θ)
          (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
            R hg hgenus hA hAlt D0 φ Θ),
          let hcovD : LiZhongQC.Covers M.halfPlaneCover A (D0.cuff j).toLoop :=
            by simpa only [hC] using hcov
          let hF := originalFNRealCoordinateMap_isHomeomorph R hg hgenus hA hAlt D0
            hU φ Θ hφ hΘ hRigid hRealize
          Unproved.Teichmuller.OriginalSignedAngularTwistMarkingRealization
            R hg hgenus hA hAlt D0 φ Θ hφ hΘ hF hp j A Q s hs hAΓ hcovD hQA →
          let := R.toRiemannAtlas.toChartedSpace
          let := nativeFrickeTopology hA
          let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
          let F := originalFNRealCoordinateMap R hg hgenus hA hAlt D0 Θ
          let x0 := nativeFrickeHomeomorph hA hAlt (TeichmullerSpace.basePoint R)
          let lengths0 := (F x0).1
          let angles0 := (F x0).2
          ∃ γ : C(ℝ, TeichmullerSpace.{0, 0} R),
            (∀ ξ : ℝ,
              F (nativeFrickeHomeomorph hA hAlt (γ ξ)) =
                (lengths0, Function.update angles0 j ξ)) ∧
            ∃ (b : Fin 2) (v : C(I, ℍ)),
              (∀ u : I, pQ (v u) =
                (D0.pants (inc.copy (j, b)).1).projection ((D0.seam (j, b)).curve u)) ∧
              (v 0 : ℂ).re = 0 ∧
              (∃ δ : ℝ, 0 < δ ∧
                ∀ u : I, 0 < (u : ℝ) → (u : ℝ) < δ → (v u : ℂ).re < 0) ∧
              let sideSign : ℝ := if b = 0 then 1 else -1
              ∃ m : ℝ → LiZhongQC.MarkedRS X,
                (∀ t : ℝ,
                  Quot.mk (LiZhongQC.MarkedRS.Equiv (S₀ := X)) (m t) =
                    TeichmullerSpace.toSource R
                      (γ (angles0 j + sideSign * (2 * Real.pi / q.length.toReal) * t))) ∧
                ∀ t : ℝ,
                  LiZhongQC.s27u_liftCoeff pQ (m t).marking =ᵐ[
                      volume.restrict LiZhongQC.upperHalf]
                    rightCosetCoefficientSum θ ΓQ s t := by
  obtain ⟨inc, D0, j, hC⟩ := hReference
  obtain ⟨A, Q, s, hs, hAΓ, hcov, hQA, hsep⟩ :=
    originalClosedGeodesic_exists_normalized_angular_one_support q hp hcircle
  refine ⟨inc, D0, j, hC, A, Q, s, hs, hAΓ, hcov, hQA, ?_⟩
  dsimp only
  refine ⟨hsep, ?_⟩
  intro hU φ Θ hφ hΘ hRigid hRealize hGeom
  have hcovD : LiZhongQC.Covers M.halfPlaneCover A (D0.cuff j).toLoop := by
    simpa only [hC] using hcov
  have h := exists_originalSignedAngularTwistMarkedCurve R hg hgenus hA hAlt D0
    hU φ Θ hφ hΘ hRigid hRealize hp j A Q s hs hAΓ hcovD hQA hGeom
  simpa only [hC] using h

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
