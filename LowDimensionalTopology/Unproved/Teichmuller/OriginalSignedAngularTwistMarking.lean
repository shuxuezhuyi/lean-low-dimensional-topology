module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCanonicalCoefficientCurve
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNConditionalHomeomorph
public import LowDimensionalTopology.Geometry.Teichmuller.SourceMarking

/-!
# The original signed angular surgery marking: a precise geometric interface

The signed cut/twist/reglue curve is identified by its actual QC marking
and the literal coefficient of the same angular collar deformation.
This proposition retains the same reference surface, original cuff, full
covering matrix and normalizer. It supplies a QC representative of the same
faithful FN class with the same actual raw coefficient. Its signed length
parameter is converted to the existing real angle by the actual cuff length.
The same geometric proposition also supplies the actual reference seam
lift and its side certificate. No surgery construction is installed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Set MeasureTheory
open LowDimensionalTopology.Geometry
open scoped unitInterval UpperHalfPlane Topology
open LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Teichmuller
open LowDimensionalTopology.Geometry.Surfaces.HandlePresentation

local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The omitted original signed cut/twist/reglue identification, retaining
both the actual QC marked class and its literal lifted coefficient. No
analytic derivative or series conclusion is assumed. The returned seam
lift records which original intrinsic cuff copy is on the moving side. -/
def OriginalSignedAngularTwistMarkingRealization
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface}
    {inc : OriginalFNCuffIncidence g}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (_hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j)
    (_hΘ : ∀ j, Circle.exp ∘ (fun x => Θ x j) = fun x => φ x j)
    (_hF : IsHomeomorph (originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ))
    {Γ : Subgroup Deck}
    (_hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (j : Fin (3 * g - 3)) (A Q : Deck) (s : ℝ) (hs : 0 < s)
    (_hAΓ : A ∈ Γ)
    (_hcov : LiZhongQC.Covers M.halfPlaneCover A (D₀.cuff j).toLoop)
    (_hQA : Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s)) : Prop := by
  let := R.toRiemannAtlas.toChartedSpace
  let := nativeFrickeTopology hA
  let q := D₀.cuff j
  let L := q.length.toReal
  let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
  let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
  let θ := AngularTwist.canonicalBandWidth s hs
  let F := originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
  let x₀ := nativeFrickeHomeomorph hA hAlt (TeichmullerSpace.basePoint R)
  let lengths₀ := (F x₀).1
  let angles₀ := (F x₀).2
  exact ∀ (γ : C(ℝ, TeichmullerSpace.{0, 0} R)),
    (∀ ξ : ℝ,
      F (nativeFrickeHomeomorph hA hAlt (γ ξ)) =
        (lengths₀, Function.update angles₀ j ξ)) →
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
            AngularTwist.rightCosetCoefficientSum θ ΓQ s t

end LowDimensionalTopology.Unproved.Teichmuller
