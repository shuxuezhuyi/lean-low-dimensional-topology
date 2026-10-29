module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNUnitNativeTwist
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceChangeDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCanonicalCoefficientCurve

/-!
# The physical original FN curve at its actual deformed reference

The geometric prerequisite concerns the same inverse-coordinate curve on
the fixed original Teichmuller space. Its actual reference change has a QC
marking with the literal angular coefficient on the actual deformed target.
The prescribed intrinsic left labels are supplied separately. The statement
does not identify a marking derivative or a Weil--Petersson contraction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped UpperHalfPlane Topology

namespace LowDimensionalTopology.Unproved.Teichmuller

open LowDimensionalTopology.Geometry
open Geometry.Surfaces Geometry.Surfaces.HandlePresentation
open Geometry.Teichmuller Geometry.Teichmuller.TeichmullerSpace
open Geometry.Teichmuller.GammaMeasurableBeltrami
open Geometry.Teichmuller.NormalizedCoefficientTransport

/-- The actual reference change of the same physical FN unit curve admits
the original cut/twist/reglue QC marking with its raw angular coefficient.
The full oriented cuff class and the prescribed normalization are retained.
Availability of these normalizing data and the actual left-copy convention
are separate geometric inputs. No tangent, differential or pairing is assumed. -/
def OriginalFNSameCurveDeformedReferenceMarking
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (hA : CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc)
    (hU : OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun x => Θ x j) = fun x => φ x j)
    (hRigid : OriginalFNMarkedCoordinateRigidity R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize : OriginalFNMarkedGluingRealization R hg hgenus hA hAlt D₀ φ Θ)
    (left : Fin (3 * g - 3) → Fin 2) : Prop := by
  let := R.toRiemannAtlas.toChartedSpace
  let σ := sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
    hU φ Θ hφ hΘ hRigid hRealize
  exact ∀ ν : Ball Γ,
    let Y := deformedNativeSurface R hgenus hΓ hp ν
    letI := Y.toRiemannAtlas.toChartedSpace
    let Δ := deformedGroup hΓ ν
    let pY := deformedTargetCover R hgenus hΓ hp ν
    let eY := deformedTargetMarking R hgenus hΓ hp ν
    let a := coefficientProjectionBall R hg hgenus
      (canonicalHandleGroupPresentation g) hΓ hfree hp ν
    let Aν := deformedReferenceChangeEquiv R hp hg hgenus hΓ ν
    ∀ j : Fin (3 * g - 3),
      let α : LiZhongQC.Loop (deformedTargetSource R hgenus hΓ hp ν).carrier :=
        ⟨eY (D₀.cuff j).toLoop.1, (D₀.cuff j).toLoop.2.map eY.continuous⟩
      ∀ (A Q : Deck) (s : ℝ) (hs : 0 < s),
        A ∈ Δ → LiZhongQC.Covers pY A α →
        Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
          Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s) →
        let ΔQ := Δ.map (MulAut.conj Q).toMonoidHom
        let θ := AngularTwist.canonicalBandWidth s hs
        (∀ ζ : ℂ,
          ∀ u v : Quotient (QuotientGroup.rightRel
            (AngularTwist.projectiveDilationSubgroup ΔQ s)),
            AngularTwist.rightCosetInfinitesimalZeroExtension θ ΔQ s u ζ ≠ 0 →
              AngularTwist.rightCosetInfinitesimalZeroExtension θ ΔQ s v ζ ≠ 0 →
                u = v) →
        ∃ m : ℝ → LiZhongQC.MarkedRS (deformedTargetSource R hgenus hΓ hp ν).carrier,
          (∀ t : ℝ,
            Quot.mk (LiZhongQC.MarkedRS.Equiv
              (S₀ := (deformedTargetSource R hgenus hΓ hp ν).carrier)) (m t) =
                toSource Y (Aν (σ a j (left j) t))) ∧
          ∀ t : ℝ,
            LiZhongQC.s27u_liftCoeff (LiZhongQC.adjustProjection pY Q) (m t).marking
              =ᵐ[volume.restrict LiZhongQC.upperHalf]
                AngularTwist.rightCosetCoefficientSum θ ΔQ s t

end LowDimensionalTopology.Unproved.Teichmuller
