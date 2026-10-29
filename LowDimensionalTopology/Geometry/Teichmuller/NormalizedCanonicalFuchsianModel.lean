module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedCanonicalConjugacy

/-!
# A given normalized canonical model of an original marked compact surface

The record retains actual endpoint monodromy and the book's dynamic labels.
Availability is separate; the standard presentation and uniqueness are outputs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation Hyperbolic Mobius
variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}

/-- Actual normalized model data for the prescribed ordered polygon marking. -/
structure NormalizedCanonicalFuchsianModel (hg : 1 < g)
    (e : X ≃ₜ PolygonQuotient g) (m : MarkedRiemannSurface.{0, 0} R) where
  model : HyperbolicSurfaceModel m.surface.toRiemannSurface
  liftBase : ℍ
  liftBase_proj : model.halfPlaneCover liftBase =
    (m.marking.toHomeomorph.symm.trans e).symm (boundaryBase g).val
  matrices : Edge g → Matrix.SpecialLinearGroup (Fin 2) ℝ
  represents : ∀ (d : Edge g) (z : ℍ), matrices d • z =
    model.markedPolygonEndpointDeck (m.marking.toHomeomorph.symm.trans e)
      liftBase liftBase_proj d • z
  alpha_attracting : MobiusAttractiveFixedPoint
    (realSLMobius (matrices (finalHandle hg, 0))) (1 : ℂ)
  beta_attracting_repelling : IsMobiusAttractingRepellingPair
    (realSLMobius (matrices (finalHandle hg, 1))) ∞ (0 : ℂ)

namespace NormalizedCanonicalFuchsianModel
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
variable {m n : MarkedRiemannSurface.{0, 0} R}

/-- The full true deck group has the standard sole surface relation; no
homomorphism of that group into SL is assumed. -/
theorem exists_deckMarking (P : NormalizedCanonicalFuchsianModel hg e m) :
    ∃ ρ : LiZhongQC.surfaceGroup g ≃* deck P.model.halfPlaneCover,
      ∀ (d : Edge g) (z : ℍ), P.matrices d • z =
        ρ (PresentedGroup.of (edgeLabelEquiv g d)) • z := by
  obtain ⟨ρ, hρ⟩ := P.model.exists_markedPolygonDeckEquiv (by omega)
    (m.marking.toHomeomorph.symm.trans e) P.liftBase P.liftBase_proj
  refine ⟨ρ, fun d z => ?_⟩
  exact (P.represents d z).trans
    (congrArg (fun k : deck P.model.halfPlaneCover => k • z) (hρ d))

/-- The raw given-model theorem determines every ordered projective generator
from the actual native marked equivalence class. -/
theorem generators_eq (P : NormalizedCanonicalFuchsianModel hg e m)
    (Q : NormalizedCanonicalFuchsianModel hg e n)
    (hmn : MarkedRiemannSurface.Equivalent m n) :
    ∀ d : Edge g, realSLMobius (P.matrices d) = realSLMobius (Q.matrices d) := by
  exact m.given_normalizedCanonicalGenerators_unique n P.model Q.model hg e
    P.liftBase Q.liftBase P.liftBase_proj Q.liftBase_proj P.matrices Q.matrices
    P.represents Q.represents P.alpha_attracting Q.alpha_attracting
    P.beta_attracting_repelling Q.beta_attracting_repelling hmn

end NormalizedCanonicalFuchsianModel
end LowDimensionalTopology.Geometry.Teichmuller
