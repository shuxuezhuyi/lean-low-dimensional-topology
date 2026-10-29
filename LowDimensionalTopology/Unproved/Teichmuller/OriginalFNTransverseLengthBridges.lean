/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNThreeBlockData
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNTwistCurve

/-!
# Unproved locality and signed annular shift for the prescribed lengths

The first proposition keeps the actual transverse length unchanged when its
cuff lengths and own real angle agree. The second compares the actual
once-twisted free class with the same original length on the same based native
curve at one signed full angular shift. The sign belongs to the geometric
conclusion and is not a field of the prescribed source data.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Surfaces.HandlePresentation Geometry.Teichmuller

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
variable (hA : CanonicalNormalizedModelsAvailable R hg e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
variable (D₀ : OriginalFNRealization M inc) (T : OriginalFNThreeBlockData D₀)
variable (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
variable (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))

/-- The original length of the selected actual transverse curve depends only
on the original cuff-length vector and its own chosen real twist angle. -/
def OriginalFNTransverseOtherTwistsInvariant : Prop :=
  OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀ →
  (∀ (m : MarkedRiemannSurface.{0, 0} R)
    (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
    (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
    (j : Fin (3 * g - 3)),
    φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
      ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j) →
  (∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j) →
  OriginalFNMarkedCoordinateRigidity R hg hgenus hA hAlt D₀ φ Θ →
  OriginalFNMarkedGluingRealization R hg hgenus hA hAlt D₀ φ Θ →
  ∀ (j : Fin (3 * g - 3)) (t u : nativeFrickeImage hA),
    (originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ t).1 =
      (originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ u).1 →
    (originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ t).2 j =
      (originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ u).2 j →
    frickeGeodesicLength R hg hgenus hA hAlt (T.tau0 j).toLoop t =
      frickeGeodesicLength R hg hgenus hA hAlt (T.tau0 j).toLoop u

/-- The actual once-annular-twisted free class has the original transverse
length one signed full angular period later on the same based native curve.
The sign is shared across all basepoints and is allowed to reflect the
annulus and phase-side choices. A full angle corresponds to the actual cuff's
full hyperbolic length at the target. -/
def OriginalFNSignedDehnLengthShift : Prop :=
  letI := nativeFrickeTopology hA
  OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀ →
  (∀ (m : MarkedRiemannSurface.{0, 0} R)
    (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
    (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
    (j : Fin (3 * g - 3)),
    φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
      ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j) →
  (∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j) →
  OriginalFNMarkedCoordinateRigidity R hg hgenus hA hAlt D₀ φ Θ →
  OriginalFNMarkedGluingRealization R hg hgenus hA hAlt D₀ φ Θ →
  ∃ ε : Fin (3 * g - 3) → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
    ∀ (t₀ : nativeFrickeImage hA) (j : Fin (3 * g - 3))
      (γ : C(ℝ, TeichmullerSpace.{0, 0} R)),
      (∀ s : ℝ,
        originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
          (nativeFrickeHomeomorph hA hAlt (γ s)) =
            ((originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ t₀).1,
              Function.update
                (originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ t₀).2 j
                ((originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ t₀).2 j + s))) →
      ∀ s : ℝ,
        frickeGeodesicLength R hg hgenus hA hAlt (T.tau1 j).toLoop
          (nativeFrickeHomeomorph hA hAlt (γ s)) =
        frickeGeodesicLength R hg hgenus hA hAlt (T.tau0 j).toLoop
          (nativeFrickeHomeomorph hA hAlt (γ (s + ε j * (2 * Real.pi))))

end LowDimensionalTopology.Unproved.Teichmuller
