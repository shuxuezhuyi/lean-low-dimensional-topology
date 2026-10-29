/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNAnalyticRealCoordinates
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Real twist parameters measured in original cuff length

The original positive cuff length scales the same full real angular branch
by 1/(2*pi). Positivity of that length gives the inverse angle formula.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
variable (D₀ : OriginalFNRealization M inc)

/-- The same real angle scaled by the actual original cuff length over 2*pi. -/
def originalFNRescaledRealTwistCoordinate
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ)) :
    nativeFrickeImage hA → (Fin (3 * g - 3) → ℝ) :=
  fun t j => (((originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ t).1 j : ℝ) /
    (2 * Real.pi)) * Θ t j

/-- The positive original cuff length recovers the same full real angle. -/
theorem originalFNRescaledRealTwistCoordinate_recoverAngle
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (t : nativeFrickeImage hA) (j : Fin (3 * g - 3)) :
    ((2 * Real.pi) /
      ((originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ t).1 j : ℝ)) *
        originalFNRescaledRealTwistCoordinate R hg hgenus hA hAlt D₀ Θ t j = Θ t j := by
  have hℓ := ne_of_gt ((originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ t).1 j).property
  dsimp only [originalFNRescaledRealTwistCoordinate]
  field_simp [hℓ, Real.pi_ne_zero]

end LowDimensionalTopology.Geometry.Teichmuller
