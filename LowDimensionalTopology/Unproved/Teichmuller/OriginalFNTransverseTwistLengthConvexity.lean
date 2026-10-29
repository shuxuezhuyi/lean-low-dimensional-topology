/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNTwistCurve
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Unproved convexity of an actual transverse length under angular twist

The selected original geodesic is simple, lies in the actual adjacent-pants
union, and crosses the chosen cuff. Its length is evaluated on the native
curve prescribed by every coordinate of the same positive-length and real-angle
map. The conclusion includes strict convexity, properness as a map to the
real line, and exactly one global minimizer.
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
variable (D₀ : OriginalFNRealization M inc)

/-- The actual transverse length along the based angular twist is strictly
convex and proper, and has a unique global minimum. The added parameter s is
an angle in radians; for the actual cuff length a at t₀, its signed displacement
convention is a*s/(2*pi). The original cuff and transverse curve use their full
periods. The incident pants may coincide. -/
def OriginalFNTransverseTwistLengthConvexity
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ)) : Prop :=
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
  ∀ (t₀ : nativeFrickeImage hA) (j : Fin (3 * g - 3))
    (τ : OriginalClosedGeodesic M),
    Function.Injective (τ.periodic.lift : AddCircle (1 : ℝ) → X) →
    Set.range τ.curve ⊆
      (D₀.component ((inc.copy (j, 0)).1)).val ∪
        Set.range (D₀.cuff j).curve ∪
          (D₀.component ((inc.copy (j, 1)).1)).val →
    Set.range τ.curve ≠ Set.range (D₀.cuff j).curve →
    (Set.range τ.curve ∩ Set.range (D₀.cuff j).curve).Nonempty →
    ∀ γ : C(ℝ, TeichmullerSpace.{0, 0} R),
      (∀ s : ℝ,
        originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
          (nativeFrickeHomeomorph hA hAlt (γ s)) =
            ((originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ t₀).1,
              Function.update
                (originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ t₀).2 j
                ((originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ t₀).2 j + s))) →
      let f : ℝ → ℝ := fun s =>
        frickeGeodesicLength R hg hgenus hA hAlt τ.toLoop
          (nativeFrickeHomeomorph hA hAlt (γ s))
      StrictConvexOn ℝ Set.univ f ∧ IsProperMap f ∧
        ∃! s : ℝ, ∀ r : ℝ, f s ≤ f r

end LowDimensionalTopology.Unproved.Teichmuller
