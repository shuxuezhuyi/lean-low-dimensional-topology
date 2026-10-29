/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNFamilyPhaseCoordinates

/-!
# A continuous family of the prescribed original cuff phases

The explicit unproved geometric-family proposition supplies its literal
analytic BV phases. Their continuity and the original marked-coordinate
evaluation give one continuous map retaining every actual target realization.
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

/-- The concrete geometric-family and analyticity premise supplies a continuous
map whose actual marked-coordinate values are the prescribed BV cuff phases
for every admissible realization on every original target model. -/
theorem exists_originalFNContinuousPhase
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc)
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀) :
    ∃ φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle),
      ∀ (m : MarkedRiemannSurface.{0, 0} R)
        (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
        (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
        (j : Fin (3 * g - 3)),
        φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
          ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j := by
  classical
  rcases hU with ⟨A, hrep, hchoices, hreg⟩
  have hcont : Continuous (fun t : nativeFrickeImage hA =>
      originalFNFamilyPhase hA hAlt D₀ A t) := by
    apply continuous_pi
    intro j
    apply continuous_induced_rng.mpr
    have hc := (hreg j).continuousOn.domRestrict
    exact hc.congr (fun t => dite_eq_left t.property)
  let φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle) :=
    ⟨fun t => originalFNFamilyPhase hA hAlt D₀ A t, hcont⟩
  refine ⟨φ, ?_⟩
  intro m N D transport j
  calc
    φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = (A m).1.phase j :=
      originalFNFamilyPhase_coordinates hA hAlt D₀ A hrep m j
    _ = D.phase j := hchoices m N D transport j

end LowDimensionalTopology.Geometry.Teichmuller
