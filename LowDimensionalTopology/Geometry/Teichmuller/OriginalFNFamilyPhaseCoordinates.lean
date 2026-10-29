/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic

/-!
# Evaluation of the prescribed original phase at marked coordinates

The actual native inverse may choose a different marked representative. The
explicit original representative-invariance premise identifies its BV phase
with the phase of the given actual marked target.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
variable {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}

/-- At the actual finite coordinates of a marked target, the whole Fricke
phase equals its prescribed original cuff phase, assuming exactly invariance
under the original marked equivalence relation. -/
theorem originalFNFamilyPhase_coordinates
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc) (A : OriginalFNGeometricFamily hA D₀)
    (hrep : ∀ m n : MarkedRiemannSurface.{0, 0} R, MarkedRiemannSurface.Equivalent m n →
      ∀ j, (A m).1.phase j = (A n).1.phase j)
    (m : MarkedRiemannSurface.{0, 0} R) (j : Fin (3 * g - 3)) :
    originalFNFamilyPhase hA hAlt D₀ A
      ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = (A m).1.phase j := by
  classical
  let := nativeFrickeTopology hA
  let t : nativeFrickeImage hA :=
    ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m), ⟨TeichmullerSpace.mk m, rfl⟩⟩
  have ht : t = nativeFrickeHomeomorph hA hAlt (TeichmullerSpace.mk m) := by
    apply Subtype.ext
    exact (nativeFrickeHomeomorph_apply hA hAlt (TeichmullerSpace.mk m)).symm
  have hinv : (nativeFrickeHomeomorph hA hAlt).symm t = TeichmullerSpace.mk m := by
    rw [ht, Homeomorph.symm_apply_apply]
  have hm : MarkedRiemannSurface.Equivalent
      (Quotient.out ((nativeFrickeHomeomorph hA hAlt).symm t)) m := by
    apply (TeichmullerSpace.mk_eq_mk_iff _ m).mp
    exact (Quotient.out_eq' ((nativeFrickeHomeomorph hA hAlt).symm t)).trans hinv
  change (A (Quotient.out ((nativeFrickeHomeomorph hA hAlt).symm t))).1.phase j = _
  exact hrep _ _ hm j

end LowDimensionalTopology.Geometry.Teichmuller
