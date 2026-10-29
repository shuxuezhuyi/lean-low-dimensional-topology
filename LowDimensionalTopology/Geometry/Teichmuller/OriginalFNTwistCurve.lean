/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNConditionalHomeomorph

/-!
# The prescribed inverse-coordinate twist curve

The same coordinate homeomorphism pulls a real coordinate line back to an
actual continuous curve of native marked classes. Its complete coordinate
equation fixes every cuff length and every other chosen real twist value.
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

/-- Varying one full real twisting coordinate with all lengths and other
twists fixed gives an actual continuous curve in the native marked space
with its original Fricke topology. The geometric premises are explicit. -/
theorem exists_originalFNTwistCurve
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j)
    (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      R hg hgenus hA hAlt D₀ φ Θ)
    (lengths : Fin (3 * g - 3) → Set.Ioi (0 : ℝ))
    (angles : Fin (3 * g - 3) → ℝ) (j : Fin (3 * g - 3)) :
    letI := nativeFrickeTopology hA
    ∃ γ : C(ℝ, TeichmullerSpace.{0, 0} R),
      ∀ ξ : ℝ,
        originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
          (nativeFrickeHomeomorph hA hAlt (γ ξ)) =
            (lengths, Function.update angles j ξ) := by
  let := nativeFrickeTopology hA
  let F := originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
  let H := (nativeFrickeHomeomorph hA hAlt).trans
    ((originalFNRealCoordinateMap_isHomeomorph R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize).homeomorph F)
  let line : C(ℝ,
      (Fin (3 * g - 3) → Set.Ioi (0 : ℝ)) × (Fin (3 * g - 3) → ℝ)) :=
    ⟨fun ξ => (lengths, Function.update angles j ξ),
      continuous_const.prodMk (continuous_const.update j continuous_id)⟩
  refine ⟨⟨fun ξ => H.symm (line ξ), H.symm.continuous.comp line.continuous⟩, ?_⟩
  intro ξ
  exact H.apply_symm_apply (line ξ)

end LowDimensionalTopology.Geometry.Teichmuller
