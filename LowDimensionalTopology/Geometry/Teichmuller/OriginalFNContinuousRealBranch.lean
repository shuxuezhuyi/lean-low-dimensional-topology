/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNContinuousPhase
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Continuous real branches of the prescribed original cuff phases

The basepoint is an actual original Fricke point. At that point each real
angle is fixed to the principal argument of the actual phase. The existing
circle exponential covering gives global continuous angles in radians; their
exponentials retain the same prescribed BV phase at every marked target.
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

/-- One normalized real branch on the entire original Fricke image, with
the exact circle-exponential equation and actual marked-target BV values.
Simple connectivity comes from the independent quadratic Teichmüller
parametrization and original QC topology. -/
theorem exists_originalFNContinuousRealBranch
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc)
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (t₀ : nativeFrickeImage hA) :
    ∃ (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
      (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ)),
      (∀ j, Θ t₀ j = Complex.arg (φ t₀ j)) ∧
      (∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j) ∧
      ∀ (m : MarkedRiemannSurface.{0, 0} R)
        (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
        (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
        (j : Fin (3 * g - 3)),
        Circle.exp (Θ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
          ⟨TeichmullerSpace.mk m, rfl⟩⟩ j) = D.phase j := by
  classical
  obtain ⟨φ, hφ⟩ := exists_originalFNContinuousPhase R hg hgenus hA hAlt D₀ hU
  have hdomain := nativeFrickeImage_domain R hg hgenus hA hAlt
  let : SimplyConnectedSpace (nativeFrickeImage hA) := hdomain.2.2.1
  let : LocallyPathConnectedSpace (nativeFrickeImage hA) :=
    hdomain.1.locallyPathConnectedSpace
  have hex : ∀ j : Fin (3 * g - 3), ∃ θ : C(nativeFrickeImage hA, ℝ),
      θ t₀ = Complex.arg (φ t₀ j) ∧ Circle.exp ∘ θ = fun t => φ t j := by
    intro j
    let φj : C(nativeFrickeImage hA, Circle) :=
      ⟨fun t => φ t j, (continuous_apply j).comp φ.continuous⟩
    obtain ⟨θ, hθ, _hunique⟩ :=
      Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts φj t₀
        (Complex.arg (φj t₀)) (Circle.exp_arg (φj t₀))
    exact ⟨θ, hθ⟩
  let θ : Fin (3 * g - 3) → C(nativeFrickeImage hA, ℝ) := fun j => (hex j).choose
  have hθ (j : Fin (3 * g - 3)) := (hex j).choose_spec
  let Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ) :=
    ⟨fun t j => θ j t, continuous_pi fun j => (θ j).continuous⟩
  refine ⟨φ, Θ, (fun j => (hθ j).1), (fun j => (hθ j).2), ?_⟩
  intro m N D transport j
  exact (congrFun (hθ j).2
    ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
      ⟨TeichmullerSpace.mk m, rfl⟩⟩).trans (hφ m N D transport j)

end LowDimensionalTopology.Geometry.Teichmuller
