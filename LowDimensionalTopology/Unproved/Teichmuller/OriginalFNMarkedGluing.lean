/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNAnalyticRealCoordinates

/-!
# Unproved marked rigidity and realization of the prescribed coordinates

Both propositions concern the same actual positive-length and chosen-real-angle
map. Its circle phases retain the specified original BV values. Rigidity keeps
the original marking homotopy; realization keeps an actual marked target and
its independent pants, intrinsic cuff copies and marked transport. Neither
proposition asserts the later topological homeomorphism conclusion.
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
variable (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
variable (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))

/-- Equal prescribed positive lengths and the same full real twist values
give an actual analytic target homeomorphism compatible with the original
markings up to homotopy. The geometric-family and exact phase compatibility
premises are retained; no unmarked comparison replaces the marking clause. -/
def OriginalFNMarkedCoordinateRigidity : Prop :=
  OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀ →
  (∀ (m : MarkedRiemannSurface.{0, 0} R)
    (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
    (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
    (j : Fin (3 * g - 3)),
    φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
      ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j) →
  (∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j) →
  ∀ m n : MarkedRiemannSurface.{0, 0} R,
    originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
      ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ =
      originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
        ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk n),
          ⟨TeichmullerSpace.mk n, rfl⟩⟩ →
    ∃ k : m.carrier ≃ₜ n.carrier,
      RiemannAnalyticMap m.surface.toRiemannAtlas n.surface.toRiemannAtlas k ∧
        ContinuousMap.Homotopic ((_root_.toContinuousMap k).comp m.markingMap)
          n.markingMap

/-- Every prescribed positive cuff-length vector and full real twist vector
are realized by an actual original marked target with its own complete cuff
and pants data and an actual marking-compatible intrinsic-copy transport.
The chosen real values are exact, including all integer branch adjustments. -/
def OriginalFNMarkedGluingRealization : Prop :=
  OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀ →
  (∀ (m : MarkedRiemannSurface.{0, 0} R)
    (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
    (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
    (j : Fin (3 * g - 3)),
    φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
      ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j) →
  (∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j) →
  ∀ (lengths : Fin (3 * g - 3) → Set.Ioi (0 : ℝ))
    (angles : Fin (3 * g - 3) → ℝ),
    ∃ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D),
      (∀ j, (D.cuff j).length.toReal = (lengths j : ℝ)) ∧
        Θ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
          ⟨TeichmullerSpace.mk m, rfl⟩⟩ = angles

end LowDimensionalTopology.Unproved.Teichmuller
