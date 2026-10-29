module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic

/-!
# A holomorphic disk in a proper scalar analytic zero set

This is an independent concrete classical prerequisite in finite complex
Cartesian space. It concerns an arbitrary scalar analytic function and
contains no vector-valued injectivity or Jacobian conclusion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set

namespace LowDimensionalTopology.Unproved.SeveralComplexVariables

/-- A nonempty proper scalar analytic zero set in complex dimension at least
 two contains an actual injective holomorphic disk. The disk's image lies in
 the same original open domain and zero set. -/
def HolomorphicZeroSetContainsDisk : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (D : Set (Fin n → ℂ)),
    IsOpen D → IsPreconnected D → ∀ (g : (Fin n → ℂ) → ℂ),
      AnalyticOnNhd ℂ g D →
      (∃ z ∈ D, g z = 0) →
      (∃ z ∈ D, g z ≠ 0) →
      ∃ γ : ℂ → (Fin n → ℂ),
        AnalyticOnNhd ℂ γ (Metric.ball (0 : ℂ) 1) ∧
        Set.InjOn γ (Metric.ball (0 : ℂ) 1) ∧
        Set.MapsTo γ (Metric.ball (0 : ℂ) 1) {z | z ∈ D ∧ g z = 0}

end LowDimensionalTopology.Unproved.SeveralComplexVariables
