module

public import LowDimensionalTopology.Geometry.Teichmuller.LiteralKobayashiAxioms

/-!
# Hyperbolicity and completeness for the literal Kobayashi distance

On the original connected manifold, the chain infimum is finite, and its
real expression is the distance used in both predicates. Completeness
uses the sequence characterization of metric completeness. Neither
predicate installs a metric-space instance or changes the manifold topology.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.KobayashiCore

universe u

variable {d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) ω M]

/-- Hyperbolicity is nondegeneracy of the same finite real chain distance. -/
def IsKobayashiHyperbolic [ConnectedSpace M] : Prop :=
  ∀ p q : M, (kobayashiEDist (d := d) p q).toReal = 0 ↔ p = q

/-- Complete hyperbolicity means hyperbolicity and convergence, in the same distance,
of every sequence that is Cauchy in that distance. -/
def IsKobayashiComplete [ConnectedSpace M] : Prop :=
  IsKobayashiHyperbolic (d := d) (M := M) ∧
    ∀ s : ℕ → M,
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
        (kobayashiEDist (d := d) (s m) (s n)).toReal < ε) →
      ∃ p : M, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
        (kobayashiEDist (d := d) (s n) p).toReal < ε

end LowDimensionalTopology.Geometry.Teichmuller.KobayashiCore
