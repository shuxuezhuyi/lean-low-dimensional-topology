module

public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Connected.Basic

/-!
# Stein's conditions for a finite-dimensional complex manifold

The holomorphic hull uses all globally holomorphic scalar functions.
Local coordinates are supplied by globally holomorphic functions and an
actual local biholomorphism. Countable compact covering is retained
explicitly. No Stein property of a particular manifold is asserted here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.ComplexManifold

/-- The normalized holomorphic hull, using all global holomorphic scalar
functions that have norm at most one on the original set. -/
def holomorphicHull {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Fin n → ℂ) M] (K : Set M) : Set M :=
  {p | ∀ f : M → ℂ, ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ) ω f →
    (∀ x ∈ K, ‖f x‖ ≤ 1) → ‖f p‖ ≤ 1}

/-- The four Stein conditions: countable compact covering, compact
holomorphic hulls, point separation and local coordinates consisting of
restrictions of global holomorphic functions. The coordinate condition
retains an actual local homeomorphism with holomorphic inverse. -/
def IsSteinManifold (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (Fin n → ℂ) M] [IsManifold 𝓘(ℂ, Fin n → ℂ) ω M] : Prop :=
  let I := 𝓘(ℂ, Fin n → ℂ)
  SigmaCompactSpace M ∧
  (∀ K : Set M, IsCompact K → IsCompact (holomorphicHull (n := n) K)) ∧
  (∀ p q : M, p ≠ q →
    ∃ f : M → ℂ, ContMDiff I 𝓘(ℂ) ω f ∧ f p ≠ f q) ∧
  (∀ p : M, ∃ F : M → Fin n → ℂ,
    ContMDiff I I ω F ∧
    ∃ e : OpenPartialHomeomorph M (Fin n → ℂ),
      p ∈ e.source ∧ EqOn F e e.source ∧ ContMDiffOn I I ω e.symm e.target)

end LowDimensionalTopology.Geometry.ComplexManifold
