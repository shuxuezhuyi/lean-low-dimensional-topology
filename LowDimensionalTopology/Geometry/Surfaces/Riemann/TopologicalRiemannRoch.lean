module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.HolomorphicQuadraticDifferential
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannRoch
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge

/-!
# Riemann–Roch and quadratic differentials in the handle genus

The proved presentation of the actual canonical handle surface identifies the
analytic genus of the original complex atlas with its topological handle genus.
This removes the comparison hypothesis from the divisor and dimension formulas.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Riemann–Roch for every actual canonical divisor, stated with the handle genus. -/
theorem riemannRoch (R : ClosedRiemannSurface X)
    {K : Jacobians.Divisor X} (hK : R.IsCanonicalDivisor K) {g : ℕ}
    (hgenus : R.HasGenus g) :
    let := R.t2Space
    let := R.compactSpace
    let := R.connectedSpace
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    ∀ D : Jacobians.Divisor X,
      (Jacobians.lDim D : ℤ) - (Jacobians.lDim (K - D) : ℤ) =
        Jacobians.Divisor.deg X D + 1 - (g : ℤ) := by
  exact R.riemannRoch_of_isCanonicalDivisor hK (R.genusComparison g) hgenus

/-- Every actual canonical divisor has degree `2g - 2` and linear-system dimension `g`. -/
theorem canonicalDivisor_degree_and_dimension (R : ClosedRiemannSurface X)
    {K : Jacobians.Divisor X} (hK : R.IsCanonicalDivisor K) {g : ℕ}
    (hgenus : R.HasGenus g) :
    let := R.t2Space
    let := R.compactSpace
    let := R.connectedSpace
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    Jacobians.Divisor.deg X K = 2 * (g : ℤ) - 2 ∧ Jacobians.lDim K = g := by
  exact R.degree_of_isCanonicalDivisor hK (R.genusComparison g) hgenus

/-- Quadratic differentials on the original atlas have complex dimension `3g - 3`
and real dimension `6g - 6` when the handle genus exceeds one. -/
theorem holomorphicQuadraticDifferential_finrank (R : ClosedRiemannSurface X) {g : ℕ}
    (hgenus : R.HasGenus g) (hg : 1 < g) :
    Module.finrank ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) = 3 * g - 3 ∧
      Module.finrank ℝ (HolomorphicQuadraticDifferential R.toRiemannAtlas) = 6 * g - 6 := by
  exact R.finrank_holomorphicQuadraticDifferential (R.genusComparison g) hgenus hg

end LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface
