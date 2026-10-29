module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.AnalyticAutomorphismGroup
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge

/-!
# Hurwitz's bound in the topological handle genus

The proved canonical handle presentation removes the comparison input from
finiteness and the sharp bound for the actual analytic automorphism group.
The analytic Hurwitz proof is due to Wu Xiaobin, fixed upstream commit
1c0d5473c020b66ed5106331a38a61536760b9b2, Apache-2.0.
-/

@[expose] public section

namespace LowDimensionalTopology.Geometry.Surfaces

universe u

/-- The actual conformal automorphism group of a higher-genus closed Riemann
surface is finite and has at most `84 * (g - 1)` elements. -/
theorem ClosedRiemannSurface.automorphismGroup_finite_card_le
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) :
    Finite R.toRiemannAtlas.analyticAutomorphismSubgroup ∧
      Nat.card R.toRiemannAtlas.analyticAutomorphismSubgroup ≤ 84 * (g - 1) := by
  exact R.analyticAutomorphism_finite_card_le hg hgenus (canonicalHandleGroupPresentation g)

end LowDimensionalTopology.Geometry.Surfaces
