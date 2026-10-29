module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeComplexMinimizers
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# The missing straight-line bridge for the actual marked quotient

The geometric input is that Teichmüller existence and uniqueness make the
original Teichmüller space a straight-line space, including the equality case
of the triangle inequality. This proposition records that concrete bridge
for the existing full-log metric. It does not contain an action, an invariant
line, or a minimizing-point claim. No proof of the bridge is supplied here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Set
open LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Teichmuller
open LiZhongQC

universe u

/-- Straight lines, their uniqueness, and metric betweenness on the original full-log quotient. -/
def OriginalTeichmullerStraightLineGeometry
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  letI := R.toRiemannAtlas.isManifold
  letI := R.t2Space
  letI := R.connectedSpace
  letI := R.compactSpace
  letI := QCBookMetric.metricSpace hg (R.hasSourceGenus hgenus)
  (∀ p q : TeichSpace X, p ≠ q →
    ∃ ℓ : ℝ → TeichSpace X,
      Isometry ℓ ∧ ℓ 0 = p ∧ ℓ (dist p q) = q) ∧
  (∀ (ℓ k : ℝ → TeichSpace X), Isometry ℓ → Isometry k →
    ∀ p q : TeichSpace X, p ≠ q →
      p ∈ range ℓ → q ∈ range ℓ → p ∈ range k → q ∈ range k →
        range ℓ = range k) ∧
  (∀ ℓ : ℝ → TeichSpace X, Isometry ℓ →
    ∀ (s t : ℝ) (q : TeichSpace X),
      dist (ℓ s) q + dist q (ℓ t) = dist (ℓ s) (ℓ t) → q ∈ range ℓ)

end LowDimensionalTopology.Unproved.Teichmuller
