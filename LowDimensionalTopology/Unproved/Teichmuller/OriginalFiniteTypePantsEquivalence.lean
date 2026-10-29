module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalFinitePantsData
public import LowDimensionalTopology.Geometry.Surfaces.Topology.FiniteRetainedConformalPresentation

/-!
# The original finite-type and completed-pants equivalence

The negative-Euler range uses actual rational singular-homology cardinal
ranks on the original carrier, independently of a finite presentation.
The finite-type predicate retains its original interior complex atlas.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

/-- The actual rational singular homology of the original topological carrier. -/
def originalRationalHomology (S : Type) [TopologicalSpace S] (i : ℕ) : ModuleCat.{0} ℚ :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℚ) i).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of S))

/-- Negative Euler range by cardinal Betti ranks, permitting infinite rank. -/
def OriginalNegativeEulerBetti (S : Type) [TopologicalSpace S] : Prop :=
  Module.rank ℚ (originalRationalHomology S 0) + Module.rank ℚ (originalRationalHomology S 2) <
    Module.rank ℚ (originalRationalHomology S 1)

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces

/-- Finite retained conformal type is equivalent to a finite completed-pants
cut on the same original complete geodesic-boundary metric without funnel ends. -/
def OriginalFiniteTypePantsEquivalence : Prop :=
  ∀ (S : Type) (tS : TopologicalSpace S),
    letI := tS
    ∀ (U : TopologicalSpace.Opens S) (A : RiemannAtlas U)
      (G : OriginalCompleteGeodesicBoundaryMetric U A),
      OriginalNegativeEulerBetti S → OriginalHasNoFunnelEnds G →
        (HasFiniteRetainedConformalPresentation U A ↔ HasOriginalFiniteCompletedPants G)

end LowDimensionalTopology.Unproved.Teichmuller
