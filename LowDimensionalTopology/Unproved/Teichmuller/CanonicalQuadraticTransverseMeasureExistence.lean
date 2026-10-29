module

public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalQuadraticFoliation

/-!
# Canonical transverse measures of an actual quadratic differential

The same original differential fixes the local flat-coordinate interval values.
The proposition asks for actual measures on every transverse arc, with their
full parameter, restriction and holonomy compatibility.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller
open LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Teichmuller

variable {X : Type} [TopologicalSpace X]

/-- Canonical transverse measures for the actual horizontal foliation of a nonzero differential. -/
def CanonicalQuadraticTransverseMeasureExistence (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) : Prop :=
  q ≠ 0 → ∀ A : SingularFoliationAtlas R, IsHorizontalFoliationAtlasOf R q A →
    ∃ μ : TransverseInvariantMeasure A,
      HasCanonicalQuadraticTransverseMeasure R q A μ ∧
        (⟨A, μ⟩ : SingularMeasuredFoliation R).IsNondegenerate

end LowDimensionalTopology.Unproved.Teichmuller
