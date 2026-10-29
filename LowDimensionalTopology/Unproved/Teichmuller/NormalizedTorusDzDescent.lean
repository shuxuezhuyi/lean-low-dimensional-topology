module

public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.NormalizedTorusModel
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.HolomorphicQuadraticDifferential

/-!
# A concrete invariant one-differential descent obligation

This defines a Prop, not an axiom or a proof. The fixed actual normalized torus
cover should descend dz to a holomorphic (1,0) coefficient family in its
unchanged original preferred charts. Neither a metric, area normalization,
Beltrami tangent nor WP formula is assumed.

This is an independent classical differential-descent prerequisite.
Its witness retains the original chart transition law.
The original atlas contains actual Mobius quotient charts; no chart derivative
is declared to be one.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces

/-- The fixed actual translation cover descends dz. The witness belongs to the
existing native (1,0) coefficient submodule, is holomorphic on every actual
preferred chart target, and pulls back to the literal plane differential dz. -/
def NormalizedTorusDzDescent (τ : ℍ) : Prop :=
  letI := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
  ∃ η : ↥(LiZhongQC.diffFamilySubmodule ComplexTorusCarrier 1 0),
    (∀ x : ComplexTorusCarrier,
      DifferentiableOn ℂ (η.val x) (chartAt ℂ x).target) ∧
    ∀ (x : ComplexTorusCarrier) (z : ℂ),
      (normalizedTorusModel τ).projection z ∈ (chartAt ℂ x).source →
        η.val x ((chartAt ℂ x) ((normalizedTorusModel τ).projection z)) *
          deriv ((chartAt ℂ x) ∘ (normalizedTorusModel τ).projection) z = 1

end LowDimensionalTopology.Unproved.Teichmuller
