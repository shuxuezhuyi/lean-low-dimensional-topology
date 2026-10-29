module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.FiniteRetainedBoundaryData

/-!
# Finite conformal deletion presentations of an original surface

A presentation retains the given surface and its designated open interior.
An actual homeomorphism from finite deletion data agrees pointwise with the
biholomorphic map of the original interior atlases.
-/

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

/-- A compact conformal deletion presentation with the same retained boundary
and a biholomorphic identification of the given original interiors. -/
def HasFiniteRetainedConformalPresentation
    {S : Type} [TopologicalSpace S] (U : TopologicalSpace.Opens S)
    (A : RiemannAtlas U) : Prop :=
  ∃ X : Type, ∃ tX : TopologicalSpace X,
    letI := tX
    ∃ (R : ClosedRiemannSurface X) (D : FiniteRetainedBoundaryData R)
      (E : D.Carrier ≃ₜ S) (e : D.interiorOpen ≃ₜ U),
        (∀ x, E (D.interiorToCarrier x) = (e x : S)) ∧
        RiemannAnalyticMap D.interiorAtlas A e ∧
        RiemannAnalyticMap A D.interiorAtlas e.symm

end LowDimensionalTopology.Geometry.Surfaces
