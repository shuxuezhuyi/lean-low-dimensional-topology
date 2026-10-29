module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.TubularGeodesicNeighborhood
public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton

/-!
# The intrinsic distance to the complete trace preimage

The actual original-atlas full rectifiable distance to one geodesic trace
is compared with distances to all its lifts in the prescribed real conjugate
covering. No angular width, embedded collar or geometric deformation is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane ENNReal

namespace LowDimensionalTopology.Unproved.Teichmuller
open LowDimensionalTopology.Geometry.Surfaces

/-- The full intrinsic distance to this actual trace is computed by distances
to its complete preimage in the prescribed adjusted half-plane covering. -/
def OriginalGeodesicIntrinsicLiftDistance
    {X : Type} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M)
    (Q : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Prop :=
  let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
  ∀ z : ℍ, q.distanceToTrace (pQ z) =
    ⨅ w : {w : ℍ // pQ w ∈ Set.range q.curve},
      ENNReal.ofReal (dist z w.val)

end LowDimensionalTopology.Unproved.Teichmuller
