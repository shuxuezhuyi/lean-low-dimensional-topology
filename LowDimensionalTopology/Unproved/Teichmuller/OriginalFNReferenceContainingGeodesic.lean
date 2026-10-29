module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic

/-!
# A reference FN realization retaining one prescribed original geodesic

The reference data consist of the complete indexed decomposition, intrinsic
cuff copies and actual shortest seams on the same original hyperbolic model.
One labelled cuff is the prescribed geodesic itself, retaining its orientation
and full period. No target family or signed deformation identity is asserted.
-/

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller

/-- One complete reference FN realization has the prescribed original
geodesic as an exactly equal labelled cuff. Existence is left unproved. -/
def OriginalFNReferenceContainingGeodesic
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (g : ℕ) (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (q : OriginalClosedGeodesic M) : Prop :=
  ∃ (inc : OriginalFNCuffIncidence g) (D0 : OriginalFNRealization M inc)
    (j : Fin (3 * g - 3)), D0.cuff j = q

end LowDimensionalTopology.Unproved.Teichmuller
