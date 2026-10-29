module

public import LowDimensionalTopology.Geometry.Fuchsian.PantsCoreClassification
public import LowDimensionalTopology.Geometry.Fuchsian.PantsCoreGeodesicBoundary
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.HyperbolicPairOfPants

/-!
# The original three-end Nielsen core is a hyperbolic pair of pants

The independent finite marked-disc prerequisite is explicit. The hyperbolic
model, open core and actual simple geodesic frontier all use the original group.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- Under the explicitly named independent topological prerequisite, the
actual three-end signature gives a pants witness on its own quotient and core. -/
theorem threeBoundaryOpenCore_isHyperbolicPairOfPants
    (hHard : LowDimensionalTopology.Unproved.Surfaces.ThreeSphericalDiscs)
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {hNE : DiscreteGroups.IsNonElementary H} {hFG : H.FG}
    (h : HasNielsenFuchsianSignature P hNE hFG 0 [] 0 3) :
    Surfaces.IsHyperbolicPairOfPants
      (threeBoundaryQuotientModel P (noElliptic_of_threeBoundarySignature h))
      (threeBoundaryOpenCore P hNE) :=
  ⟨isOpen_threeBoundaryOpenCore P hNE, isCompact_closure_threeBoundaryOpenCore h,
    threeBoundaryOpenCore_homeomorphic_pantsPlanarRegion hHard h,
    threeBoundaryOpenCore_geodesicFrontier h⟩

end LowDimensionalTopology.Geometry.Fuchsian
