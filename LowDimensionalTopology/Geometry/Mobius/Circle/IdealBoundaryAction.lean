module
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyIdealBoundary
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Mobius.FractionalLinear
public import LowDimensionalTopology.Geometry.Mobius.ReflectionEquivalence

/-!
# Möbius transformations on the ideal boundary of the half-plane.

The ideal boundary is the closed upper half-plane minus its interior in the extended
complex plane. A Möbius transformation preserving the open half-plane preserves this
boundary, and conjugation transports the images of boundary subsets.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped OnePoint Pointwise UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Mobius

/-- The actual ideal boundary is the difference between the closed and open half-plane. -/
theorem stableAxis_halfPlaneIdealBoundary_eq :
    Hyperbolic.halfPlaneIdealBoundary = closure Hyperbolic.openHalfPlaneSet \ Hyperbolic.openHalfPlaneSet := by
  rw [Hyperbolic.closure_openHalfPlaneSet]
  ext p
  induction p using OnePoint.rec with
  | infty => simp [Hyperbolic.halfPlaneIdealBoundary, Hyperbolic.closedHalfPlaneSet, Hyperbolic.openHalfPlaneSet]
  | coe z =>
    simp only [Hyperbolic.coe_mem_halfPlaneIdealBoundary, Set.mem_sdiff,
      Hyperbolic.coe_mem_closedHalfPlaneSet, Hyperbolic.coe_mem_openHalfPlaneSet]
    constructor
    · intro h
      simp [h]
    · intro h
      exact le_antisymm (le_of_not_gt h.2) h.1

/-- Actual conjugation transports images of arbitrary boundary subsets. -/
theorem stableAxis_conjugate_image (q f : complexMobiusGroup) (S : Set ExtendedComplex) :
    (q * f * q⁻¹).val '' (q.val '' S) = q.val '' (f.val '' S) := by
  rw [image_image, image_image]
  congr 1
  funext x
  change q.val (f.val (q.val.symm (q.val x))) = q.val (f.val x)
  rw [Equiv.symm_apply_apply]

/-- An actual Mobius map preserving the open half-plane preserves its genuine ideal boundary. -/
theorem stableAxis_mobius_boundary_preserved (f : complexMobiusGroup)
    (hH : f.val '' Hyperbolic.openHalfPlaneSet = Hyperbolic.openHalfPlaneSet) :
    f.val '' Hyperbolic.halfPlaneIdealBoundary = Hyperbolic.halfPlaneIdealBoundary := by
  let F := mobiusBoundaryHomeomorph f
  change F '' Hyperbolic.halfPlaneIdealBoundary = Hyperbolic.halfPlaneIdealBoundary
  rw [stableAxis_halfPlaneIdealBoundary_eq, image_sdiff F.injective, F.image_closure]
  rw [show F '' Hyperbolic.openHalfPlaneSet = Hyperbolic.openHalfPlaneSet from hH]

end LowDimensionalTopology.Geometry.Mobius
