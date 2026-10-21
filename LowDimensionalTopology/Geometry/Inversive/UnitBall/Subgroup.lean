module
public import LowDimensionalTopology.Geometry.Inversive.UnitBall.NormalForm

/-!
# The subgroup preserving the unit ball.

The inverse-image identity for homeomorphisms shows that unit-ball-preserving elements
of the inversive transformation group form a subgroup.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Filter EuclideanGeometry Set
open scoped Topology OnePoint
variable {n : ℕ}

namespace LowDimensionalTopology.Geometry.Inversive

theorem homeomorph_inv_image_image (h : ExtendedHomeomorph n) (S : Set (ExtendedEuclidean n)) :
    (h⁻¹ : ExtendedHomeomorph n) '' (h '' S) = S := by
  change h.symm '' (h '' S) = S
  rw [Set.image_image]
  simp only [h.symm_apply_apply]
  exact Set.image_id' _

/-- The actual subgroup of the higher-dimensional reflection group preserving the unit ball. -/
def ballPreservingSubgroup (n : ℕ) : Subgroup (GM (n+1)) where
  carrier := {f | PreservesUnitBall (f : ExtendedHomeomorph (n+1))}
  one_mem' := by exact Set.image_id _
  mul_mem' hf hg := hf.mul hg
  inv_mem' {f} hf := by
    change (f.val⁻¹ : ExtendedHomeomorph (n+1)) '' extendedUnitBall = extendedUnitBall
    have he := homeomorph_inv_image_image f.val extendedUnitBall
    rw [hf] at he
    exact he

end LowDimensionalTopology.Geometry.Inversive
