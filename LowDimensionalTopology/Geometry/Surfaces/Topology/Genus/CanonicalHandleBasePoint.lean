module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CanonicalHandleWindings

@[expose] public section

noncomputable section

namespace LowDimensionalTopology.Geometry.Surfaces

/-- A specified point of the actual handle model. On the sphere this is the
first unit coordinate vector; on a positive-genus polygon it is its boundary
vertex at parameter zero, viewed in the original quotient. -/
def canonicalHandleBasePoint : (g : ℕ) → CanonicalHandleSurface g
  | 0 => ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ),
      mem_sphere_zero_iff_norm.mpr (by simp [EuclideanSpace.single])⟩
  | g + 1 => canonicalHandleVertex (g + 1) 0

end LowDimensionalTopology.Geometry.Surfaces
