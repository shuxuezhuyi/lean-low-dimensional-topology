/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.GeodesicReflections
@[expose] public section
noncomputable section
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- A genuine geometric reflection bundled as a native hyperbolic isometry. -/
def halfPlaneLineReflectionIsometry (L : HalfPlaneLine) : ℍ ≃ᵢ ℍ where
  toEquiv := Function.Involutive.toPerm L.reflection L.reflection_involutive
  isometry_toFun := L.reflection_isometry

end LowDimensionalTopology.Geometry.Hyperbolic
