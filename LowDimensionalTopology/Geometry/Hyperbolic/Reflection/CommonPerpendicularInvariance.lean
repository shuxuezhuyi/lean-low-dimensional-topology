module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ReflectionProductTraces
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.SaccheriQuadrilaterals

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Both reflections preserve a common perpendicular, so their actual product does too. -/
theorem reflectionProductSL_preserves_perpendicular
    (L M N : HalfPlaneLine) (p q : ℍ)
    (hp : L.OrthogonalAt N p) (hq : M.OrthogonalAt N q) :
    (reflectionProductSL L M • · : ℍ → ℍ) '' N.carrier = N.carrier := by
  have hact : (reflectionProductSL L M • · : ℍ → ℍ) =
      L.reflection ∘ M.reflection := funext (reflectionProductSL_action L M)
  rw [hact, image_comp, M.reflection_image_of_orthogonalAt N q hq,
    L.reflection_image_of_orthogonalAt N p hp]

end LowDimensionalTopology.Geometry.Hyperbolic
