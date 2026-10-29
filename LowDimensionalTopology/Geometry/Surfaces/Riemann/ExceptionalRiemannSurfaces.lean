module

public import LowDimensionalTopology.Geometry.Surfaces.Covering.PlaneUniversalCoverClassification
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.SphereUniversalCover

/-!
# Exceptional Riemann surfaces

The four conformal types follow Imayoshi--Taniguchi.
The torus alternative retains an arbitrary genuine period lattice, rather than
selecting one complex structure on the topological torus.
-/

public section
noncomputable section

open scoped OnePoint

namespace LowDimensionalTopology.Geometry.Surfaces

universe u

/-- A surface is exceptional when it is biholomorphic to the sphere, plane,
punctured plane, or a genuine complex period-lattice torus. -/
def RiemannSurface.IsExceptional {X : Type u} [TopologicalSpace X]
    (R : RiemannSurface X) : Prop :=
  RiemannConformallyEquivalent R sphereRiemannSurface ∨
    RiemannConformallyEquivalent R complexPlaneRiemannSurface ∨
      RiemannConformallyEquivalent R puncturedPlaneRiemannSurface ∨
        ∃ b : Module.Basis (Fin 2) ℝ ℂ, ∃ T : ComplexTorusModel b,
          RiemannConformallyEquivalent R T.surface

/-- The definition agrees with the actual sphere and plane alternatives for
any original analytic universal cover. -/
theorem RiemannUniversalCover.isExceptional_iff_sphere_or_plane
    {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}
    (C : RiemannUniversalCover R) :
    R.IsExceptional ↔
      (@RiemannConformallyEquivalent C.space (OnePoint ℂ) C.topology _ C.surface
        sphereRiemannSurface) ∨
      (@RiemannConformallyEquivalent C.space ℂ C.topology _ C.surface
        complexPlaneRiemannSurface) := by
  rw [C.sphere_model_iff_base_sphere, C.plane_model_iff_standard_quotients]
  rfl

end LowDimensionalTopology.Geometry.Surfaces
