module

public import LowDimensionalTopology.Geometry.Surfaces.SingularMeasuredFoliation
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Closed
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S24_QuasiFuchsian

/-!
# Pseudo-Anosov homeomorphisms of the original oriented surface

The invariant measured foliations use the original real smooth structure.
Their actual transverse measures are atomless and have full support.
The homeomorphism scales these measures by reciprocal positive factors.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

universe u
variable {X : Type u} [TopologicalSpace X]

/-- An oriented surface homeomorphism preserving a nondegenerate transverse measured pair. -/
def IsPseudoAnosov (R : ClosedRiemannSurface X) (f : X ≃ₜ X) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  LiZhongQC.IsOrientationPreservingRS f ∧
    ∃ F G : SingularMeasuredFoliation R,
      F.IsNondegenerate ∧ G.IsNondegenerate ∧ AreTransverseMeasuredFoliations F G ∧
        ∃ lam : ℝ, 1 < lam ∧
          IsMeasuredFoliationHomothety F f lam ∧ IsMeasuredFoliationHomothety G f lam⁻¹

end LowDimensionalTopology.Geometry.Surfaces
