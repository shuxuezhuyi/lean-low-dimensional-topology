module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CompactGenusTypes

@[expose] public section

noncomputable section

namespace LowDimensionalTopology.Geometry.Surfaces

/-- An arbitrary genuine universal cover is conformally the sphere exactly
when its original base is conformally the sphere. Both directions use old
native theorems without additional topology or compactness assumptions. -/
theorem RiemannUniversalCover.sphere_model_iff_base_sphere
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (C : RiemannUniversalCover R) :
    @RiemannConformallyEquivalent C.space (OnePoint ℂ) C.topology _ C.surface
      sphereRiemannSurface ↔ RiemannConformallyEquivalent R sphereRiemannSurface := by
  rw [C.sphere_model_iff_homeomorphic_sphere,
    riemannSurface_conformallyEquivalent_sphere_iff_homeomorphic_sphere R]

end LowDimensionalTopology.Geometry.Surfaces
