module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticFoliationAtlas
public import LowDimensionalTopology.Unproved.Teichmuller.CanonicalQuadraticTransverseMeasureExistence

/-!
# Conditional canonical measured foliations of the same differential

The original differential supplies an actual aligned raw atlas. The explicit
measure-existence proposition then gives its canonical nondegenerate measure.
The same construction applies to the negative differential on the same surface.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
open LowDimensionalTopology.Unproved.Teichmuller

variable {X : Type} [TopologicalSpace X]

/-- The actual raw atlas and its canonical transverse measure form a nondegenerate foliation. -/
theorem exists_canonicalQuadraticMeasuredFoliation (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    (hμ : CanonicalQuadraticTransverseMeasureExistence R q) :
    ∃ F : SingularMeasuredFoliation R,
      IsHorizontalFoliationAtlasOf R q F.atlas ∧
        HasCanonicalQuadraticTransverseMeasure R q F.atlas F.transverse ∧
          F.IsNondegenerate := by
  obtain ⟨A, hA⟩ := exists_horizontalFoliationAtlasOf R q hq
  obtain ⟨μ, hcanonical, hnondegenerate⟩ := hμ hq A hA
  exact ⟨⟨A, μ⟩, hA, hcanonical, hnondegenerate⟩

/-- The canonical objects of the differential and its negative use the same original surface. -/
theorem exists_canonicalQuadraticMeasuredFoliation_pair (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    (hμq : CanonicalQuadraticTransverseMeasureExistence R q)
    (hμneg : CanonicalQuadraticTransverseMeasureExistence R (-q)) :
    ∃ F G : SingularMeasuredFoliation R,
      IsHorizontalFoliationAtlasOf R q F.atlas ∧
        HasCanonicalQuadraticTransverseMeasure R q F.atlas F.transverse ∧
          F.IsNondegenerate ∧
            IsHorizontalFoliationAtlasOf R (-q) G.atlas ∧
              HasCanonicalQuadraticTransverseMeasure R (-q) G.atlas G.transverse ∧
                G.IsNondegenerate := by
  obtain ⟨F, hF, hcanonicalF, hnondegenerateF⟩ :=
    exists_canonicalQuadraticMeasuredFoliation R q hq hμq
  obtain ⟨G, hG, hcanonicalG, hnondegenerateG⟩ :=
    exists_canonicalQuadraticMeasuredFoliation R (-q) (neg_ne_zero.mpr hq) hμneg
  exact ⟨F, G, hF, hcanonicalF, hnondegenerateF, hG, hcanonicalG, hnondegenerateG⟩

end LowDimensionalTopology.Geometry.Teichmuller
