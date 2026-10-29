module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannManifold

/-!
# Closed Riemann surfaces

A closed Riemann surface is a compact connected Hausdorff complex analytic
surface. The inherited charts take values in open subsets of the complex plane,
so these are surfaces without boundary.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Surfaces

universe u

/-- A compact Riemann surface, with the original complex atlas and topology. -/
structure ClosedRiemannSurface (X : Type u) [TopologicalSpace X]
    extends RiemannSurface X where
  compactSpace : CompactSpace X

namespace ClosedRiemannSurface

variable {X : Type u} [TopologicalSpace X]

/-- Read an existing compact Riemann surface as a closed Riemann surface. -/
def ofRiemannSurface (R : RiemannSurface X) [CompactSpace X] : ClosedRiemannSurface X where
  toRiemannSurface := R
  compactSpace := inferInstance

@[simp]
theorem ofRiemannSurface_toRiemannSurface (R : RiemannSurface X) [CompactSpace X] :
    (ofRiemannSurface R).toRiemannSurface = R := rfl

/-- The connectedness in the surface definition already supplies a point. -/
theorem nonempty (R : ClosedRiemannSurface X) : Nonempty X :=
  R.connectedSpace.toNonempty

/-- Countability follows from the existing Riemann surface theorem. -/
theorem secondCountableTopology (R : ClosedRiemannSurface X) : SecondCountableTopology X :=
  R.toRiemannSurface.secondCountableTopology

/-- The inherited complex atlas is an analytic Mathlib manifold. -/
theorem isManifold (R : ClosedRiemannSurface X) :
    let := R.toRiemannAtlas.toChartedSpace
    IsManifold 𝓘(ℂ) ω X :=
  R.toRiemannAtlas.isManifold

/-- A compact connected Hausdorff complex analytic manifold gives a closed Riemann surface. -/
def ofManifold (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [T2Space X] [ConnectedSpace X] [CompactSpace X] :
    ClosedRiemannSurface X :=
  ofRiemannSurface (RiemannSurface.ofManifold X)

end ClosedRiemannSurface

/-- Closedness adds exactly compactness to the existing Riemann surface data. -/
theorem nonempty_closedRiemannSurface_iff (X : Type u) [TopologicalSpace X] :
    Nonempty (ClosedRiemannSurface X) ↔ Nonempty (RiemannSurface X) ∧ CompactSpace X := by
  constructor
  · rintro ⟨R⟩
    exact ⟨⟨R.toRiemannSurface⟩, R.compactSpace⟩
  · rintro ⟨⟨R⟩, hcompact⟩
    exact ⟨{ toRiemannSurface := R, compactSpace := hcompact }⟩

end LowDimensionalTopology.Geometry.Surfaces
