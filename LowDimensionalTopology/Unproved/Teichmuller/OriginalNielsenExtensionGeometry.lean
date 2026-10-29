module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalNielsenExtension

/-!
# Existence, uniqueness and the independent finite-area region identity

The existence statement starts with the given original bordered surface.
Uniqueness compares actual extensions over every point of that same surface.
The separate region identity concerns its concrete invariant convex lift.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Fuchsian Set

/-- Existence of an actual extension over every original bordered input. -/
def OriginalBorderedNielsenExtensionExistence : Prop :=
  ∀ (S : Type) (tS : TopologicalSpace S),
    letI := tS
    ∀ (U : TopologicalSpace.Opens S) (A : RiemannAtlas U)
      (input : OriginalBorderedHyperbolicInput U A),
      ∃ (Y : Type) (tY : TopologicalSpace Y),
        letI := tY
        ∃ (RY : RiemannSurface Y) (M : HyperbolicSurfaceModel RY),
          Nonempty (OriginalNielsenExtension input M)

/-- Uniqueness of the analytic isometry over every point of the original surface. -/
def OriginalBorderedNielsenExtensionUniqueness : Prop :=
  ∀ (S : Type) (tS : TopologicalSpace S),
    letI := tS
    ∀ (U : TopologicalSpace.Opens S) (A : RiemannAtlas U)
      (input : OriginalBorderedHyperbolicInput U A),
      ∀ (Y : Type) (tY : TopologicalSpace Y),
        letI := tY
        ∀ (RY : RiemannSurface Y) (M : HyperbolicSurfaceModel RY)
          (D : OriginalNielsenExtension input M),
          ∀ (Z : Type) (tZ : TopologicalSpace Z),
            letI := tZ
            ∀ (RZ : RiemannSurface Z) (N : HyperbolicSurfaceModel RZ)
              (E : OriginalNielsenExtension input N),
              ∃! J : Y ≃ₜ Z, OriginalNielsenExtensionComparison D E J

/-- Identification of the actual finite-area convex region with the closed Nielsen core. -/
def OriginalFiniteAreaGeodesicRegionCore : Prop :=
  ∀ (Y : Type) (tY : TopologicalSpace Y),
    letI := tY
    ∀ (RY : RiemannSurface Y) (M : HyperbolicSurfaceModel RY)
      (D : OriginalGeodesicBoundaryRegion M),
      D.region = closure
        (fuchsianNielsenCore (originalHyperbolicDiscGroup M) D.non_elementary)

end LowDimensionalTopology.Unproved.Teichmuller
