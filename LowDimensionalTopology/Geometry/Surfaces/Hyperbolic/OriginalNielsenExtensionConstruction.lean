module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalNielsenExtensionGeometry
public import Mathlib.Logic.Equiv.Set

/-!
# The original image and unique core comparison of a Nielsen extension

The same original inclusion is the whole transported closed core. An actual
comparison fixing that original surface therefore carries the first core
onto the second. Existence, uniqueness and the independent convex-region
identity remain explicit geometric inputs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

open Set Fuchsian

/-- The same original inclusion has image equal to the transported closed core. -/
theorem originalNielsenExtension_image_eq_modelConvexCore
    (hCore : Unproved.Teichmuller.OriginalFiniteAreaGeodesicRegionCore)
    {S Y : Type} [tS : TopologicalSpace S] [tY : TopologicalSpace Y]
    {U : TopologicalSpace.Opens S} {A : RiemannAtlas U}
    {input : OriginalBorderedHyperbolicInput U A}
    {RY : RiemannSurface Y} {M : HyperbolicSurfaceModel RY}
    (D : OriginalNielsenExtension input M) :
    Set.range D.inclusion = originalModelConvexCore M D.non_elementary := by
  have hRange : Set.range D.inclusion = M.discCover '' D.region := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      rw [D.inclusion_eq s]
      exact (D.original s).property
    · intro hy
      obtain ⟨s, hs⟩ := D.original.surjective ⟨y, hy⟩
      refine ⟨s, ?_⟩
      exact (D.inclusion_eq s).trans (congrArg Subtype.val hs)
  have hRegion := hCore Y tY RY M D.toOriginalGeodesicBoundaryRegion
  rw [hRange, hRegion]
  change (M.homeomorph.symm ∘
      mobiusDomainProjection (unitDiscMobiusInvariantDomain M.group M.invariant)) ''
      closure (fuchsianNielsenCore (originalHyperbolicDiscGroup M) D.non_elementary) =
    M.homeomorph ⁻¹' (mobiusDomainProjection (unitDiscMobiusInvariantDomain M.group M.invariant) ''
      closure (fuchsianNielsenCore (originalHyperbolicDiscGroup M) D.non_elementary))
  rw [Set.image_comp]
  exact M.homeomorph.toEquiv.image_symm_eq_preimage _

/-- There is an actual extension whose core is the same original surface,
with a unique over-surface analytic isometry carrying its core to every other one. -/
theorem original_exists_nielsen_extension_with_unique_core_comparison
    (hExists : Unproved.Teichmuller.OriginalBorderedNielsenExtensionExistence)
    (hUnique : Unproved.Teichmuller.OriginalBorderedNielsenExtensionUniqueness)
    (hCore : Unproved.Teichmuller.OriginalFiniteAreaGeodesicRegionCore)
    {S : Type} [tS : TopologicalSpace S]
    {U : TopologicalSpace.Opens S} {A : RiemannAtlas U}
    (input : OriginalBorderedHyperbolicInput U A) :
    ∃ (Y : Type) (tY : TopologicalSpace Y),
      letI := tY
      ∃ (RY : RiemannSurface Y) (M : HyperbolicSurfaceModel RY)
        (D : OriginalNielsenExtension input M),
        Set.range D.inclusion = originalModelConvexCore M D.non_elementary ∧
        ∀ (Z : Type) (tZ : TopologicalSpace Z),
          letI := tZ
          ∀ (RZ : RiemannSurface Z) (N : HyperbolicSurfaceModel RZ)
            (E : OriginalNielsenExtension input N),
            ∃! J : Y ≃ₜ Z,
              OriginalNielsenExtensionComparison D E J ∧
              J '' originalModelConvexCore M D.non_elementary =
                originalModelConvexCore N E.non_elementary := by
  obtain ⟨Y, tY, hY⟩ := hExists S tS U A input
  let := tY
  obtain ⟨RY, M, ⟨D⟩⟩ := hY
  have hD := originalNielsenExtension_image_eq_modelConvexCore hCore D
  refine ⟨Y, tY, RY, M, D, hD, ?_⟩
  intro Z tZ
  let := tZ
  intro RZ N E
  have hE := originalNielsenExtension_image_eq_modelConvexCore hCore E
  obtain ⟨J, hJ, hUniqueJ⟩ := hUnique S tS U A input Y tY RY M D Z tZ RZ N E
  refine ⟨J, ⟨hJ, ?_⟩, ?_⟩
  · rw [← hD, ← hE, ← Set.range_comp]
    exact congrArg Set.range (funext hJ.2.2.2)
  · intro K hK
    exact hUniqueJ K hK.1

end LowDimensionalTopology.Geometry.Surfaces
