module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.QuotientMetric
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.ProjectedFunnelCoreCut

/-!
# The closed convex core in an original hyperbolic model

Use the entire given uniformizing group and pull its closed core back to the
same original surface. All off-axis complementary pieces are removed and
every projected boundary axis is retained. Finite generation is required
separately for the closed-cylinder description of the complementary pieces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Surfaces

open Fuchsian

variable {X : Type} [TopologicalSpace X] {R : RiemannSurface X}

/-- The whole original disc group, with exactly the given invariant domain. -/
theorem originalHyperbolicDiscGroup (M : HyperbolicSurfaceModel R) :
    UnitDiscFuchsianGroup M.group :=
  { invariant := M.invariant, discontinuous := M.discontinuous }

/-- The actual closed core transported to the same original surface. -/
def originalModelConvexCore (M : HyperbolicSurfaceModel R)
    (hNE : DiscreteGroups.IsNonElementary M.group) : Set X :=
  M.homeomorph ⁻¹' threeBoundaryClosedCore (originalHyperbolicDiscGroup M) hNE

variable (M : HyperbolicSurfaceModel R)
    (hNE : DiscreteGroups.IsNonElementary M.group)
local notation "P" => originalHyperbolicDiscGroup M

/-- The core is the complement of all actual projected off-axis pieces. -/
theorem originalModelConvexCore_eq_compl_funnelInteriors
    (w : (P).domain.carrier) (hw : w ∈ fuchsianNielsenCore P hNE) :
    originalModelConvexCore M hNE =
      (⋃ L : nielsenBoundaryDiscLineFamily P hNE,
        M.homeomorph ⁻¹' projectedNielsenFunnelInterior P L.val w)ᶜ := by
  ext x
  change M.homeomorph x ∈ threeBoundaryClosedCore P hNE ↔ _
  rw [projectedNielsenCore_eq_compl_funnelInteriors P hNE w hw]
  constructor
  · intro h hx
    obtain ⟨L, hL⟩ := Set.mem_iUnion.mp hx
    exact h (Set.mem_iUnion.mpr ⟨L, hL⟩)
  · intro h hx
    obtain ⟨L, hL⟩ := Set.mem_iUnion.mp hx
    exact h (Set.mem_iUnion.mpr ⟨L, hL⟩)

/-- Every point of every original projected boundary axis stays in the core. -/
theorem originalModelConvexCore_retains_axis
    (L : Hyperbolic.DiscLine) (hL : L ∈ nielsenBoundaryDiscLineFamily P hNE)
    (w : (P).domain.carrier) (hw : w ∈ fuchsianNielsenCore P hNE) :
    M.homeomorph ⁻¹'
      (mobiusDomainProjection (P).domain '' ((P).finiteCoordinate.symm '' L.carrier)) ⊆
        originalModelConvexCore M hNE := by
  intro x hx
  change M.homeomorph x ∈ threeBoundaryClosedCore P hNE
  have hmem : M.homeomorph x ∈ projectedNielsenClosedFunnel P L w ∩
      threeBoundaryClosedCore P hNE := by
    rw [projectedNielsenClosedFunnel_inter_core P hNE L hL w hw]
    exact hx
  exact hmem.2

end LowDimensionalTopology.Geometry.Surfaces
