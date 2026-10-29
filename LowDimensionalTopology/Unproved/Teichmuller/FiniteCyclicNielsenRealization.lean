module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceQCModularAction
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.AnalyticAutomorphismGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller
open LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Teichmuller

universe u

/-- A finite cyclic subgroup of the full original QC homotopy quotient has a
coherent faithful conformal realization compatible with an actual smooth marking.
This is an explicit unproved classical realization statement. -/
def FiniteCyclicNielsenRealization
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  letI := R.toRiemannAtlas.isManifold
  ∀ g : ℕ, 1 < g → R.HasGenus g →
    ∀ C : Subgroup (SourceQCModular.ModularGroup X), Finite C → IsCyclic C →
      ∃ (M : MarkedRiemannSurface.{u, u} R)
        (ρ : C →* M.surface.toRiemannAtlas.analyticAutomorphismSubgroup),
        Function.Injective ρ ∧
          ∀ (c : C) (f : SourceQCModular.Aut X), SourceQCModular.mk f = c.val →
            ContinuousMap.Homotopic
              ((_root_.toContinuousMap (ρ c).val).comp M.markingMap)
              (M.markingMap.comp (SourceQCModular.continuousMap f))

end LowDimensionalTopology.Unproved.Teichmuller
