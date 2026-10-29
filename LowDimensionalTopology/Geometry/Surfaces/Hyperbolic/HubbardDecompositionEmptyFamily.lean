/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Unproved.Teichmuller.HubbardDecomposition

/-!
# Empty-family specialization of a Hubbard decomposition

The empty prescribed family gives a geodesic family with the full completed-
piece geometry and all residual-geodesic boundary identifications.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Unproved.Teichmuller

/-- The extension property for finite geodesic families supplies a geodesic
family with the same completed-piece and residual-boundary data. -/
theorem exists_hubbard_decomposition_of_finite_prescribed
    {X : Type} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (hHubbard : HubbardFinitePrescribedDecomposition M)
    (hNotSimplyConnected : ¬ SimplyConnectedSpace X)
    (hUserException : ¬ RiemannConformallyEquivalent R
      (stableCuspPuncturedDiscRiemannSurface 0)) :
    ∃ Y : Set (EssentialSimpleCircle X),
      IsGeodesicMulticurve M Y ∧ HubbardDecompositionBody M Y := by
  have hEmpty : IsGeodesicMulticurve M (∅ : Set (EssentialSimpleCircle X)) := by
    simp [IsGeodesicMulticurve, IsMulticurve]
  obtain ⟨Y, _hContains, hMaximal, hBody⟩ :=
    hHubbard hNotSimplyConnected hUserException ∅ Set.finite_empty hEmpty
  exact ⟨Y, hMaximal.1, hBody⟩

end LowDimensionalTopology.Geometry.Surfaces
