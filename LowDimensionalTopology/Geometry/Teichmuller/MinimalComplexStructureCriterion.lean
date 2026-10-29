module

public import LowDimensionalTopology.Geometry.Teichmuller.IrreducibleNativeMinimizer
public import LowDimensionalTopology.Geometry.Teichmuller.MinimalComplexStructureNecessaryTypes
public import LowDimensionalTopology.Geometry.Teichmuller.PeriodicMinimalComplexStructure

/-!
# The periodic-or-irreducible criterion for a minimizing structure

The necessary topological alternative, the cyclic Nielsen branch, and the
irreducible minimum-displacement theorem combine on the same original
positive homeomorphism. Periodicity is represented by an actual positive
finite-order homeomorphism in its genuine homotopy class.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers

open Surfaces LiZhongQC

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- An original jointly minimizing complex structure exists exactly in the
periodic homotopy or irreducible cases, with the independent inputs explicit. -/
theorem exists_minimalComplexStructure_iff_periodic_or_irreducible
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hD : LowDimensionalTopology.Unproved.Teichmuller.OriginalReducibleModularDichotomy R g)
    (hNielsen : LowDimensionalTopology.Unproved.Teichmuller.FiniteCyclicNielsenRealization R)
    (hSimple : ∀ σ : PositiveComplexStructure R,
      LowDimensionalTopology.Unproved.Surfaces.SimpleClosedGeodesicRepresentatives
        σ.surface g (σ.marked.geodesicLengthModel R (Nat.succ_le_of_lt hg) hgenus))
    (hCard : ∀ σ : PositiveComplexStructure R,
      LowDimensionalTopology.Unproved.Surfaces.ClosedDecomposingSystemCardinalities
        σ.surface (Nat.succ_le_of_lt hg) hgenus
        (σ.marked.geodesicLengthModel R (Nat.succ_le_of_lt hg) hgenus))
    (hCircle : LowDimensionalTopology.Unproved.Topology.CircleHomeomorphHomotopyDichotomy)
    (hStraight : LowDimensionalTopology.Unproved.Surfaces.SimultaneousAdmissibleCurveStraightening
      R g)
    (hMumford : LowDimensionalTopology.Unproved.Teichmuller.NativeMumfordSequentialCompactness
      R hg hgenus)
    (f : X ≃ₜ X)
    (hf : letI := R.toRiemannAtlas.toChartedSpace
      letI := R.toRiemannAtlas.isManifold
      IsOrientationPreservingRS f) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    (∃ σ : PositiveComplexStructure R, IsMinimalComplexStructure R f σ) ↔
      (∃ h : X ≃ₜ X, IsOrientationPreservingRS h ∧ IsOfFinOrder h ∧
        ContinuousMap.Homotopic (_root_.toContinuousMap f) (_root_.toContinuousMap h)) ∨
      IsIrreducible f := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  constructor
  · exact periodic_or_irreducible_of_minimalComplexStructure_of_reducibleDichotomy
      R hg hgenus hD f hf
  · rintro (hperiodic | hirred)
    · exact exists_minimalComplexStructure_of_homotopic_positive_periodic_of_nielsen
        R hg hgenus hNielsen f hf hperiodic
    · obtain ⟨a, ha, _hcomparison, hexists⟩ :=
        originalHomeomorph_minimizer_comparison R hg hgenus f hf
      exact hexists.mpr
        (elliptic_or_hyperbolic_of_irreducible_originalHomeomorph_of_mumford
          R hg hgenus hSimple hCard hCircle hStraight hMumford f hf hirred a ha)

end LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers
