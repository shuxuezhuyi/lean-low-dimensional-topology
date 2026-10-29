module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalReducibleModularDichotomy

/-!
# A necessary topological alternative for a jointly minimizing structure

An actual original minimizing complex structure gives a genuine minimizing
point for a QC representative of the same original homotopy class. The
explicit reducible-class dichotomy excludes the reducible nonperiodic case.
This proves the necessary direction; no converse or full classification
is supplied here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers

open Surfaces
open LowDimensionalTopology.Unproved.Teichmuller

variable {X : Type} [TopologicalSpace X]

/-- Under the explicit reducible-class dichotomy, a jointly minimizing
original complex structure forces periodic homotopy or irreducibility.
Periodicity concerns an actual positive finite-order homeomorphism. -/
theorem periodic_or_irreducible_of_minimalComplexStructure_of_reducibleDichotomy
    (R : ClosedRiemannSurface X) {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hD : OriginalReducibleModularDichotomy R g) (f : X ≃ₜ X)
    (hOri : let := R.toRiemannAtlas.toChartedSpace
      let := R.toRiemannAtlas.isManifold
      LiZhongQC.IsOrientationPreservingRS f)
    (hmin : ∃ σ : PositiveComplexStructure R, IsMinimalComplexStructure R f σ) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    (∃ h : X ≃ₜ X,
      LiZhongQC.IsOrientationPreservingRS h ∧ IsOfFinOrder h ∧
        ContinuousMap.Homotopic (_root_.toContinuousMap f) (_root_.toContinuousMap h)) ∨
      IsIrreducible f := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  by_cases hperiodic : ∃ h : X ≃ₜ X,
      LiZhongQC.IsOrientationPreservingRS h ∧ IsOfFinOrder h ∧
        ContinuousMap.Homotopic (_root_.toContinuousMap f) (_root_.toContinuousMap h)
  · exact Or.inl hperiodic
  · apply Or.inr
    change ¬ IsReducible f
    intro hred
    obtain ⟨a, ha, hcomparison, _⟩ :=
      originalHomeomorph_minimizer_comparison R hg hgenus f hOri
    obtain ⟨σ, hσ⟩ := hmin
    have htypes := hD hg hgenus f hOri hred hperiodic a ha
    have hno := (no_minimizingPoint_iff_parabolic_or_pseudoHyperbolic R
      (SourceQCModular.mk a)).mpr htypes
    exact hno ⟨σ.point, (hcomparison σ).mp hσ⟩

end LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers
