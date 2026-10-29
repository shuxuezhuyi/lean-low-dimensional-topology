module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeModularDisplacementTypes
public import LowDimensionalTopology.Geometry.Surfaces.AdmissibleReduction
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The reducible nonperiodic modular dichotomy on the original surface

The input ranges over all original positive self-homeomorphisms, not just
quasiconformal ones. Periodicity concerns an actual positive homeomorphism
in the given homotopy class. The conclusion uses every actual QC
representative of that class and the existing full-log displacement types.
Their existence is supplied by the proved representative entry. This is a
concrete unresolved proposition; no dichotomy proof is supplied here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller

variable {X : Type} [TopologicalSpace X]

/-- A reducible positive self-homeomorphism not homotopic to any actual
positive periodic homeomorphism has parabolic or pseudo-hyperbolic class.
All original maps and all their genuine QC representatives are retained. -/
def OriginalReducibleModularDichotomy (R : ClosedRiemannSurface X) (g : ℕ) : Prop :=
  1 < g → R.HasGenus g →
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    ∀ f : X ≃ₜ X, LiZhongQC.IsOrientationPreservingRS f → IsReducible f →
      (¬ ∃ h : X ≃ₜ X,
        LiZhongQC.IsOrientationPreservingRS h ∧ IsOfFinOrder h ∧
          ContinuousMap.Homotopic (_root_.toContinuousMap f) (_root_.toContinuousMap h)) →
      ∀ q : SourceQCModular.Aut X,
        ContinuousMap.Homotopic (_root_.toContinuousMap f) (SourceQCModular.continuousMap q) →
        NativeMinimizers.IsParabolic R (SourceQCModular.mk q) ∨
          NativeMinimizers.IsPseudoHyperbolic R (SourceQCModular.mk q)

end LowDimensionalTopology.Unproved.Teichmuller
