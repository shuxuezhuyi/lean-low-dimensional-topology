module

public import LowDimensionalTopology.Geometry.Surfaces.PseudoAnosov
public import LowDimensionalTopology.Geometry.Teichmuller.NativeComplexMinimizers

/-!
# Pseudo-Anosov representatives and the actual hyperbolic modular type

The original positive homeomorphism and its genuine homotopy class are kept.
The geometric representative preserves actual nondegenerate measured
foliations, while the modular type uses the original full-log displacement.
-/

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller

/-- Hyperbolicity of every actual QC representative is equivalent to the
existence of a genuine pseudo-Anosov representative in the same homotopy class. -/
def OriginalPseudoAnosovModularCharacterization
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) (g : ℕ) : Prop :=
  1 < g → R.HasGenus g →
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ f : X ≃ₜ X, LiZhongQC.IsOrientationPreservingRS f →
      ∀ q : SourceQCModular.Aut X,
        ContinuousMap.Homotopic (_root_.toContinuousMap f)
          (SourceQCModular.continuousMap q) →
        ((∃ h : X ≃ₜ X, IsPseudoAnosov R h ∧
          ContinuousMap.Homotopic (_root_.toContinuousMap f) (_root_.toContinuousMap h)) ↔
            NativeMinimizers.IsHyperbolic R (SourceQCModular.mk q))

end LowDimensionalTopology.Unproved.Teichmuller
