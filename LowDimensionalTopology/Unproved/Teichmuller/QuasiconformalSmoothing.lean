module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceMarking

/-!
# Global smoothing with quantitative quasiconformal distortion

This proposition concerns the original complex atlases of actual closed
surfaces and an actual quasiconformal homeomorphism. It asks for a positive
smooth diffeomorphism in the same free homotopy class whose intrinsic uniform
Beltrami norm is arbitrarily close to the given distortion bound. Importing
this definition supplies no proof of that analytic approximation theorem.
-/

@[expose] public section
noncomputable section

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller

universe u

/-- Quantitative global smoothing of actual quasiconformal maps between closed
Riemann surfaces. The tensor and its norm use the unchanged original atlases. -/
def QuasiconformalSmoothing : Prop :=
  ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y)
    (f : X ≃ₜ Y) (K : ℝ), 1 ≤ K →
    (let := R.toRiemannAtlas.toChartedSpace
     let := S.toRiemannAtlas.toChartedSpace
     LiZhongQC.IsKQCRS f K) →
    let := R.compactSpace
    ∀ ε : ℝ, 0 < ε →
      ∃ (F : SmoothSurfaceEquiv R.toRiemannSurface S.toRiemannSurface)
        (hF : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas F.toHomeomorph),
        ContinuousMap.Homotopic (_root_.toContinuousMap F.toHomeomorph)
          (_root_.toContinuousMap f) ∧
        (F.beltrami hF).supNorm ≤ (K - 1) / (K + 1) + ε

end LowDimensionalTopology.Unproved.Teichmuller
