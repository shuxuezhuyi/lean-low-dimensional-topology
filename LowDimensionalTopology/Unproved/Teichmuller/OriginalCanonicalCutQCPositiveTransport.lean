module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.OriginalCanonicalCut

/-!
# Positivity of the same canonical cut after a quasiconformal map

The input is one actual original cut and one actual quasiconformal map. The
missing geometric implementation transports local sense preservation to the
whole cut chart. This proposition records exactly the positive field of the
same composed polygon, with the original source and target complex atlases.
It asserts no quotient comparison or realization of prescribed markings.
-/

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Surfaces.HandlePresentation

/-- A given quasiconformal map preserves positivity of the same original cut,
tested on the actual inverse domain of every original target chart. -/
def OriginalCanonicalCutQCPositiveTransport
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (p : X)
    (D : OriginalOrientedCanonicalCut R g
      (lt_trans Nat.zero_lt_one hg) p) : Prop :=
  ∀ {Y : Type} [TopologicalSpace Y] (S : ClosedRiemannSurface Y)
    (f : X ≃ₜ Y),
    (letI := R.toRiemannAtlas.toChartedSpace
     letI := S.toRiemannAtlas.toChartedSpace
     LiZhongQC.IsQCRS f) →
    ∀ c ∈ S.toRiemannAtlas.charts,
      LiZhongQC.IsSensePreserving
        (fun z => c (originalCanonicalCutPlane
          (f.symm.trans D.polygon) z))
        (Metric.ball (0 : ℂ) 1 ∩
          originalCanonicalCutPlane (f.symm.trans D.polygon) ⁻¹' c.source)

end LowDimensionalTopology.Unproved.Teichmuller
