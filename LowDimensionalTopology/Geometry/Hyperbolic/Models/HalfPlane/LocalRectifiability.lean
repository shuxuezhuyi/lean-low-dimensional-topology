module

public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.LocalBoundedVariation
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.IntrinsicBoundedVariation

/-!
# Rectifiability of continuous half-plane curves in local coordinates

A continuous curve on a compact real interval is rectifiable for the actual
hyperbolic metric exactly when its complex coordinate is BV locally at every
parameter, using genuine relative neighborhoods and retaining the endpoints.
-/

public section
noncomputable section
open Set Filter
open scoped UpperHalfPlane Topology

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Rectifiability in the genuine hyperbolic metric can be checked in arbitrarily
small coordinate neighborhoods of each parameter of a continuous compact curve. -/
theorem halfPlane_boundedVariation_iff_locally_coe {f : ℝ → ℍ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    BoundedVariationOn f (Icc a b) ↔
      ∀ x ∈ Icc a b, ∃ U ∈ 𝓝[Icc a b] x,
        BoundedVariationOn (fun t => (f t : ℂ)) U := by
  constructor
  · intro h x hx
    exact ⟨Icc a b, self_mem_nhdsWithin,
      (halfPlane_boundedVariation_iff_coe_of_continuousOn hf).mp h⟩
  · intro h
    exact (halfPlane_boundedVariation_iff_coe_of_continuousOn hf).mpr
      (boundedVariationOn_Icc_of_nhdsWithin h)

end LowDimensionalTopology.Geometry.Hyperbolic
