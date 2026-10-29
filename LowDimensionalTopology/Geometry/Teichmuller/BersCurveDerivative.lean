module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeNonzeroBersIntegralKernel
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The Bers derivative along first-order coefficient curves

Every first-order coefficient curve remains in the original coefficient ball
near its base point. Its Bers difference quotient converges in the original
weighted Banach norm to the derivative applied to its tangent coefficient.
-/

public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Surfaces
universe u

/-- First-order coefficient perturbations have the same weighted Bers derivative. -/
theorem automorphicProjection_tendsto_firstOrderCurve
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (μ : Ball Γ)
    (η : Space Γ) (ε : ℂ → Space Γ)
    (hε : Tendsto ε (𝓝[≠] (0 : ℂ)) (𝓝 0)) :
    (∀ᶠ t : ℂ in 𝓝 0,
      μ.val + t • η + t • ε t ∈ Metric.ball (0 : Space Γ) 1) ∧
    Tendsto (fun t : ℂ => t⁻¹ •
      (BersWeighted.automorphicProjection hΓ (μ.val + t • η + t • ε t) -
        BersWeighted.automorphicProjection hΓ μ.val))
      (𝓝[≠] 0) (𝓝 (nonzeroBersDerivative R hp hg hgenus hΓ μ η)) := by
  let c : ℂ → Space Γ := fun t => μ.val + t • η + t • ε t
  have hc : HasDerivAt c η 0 := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    have heq : (fun t : ℂ => t⁻¹ • (c (0 + t) - c 0)) =ᶠ[𝓝[≠] 0]
        (fun t => η + ε t) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : t ≠ 0 := by simpa using ht
      simp [c, add_assoc, smul_add, smul_smul, inv_mul_cancel₀ ht']
    apply (Filter.tendsto_congr' heq).mpr
    simpa only [add_zero] using tendsto_const_nhds.add hε
  have hnear : ∀ᶠ t : ℂ in 𝓝 0, c t ∈ Metric.ball (0 : Space Γ) 1 := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa [c] using Metric.isOpen_ball.mem_nhds μ.property
  refine ⟨by simpa only [c] using hnear, ?_⟩
  have hd := (hasFDerivAt_automorphicProjection_nonzero R hp hg hgenus hΓ μ).comp_hasDerivAt_of_eq
    (0 : ℂ) hc (by simp [c])
  simpa only [Function.comp_apply, zero_add, c, zero_smul, add_zero]
    using hd.tendsto_slope_zero

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
