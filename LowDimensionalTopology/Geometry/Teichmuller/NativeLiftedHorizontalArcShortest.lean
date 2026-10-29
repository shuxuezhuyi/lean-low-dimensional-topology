module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.HolomorphicQuadraticDifferential
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedUniqueness

/-! The actual horizontal arc minimizes the lifted quadratic-differential length.
The original differential and both lifted endpoints are retained. Regularity is
required only on the open arc; the continuous endpoints may be zeros. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

/-- A horizontal arc of the actual lifted original differential is no longer
than any same-half-plane competitor joining its lifted endpoints. -/
theorem nativeLiftedHorizontalArc_shortest
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
      (p : UpperHalfPlane → X) (_hp : IsUniformization Γ p)
      (c : ℝ → ℂ) (a b : ℝ), a < b →
      IsHorizontalArc (utm_liftQD (q : X → ℂ → ℂ) p) c a b →
      ContinuousOn c (Icc a b) → c '' Icc a b ⊆ upperHalf →
      ∀ (β : LRCurve), β.trace ⊆ upperHalf →
        Tendsto β.toFun (nhdsWithin 0 (Ioi 0)) (𝓝 (c a)) →
        Tendsto β.toFun (nhdsWithin 1 (Iio 1)) (𝓝 (c b)) →
        (∫⁻ t in Ioo a b,
          phiDensity (utm_liftQD (q : X → ℂ → ℂ) p) (c t) * ‖deriv c t‖ₑ) ≤
          phiLength (utm_liftQD (q : X → ℂ → ℂ) p) β := by
  let := R.t2Space
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro Γ p hp c a b hab hc hcc hcH β hβ hβa hβb
  have hqfun : (q : X → ℂ → ℂ) ≠ 0 := by
    intro hzero
    exact hq (Subtype.ext hzero)
  have hhol := utm_liftQD_differentiableOn q.property hp
  have hne := utm_liftQD_ne q.property hqfun hp
  exact utm_arc_shortest_upperHalf hhol hne hab hc hcc hcH β hβ hβa hβb

end LowDimensionalTopology.Geometry.Teichmuller
