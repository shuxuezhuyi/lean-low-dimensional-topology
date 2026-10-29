module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticNaturalCoordinateProjection
public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalQuadraticFoliation

/-!
# Regular ordinary charts of the same quadratic differential

At a regular centre the ordinary normal form has order zero. Its actual
restricted chart is a flat coordinate of the original differential at every
point of its source, with centering only by an additive constant.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
    {q : HolomorphicQuadraticDifferential R.toRiemannAtlas} {p : X}

/-- At a regular centre the actual ordinary neighborhood is a flat chart of the same differential. -/
theorem QuadraticNaturalCoordinateData.ordinaryNeighborhood_isQuadraticNatural_of_regular
    (D : QuadraticNaturalCoordinateData R q p)
    (hp : letI := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsRegularPoint (q : X → ℂ → ℂ) p) :
    IsQuadraticNaturalLeafChart R q D.ordinaryNeighborhood := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.isManifold
  have hm : D.order = 0 := D.normal.regular_iff.mp hp
  have hdom (x : X) (hx : x ∈ D.ordinaryNeighborhood.source) :
      x ∈ (chartAt ℂ p).source ∧ chartAt ℂ p x ∈ D.ordinaryChart.source := hx.1
  have hregular (x : X) (hx : x ∈ D.ordinaryNeighborhood.source) :
      LiZhongQC.IsRegularPoint (q : X → ℂ → ℂ) x := by
    by_cases hxp : x = p
    · simpa only [hxp] using hp
    have hx' := hdom x hx
    have hne : chartAt ℂ p x ≠ chartAt ℂ p p := fun h =>
      hxp ((chartAt ℂ p).injOn hx'.1 (mem_chart_source ℂ p) h)
    have hcoeff := D.normal.ne_zero (chartAt ℂ p x) hx'.2 hne
    simpa only [(chartAt ℂ p).left_inv hx'.1] using
      (LiZhongQC.s26d_a_isRegularPoint_iff q.property p
        ((chartAt ℂ p).map_source hx'.1)).mpr hcoeff
  refine ⟨fun x hx => hregular x hx, ?_⟩
  intro x hx
  have hx' := hdom x hx
  have hW :
      AnalyticAt ℂ (fun z => D.ordinaryNeighborhood ((chartAt ℂ x).symm z))
        (chartAt ℂ x x) ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ x x),
        deriv (fun z => D.ordinaryNeighborhood ((chartAt ℂ x).symm z)) z ^ 2 =
          (q : X → ℂ → ℂ) x z :=
    LiZhongQC.s26d_a_W_natural q.property D.normal hx'.1 hx'.2
      (h := id) analyticAt_id (Filter.Eventually.of_forall fun ξ => by norm_num [hm])
  have hsq : ∀ᶠ z in 𝓝 (chartAt ℂ x x),
      deriv (fun z => D.ordinaryNeighborhood ((chartAt ℂ x).symm z) -
        D.ordinaryNeighborhood x) z ^ 2 = (q : X → ℂ → ℂ) x z :=
    hW.2.mono fun z hz => by simpa only [deriv_sub_const] using hz
  refine ⟨hW.1.sub analyticAt_const, ?_, ?_, hsq⟩
  · simp only [(chartAt ℂ x).left_inv (mem_chart_source ℂ x), sub_self]
  · intro hzero
    have hqzero : (q : X → ℂ → ℂ) x (chartAt ℂ x x) = 0 := by
      rw [← hsq.self_of_nhds, hzero, zero_pow (by decide)]
    exact hregular x hx hqzero

end LowDimensionalTopology.Geometry.Teichmuller
