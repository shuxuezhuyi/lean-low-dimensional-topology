module

public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.RectifiableDistance
public import LowDimensionalTopology.External.LiZhongQC.Ch03.S14_PoincareMetric
public import Mathlib.Tactic.FunProp

/-!
# The upper-half-plane distance over all continuous rectifiable curves

The density is the literal reciprocal imaginary coordinate. Its values outside
this domain do not enter any admissible curve's line integral.
-/
public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

private theorem metricDist_congr_density {D : Set ℂ} {ρ σ : ℂ → ℝ≥0∞}
    (hρσ : EqOn ρ σ D) (z w : ℂ) :
    LiZhongQC.metricDist D ρ z w = LiZhongQC.metricDist D σ z w := by
  unfold LiZhongQC.metricDist
  refine iInf_congr fun γ => iInf_congr fun hγ => ?_
  apply LiZhongQC.LRCurve.rhoLength_congr
  rintro ζ ⟨t, ht, rfl⟩
  exact hρσ (hγ.2.2.2 ⟨t, Ioo_subset_Icc_self ht, rfl⟩)

/-- Reciprocal height is a Borel density on the ambient complex plane. -/
theorem measurable_halfPlane_poincareDensity :
    Measurable (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) := by
  fun_prop

/-- Mathlib's hyperbolic distance is the infimum of literal Poincaré
arclength integrals over every continuous rectifiable joining curve. -/
theorem halfPlane_rectifiable_distance (z w : ℍ) :
    rectifiableMetricDist LiZhongQC.upperHalf
      (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) z w =
      ENNReal.ofReal (dist z w) := by
  rw [rectifiableMetricDist_eq_metricDist LiZhongQC.upperHalf
    measurable_halfPlane_poincareDensity]
  calc
    _ = LiZhongQC.poincareDist LiZhongQC.upperHalf z w :=
      metricDist_congr_density
        (fun ζ hζ => congrArg ENNReal.ofReal
          (LiZhongQC.poincareDensity_upperHalf hζ).symm) z w
    _ = _ := LiZhongQC.poincareDist_upperHalf z w

end LowDimensionalTopology.Geometry.Hyperbolic
