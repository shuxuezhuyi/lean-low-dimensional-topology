module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.HolomorphicQuadraticDifferential
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S25_QuadraticDifferentials
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : Surfaces.HolomorphicQuadraticDifferential R.toRiemannAtlas)

/-- The squared singular line element is unchanged by the original chart transition. -/
theorem quadraticFlatMetric_chart_change :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ (x y : X) (z v : ℂ), z ∈ (chartAt ℂ x).target →
      (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source →
      ‖(q : X → ℂ → ℂ) x z‖ * ‖v‖ ^ 2 =
        ‖(q : X → ℂ → ℂ) y (LiZhongQC.chartTransition y x z)‖ *
          ‖deriv (LiZhongQC.chartTransition y x) z * v‖ ^ 2 := by
  let := R.toRiemannAtlas.toChartedSpace
  intro x y z v hz hzy
  have hq : LiZhongQC.IsHolQuadDiff (q : X → ℂ → ℂ) := q.property
  rw [LiZhongQC.s26u_law hq x y hz hzy, norm_mul, norm_pow, norm_mul]
  ring

/-- The entire squared line element vanishes exactly at a zero of its coefficient. -/
theorem quadraticFlatMetric_zero_iff (x : X) (z : ℂ) :
    (∀ v : ℂ, ‖(q : X → ℂ → ℂ) x z‖ * ‖v‖ ^ 2 = 0) ↔ (q : X → ℂ → ℂ) x z = 0 := by
  constructor
  · intro h
    simpa only [norm_one, one_pow, mul_one, norm_eq_zero] using h 1
  · intro h v
    rw [h, norm_zero, zero_mul]

/-- The original length density is the square root of this squared line element. -/
theorem quadraticFlatMetric_density_sq (x : X) (z : ℂ) :
    LiZhongQC.phiDensity ((q : X → ℂ → ℂ) x) z ^ 2 = ENNReal.ofReal ‖(q : X → ℂ → ℂ) x z‖ := by
  rw [LiZhongQC.phiDensity, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt (norm_nonneg _)]

/-- Each original chart coefficient extends continuously through its actual zeros. -/
theorem quadraticFlatMetric_continuous :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ x : X, ContinuousOn (fun z : ℂ => ‖(q : X → ℂ → ℂ) x z‖) (chartAt ℂ x).target := by
  let := R.toRiemannAtlas.toChartedSpace
  intro x
  have hq : LiZhongQC.IsHolQuadDiff (q : X → ℂ → ℂ) := q.property
  exact continuous_norm.comp_continuousOn (hq.2 x).continuousOn

/-- Away from an actual zero, the original singular metric is the Euclidean
pullback in a genuine local natural coordinate. -/
theorem quadraticFlatMetric_natural_coordinate :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ p : X, (q : X → ℂ → ℂ) p (chartAt ℂ p p) ≠ 0 →
      ∃ (ζ : ℂ → ℂ) (e : OpenPartialHomeomorph ℂ ℂ),
        AnalyticAt ℂ ζ (chartAt ℂ p p) ∧ ζ (chartAt ℂ p p) = 0 ∧
        deriv ζ (chartAt ℂ p p) ≠ 0 ∧ (e : ℂ → ℂ) = ζ ∧
        chartAt ℂ p p ∈ e.source ∧
        ∀ᶠ z in 𝓝 (chartAt ℂ p p), deriv ζ z ^ 2 = (q : X → ℂ → ℂ) p z ∧
          ∀ v : ℂ, ‖(q : X → ℂ → ℂ) p z‖ * ‖v‖ ^ 2 = ‖deriv ζ z * v‖ ^ 2 := by
  let := R.toRiemannAtlas.toChartedSpace
  intro p h0
  have hq : LiZhongQC.IsHolQuadDiff (q : X → ℂ → ℂ) := q.property
  have han : AnalyticAt ℂ ((q : X → ℂ → ℂ) p) (chartAt ℂ p p) :=
    (hq.2 p).analyticAt ((chartAt ℂ p).open_target.mem_nhds
      ((chartAt ℂ p).map_source (mem_chart_source ℂ p)))
  obtain ⟨ζ, hζ, hζ0, hζd, hζq⟩ := LiZhongQC.eq25_2_natural_parameter han h0
  have hs := hζ.hasStrictDerivAt.hasStrictFDerivAt_equiv hζd
  refine ⟨ζ, hs.toOpenPartialHomeomorph ζ, hζ, hζ0, hζd, rfl,
    hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  filter_upwards [hζq] with z hz
  refine ⟨hz, fun v => ?_⟩
  rw [← hz, norm_pow, norm_mul]
  ring

end LowDimensionalTopology.Geometry.Teichmuller
