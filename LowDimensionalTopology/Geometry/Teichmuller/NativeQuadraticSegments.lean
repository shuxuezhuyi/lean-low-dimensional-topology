module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.HolomorphicQuadraticDifferential
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Segments of an original holomorphic quadratic differential

A segment is an embedded closed arc whose interior is regular and becomes a
straight Euclidean segment in local natural coordinates. Its endpoints may be
zeros of the differential.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

variable {X : Type} [TopologicalSpace X] (R : RiemannSurface X)
    (q : Surfaces.HolomorphicQuadraticDifferential R.toRiemannAtlas)

/-- A closed arc which is locally straight in genuine natural coordinates at
every interior point. No regularity condition is imposed at either endpoint. -/
def IsQuadraticSegment (c : C(unitInterval, X)) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  Function.Injective c ∧
    ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
      (q : X → ℂ → ℂ) (c t) (chartAt ℂ (c t) (c t)) ≠ 0 ∧
      ∃ e : OpenPartialHomeomorph ℂ ℂ,
        e.source ⊆ (chartAt ℂ (c t)).target ∧
        AnalyticOnNhd ℂ (e : ℂ → ℂ) e.source ∧
        e (chartAt ℂ (c t) (c t)) = 0 ∧
        (∀ z ∈ e.source, deriv (e : ℂ → ℂ) z ^ 2 = (q : X → ℂ → ℂ) (c t) z) ∧
        ∃ a b : unitInterval, a < t ∧ t < b ∧
          (∀ s ∈ Set.Icc a b, c s ∈ (chartAt ℂ (c t)).source ∧
            chartAt ℂ (c t) (c s) ∈ e.source) ∧
          (fun s : unitInterval => e (chartAt ℂ (c t) (c s))) '' Set.Icc a b =
            segment ℝ (e (chartAt ℂ (c t) (c a))) (e (chartAt ℂ (c t) (c b)))

/-- The original continuous arc is a closed embedding in the original surface. -/
theorem IsQuadraticSegment.isClosedEmbedding {c : C(unitInterval, X)}
    (h : IsQuadraticSegment R q c) : Topology.IsClosedEmbedding c := by
  let := R.t2Space
  exact c.continuous.isClosedEmbedding h.1

/-- A zero met by the original segment can occur only at an endpoint. -/
theorem IsQuadraticSegment.zero_only_at_endpoints {c : C(unitInterval, X)}
    (h : IsQuadraticSegment R q c) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ t : unitInterval,
      (q : X → ℂ → ℂ) (c t) (chartAt ℂ (c t) (c t)) = 0 → t = 0 ∨ t = 1 := by
  let := R.toRiemannAtlas.toChartedSpace
  intro t hz
  by_cases ht0 : t = 0
  · exact Or.inl ht0
  by_cases ht1 : t = 1
  · exact Or.inr ht1
  have h0 : 0 < (t : ℝ) :=
    lt_of_le_of_ne t.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr ht0))
  have h1 : (t : ℝ) < 1 :=
    lt_of_le_of_ne t.property.2 (unitInterval.coe_ne_one.mpr ht1)
  exact False.elim ((h.2 t h0 h1).1 hz)

end LowDimensionalTopology.Geometry.Teichmuller
