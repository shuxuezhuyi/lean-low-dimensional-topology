module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedGeodesicCrossing
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A universal short-geodesic disjointness threshold

The short-geodesic theorem follows from the existing original crossing inequality.
The explicit constant is the disjointness part of LearningMath 75.41;
maximality of that constant is a separate assertion, not proved here.
-/

public section
noncomputable section
open Set

namespace LowDimensionalTopology.Geometry.Surfaces

/-- The explicit strict cutoff in the notes' short-geodesic statement. -/
@[expose] def shortClosedGeodesicCutoff : ℝ := Real.log (3 + 2 * Real.sqrt 2)

theorem shortClosedGeodesicCutoff_pos : 0 < shortClosedGeodesicCutoff := by
  apply Real.log_pos
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

theorem sinh_shortClosedGeodesicCutoff_half :
    Real.sinh (shortClosedGeodesicCutoff / 2) = 1 := by
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hp : 0 < 1 + Real.sqrt (2 : ℝ) := by positivity
  have hsq : 3 + 2 * Real.sqrt (2 : ℝ) = (1 + Real.sqrt 2) ^ 2 := by
    nlinarith
  have hlog : shortClosedGeodesicCutoff / 2 = Real.log (1 + Real.sqrt 2) := by
    unfold shortClosedGeodesicCutoff
    rw [hsq, Real.log_pow]
    ring
  have hi : (1 + Real.sqrt (2 : ℝ))⁻¹ = Real.sqrt 2 - 1 := by
    have he : (1 : ℝ) / (1 + Real.sqrt 2) = Real.sqrt 2 - 1 := by
      apply (div_eq_iff hp.ne').mpr
      nlinarith
    simpa only [one_div] using he
  rw [hlog, Real.sinh_log hp, hi]
  ring

/-- Two full original periods below the explicit cutoff have equal or
disjoint geometric images. Simplicity and compactness are not needed. -/
theorem OriginalClosedGeodesic.trace_eq_or_disjoint_of_length_lt_shortCutoff
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q r : OriginalClosedGeodesic M)
    (hq : q.length.toReal < shortClosedGeodesicCutoff)
    (hr : r.length.toReal < shortClosedGeodesicCutoff) :
    range q.curve = range r.curve ∨ Disjoint (range q.curve) (range r.curve) := by
  by_cases heq : range q.curve = range r.curve
  · exact Or.inl heq
  · refine Or.inr ?_
    by_contra hcross
    have hprod := q.crossing_length_product r heq hcross
    have hq' : Real.sinh (q.length.toReal / 2) < 1 := by
      rw [← sinh_shortClosedGeodesicCutoff_half]
      exact Real.sinh_lt_sinh.mpr (by linarith)
    have hr' : Real.sinh (r.length.toReal / 2) < 1 := by
      rw [← sinh_shortClosedGeodesicCutoff_half]
      exact Real.sinh_lt_sinh.mpr (by linarith)
    have hr0 : 0 ≤ Real.sinh (r.length.toReal / 2) :=
      Real.sinh_nonneg_iff.mpr (by linarith [r.length_toReal_pos])
    have hle : Real.sinh (q.length.toReal / 2) * Real.sinh (r.length.toReal / 2) ≤
        Real.sinh (r.length.toReal / 2) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hq'.le hr0
    exact (not_le_of_gt (hle.trans_lt hr')) hprod

/-- The complete existential short-geodesic disjointness assertion, with one
universal witness, on each unchanged original hyperbolic surface. -/
theorem HyperbolicSurfaceModel.exists_short_closed_geodesic_disjointness
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q r : OriginalClosedGeodesic M,
      range q.curve ≠ range r.curve → q.length.toReal < δ → r.length.toReal < δ →
        Disjoint (range q.curve) (range r.curve) := by
  refine ⟨shortClosedGeodesicCutoff, shortClosedGeodesicCutoff_pos, ?_⟩
  intro q r hneq hq hr
  exact (q.trace_eq_or_disjoint_of_length_lt_shortCutoff r hq hr).resolve_left hneq

end LowDimensionalTopology.Geometry.Surfaces
