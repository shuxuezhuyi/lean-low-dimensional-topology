module

public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.RectifiableMonotoneReparam
public import Mathlib.Topology.Order.IntermediateValue

/-! # Literal affine normalization of an actual continuous BV curve -/

public section
noncomputable section
open Set
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.RectifiableCurve

/-- The actual affine parameter map stays in the complete original interval. -/
theorem unitAffine_maps (c : RectifiableCurve) :
    MapsTo (fun t : ℝ => c.a + (c.b - c.a) * t) (Icc 0 1) (Icc c.a c.b) := by
  intro t ht
  have hlo := mul_nonneg (sub_nonneg.mpr c.ordered) ht.1
  have hhi := mul_le_of_le_one_right (sub_nonneg.mpr c.ordered) ht.2
  constructor <;> linarith

/-- The actual affine parameter map is monotone, including a degenerate interval. -/
theorem unitAffine_mono (c : RectifiableCurve) :
    Monotone (fun t : ℝ => c.a + (c.b - c.a) * t) := by
  intro s t hst
  have hmul := mul_le_mul_of_nonneg_left hst (sub_nonneg.mpr c.ordered)
  change c.a + (c.b - c.a) * s ≤ c.a + (c.b - c.a) * t
  linarith

/-- Normalize only the parameter interval by its actual affine map. The
original trace, repetitions and full BV data are preserved, including `a=b`. -/
@[expose] def unitAffine (c : RectifiableCurve) : RectifiableCurve where
  a := 0
  b := 1
  ordered := zero_le_one
  curve := fun t => c.curve (c.a + (c.b - c.a) * t)
  continuous := c.continuous.comp (by fun_prop) (unitAffine_maps c)
  boundedVariation := by
    apply ne_of_lt
    exact lt_of_le_of_lt
      (eVariationOn.comp_le_of_monotoneOn c.curve
        (fun t => c.a + (c.b - c.a) * t) ((unitAffine_mono c).monotoneOn (Icc 0 1)) (unitAffine_maps c))
      (lt_top_iff_ne_top.mpr c.boundedVariation)

/-- Affine interval normalization preserves the actual full weighted
arclength, rather than only the geometric image. -/
theorem unitAffine_weightedLength (c : RectifiableCurve) (ρ : ℂ → ℝ≥0∞) :
    c.unitAffine.weightedLength ρ = c.weightedLength ρ := by
  apply weightedLength_eq_of_monotone_onto_reparam c.unitAffine c
    (fun t => c.a + (c.b - c.a) * t) ((unitAffine_mono c).monotoneOn (Icc 0 1))
  · change (fun t : ℝ => c.a + (c.b - c.a) * t) '' Icc 0 1 = Icc c.a c.b
    simpa using (show ContinuousOn (fun t : ℝ => c.a + (c.b - c.a) * t) (Icc 0 1)
      from by fun_prop).image_Icc_of_monotoneOn zero_le_one ((unitAffine_mono c).monotoneOn (Icc 0 1))
  · simp [unitAffine]
  · simp [unitAffine]
  · intro t _ht
    rfl

end LowDimensionalTopology.Geometry.RectifiableCurve
