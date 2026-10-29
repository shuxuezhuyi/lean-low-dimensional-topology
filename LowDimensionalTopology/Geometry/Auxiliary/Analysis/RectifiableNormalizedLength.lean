module

public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.RectifiableWeightedLength
public import LowDimensionalTopology.External.LiZhongQC.Ch03.S14_PoincareMetric

/-!
# Lossless normalized Lipschitz representatives of rectifiable curves

The representative traverses the original curve in its actual arclength clock.
Its weighted source length is exactly the original rectifiable line integral,
for every Borel nonnegative density, including all traversal multiplicities.
-/

public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.RectifiableCurve

/-- The actual arclength factor, rescaled without division to `[0,1]`. -/
@[expose] def normalizedParam (c : RectifiableCurve) (t : ℝ) : ℂ :=
  c.arclengthFactor (c.euclideanLength * t)

theorem normalizedParam_lipschitz (c : RectifiableCurve) :
    LipschitzWith (Real.toNNReal c.euclideanLength) c.normalizedParam := by
  have hL := c.clock_spec.1
  have hlin : LipschitzWith (Real.toNNReal c.euclideanLength)
      (fun t : ℝ => c.euclideanLength * t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.coe_toNNReal _ hL, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hL]
    exact le_rfl
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [normalizedParam, one_mul, Function.comp_apply] using
    (c.arclengthFactor_spec.1.comp hlin).dist_le_mul x y

/-- A genuine source Lipschitz curve, available for every continuous BV curve. -/
@[expose] def normalizedCurve (c : RectifiableCurve) : LiZhongQC.LRCurve where
  toFun := c.normalizedParam
  locallyLipschitzOn := c.normalizedParam_lipschitz.locallyLipschitz.locallyLipschitzOn

/-- Exact variation in the normalized parameter. The clock includes every wrap,
and remains valid for a constant original curve. -/
theorem normalized_clock (c : RectifiableCurve) {t : ℝ} (ht : t ∈ Icc 0 1) :
    variationOnFromTo c.normalizedParam (Icc 0 1) 0 t = c.euclideanLength * t := by
  have hL := c.clock_spec.1
  have hLt0 : 0 ≤ c.euclideanLength * t := mul_nonneg hL ht.1
  have hLtL : c.euclideanLength * t ≤ c.euclideanLength := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 hL
  have hmono : MonotoneOn (fun r : ℝ => c.euclideanLength * r) (Icc 0 t) := by
    intro x _ y _ hxy
    exact mul_le_mul_of_nonneg_left hxy hL
  have himage : (fun r : ℝ => c.euclideanLength * r) '' Icc 0 t =
      Icc 0 (c.euclideanLength * t) := by
    have hcont : ContinuousOn (fun r : ℝ => c.euclideanLength * r) (Icc 0 t) :=
      (continuous_const.mul continuous_id).continuousOn
    simpa only [mul_zero] using hcont.image_Icc_of_monotoneOn ht.1 hmono
  rw [variationOnFromTo.eq_of_le c.normalizedParam (Icc 0 1) ht.1,
    inter_eq_right.mpr (Icc_subset_Icc le_rfl ht.2)]
  change (eVariationOn (c.arclengthFactor ∘ fun r : ℝ => c.euclideanLength * r)
    (Icc 0 t)).toReal = _
  rw [eVariationOn.comp_eq_of_monotoneOn c.arclengthFactor _ hmono, himage,
    c.arclengthFactor_spec.2.2 0 (c.euclideanLength * t)
      ⟨le_rfl, hL⟩ ⟨hLt0, hLtL⟩ hLt0,
    sub_zero, ENNReal.toReal_ofReal hLt0]

theorem normalizedCurve_endpoints (c : RectifiableCurve) :
    c.normalizedCurve.toFun 0 = c.curve c.a ∧
      c.normalizedCurve.toFun 1 = c.curve c.b := by
  have ha := c.arclengthFactor_spec.2.1 ⟨le_rfl, c.ordered⟩
  have hb := c.arclengthFactor_spec.2.1 ⟨c.ordered, le_rfl⟩
  constructor
  · simpa only [normalizedCurve, normalizedParam, Function.comp_apply, mul_zero,
      c.clock_spec.2.2.2.1] using ha.symm
  · simpa only [normalizedCurve, normalizedParam, Function.comp_apply, mul_one,
      euclideanLength] using hb.symm

theorem normalizedCurve_closedTrace (c : RectifiableCurve) :
    c.normalizedCurve.closedTrace = c.curve '' Icc c.a c.b := by
  have hL := c.clock_spec.1
  have hmono : MonotoneOn (fun t : ℝ => c.euclideanLength * t) (Icc 0 1) := by
    intro x _ y _ hxy
    exact mul_le_mul_of_nonneg_left hxy hL
  have himage : (fun t : ℝ => c.euclideanLength * t) '' Icc 0 1 =
      Icc 0 c.euclideanLength := by
    have hcont : ContinuousOn (fun t : ℝ => c.euclideanLength * t) (Icc 0 1) :=
      (continuous_const.mul continuous_id).continuousOn
    simpa only [mul_zero, mul_one] using
      hcont.image_Icc_of_monotoneOn zero_le_one hmono
  change (fun t : ℝ => c.arclengthFactor (c.euclideanLength * t)) '' Icc 0 1 = _
  rw [← image_image, himage, ← c.clock_spec.2.2.2.2, image_image]
  simpa only [Function.comp_def] using c.arclengthFactor_spec.2.1.symm.image_eq

/-- Lossless agreement for every Borel density, proved from the actual normalized
variation clock rather than equality of the two image sets. -/
theorem normalizedCurve_rhoLength (c : RectifiableCurve) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) : c.normalizedCurve.rhoLength ρ = c.weightedLength ρ := by
  let d := ofLRCurve c.normalizedCurve c.normalizedParam_lipschitz.lipschitzOnWith
  have hdclock (t : ℝ) (ht : t ∈ Icc 0 1) : d.clock t = c.euclideanLength * t :=
    c.normalized_clock ht
  have hdlength : d.euclideanLength = c.euclideanLength := by
    change d.clock 1 = _
    rw [hdclock 1 ⟨zero_le_one, le_rfl⟩, mul_one]
  have hfactor : EqOn d.curve (c.arclengthFactor ∘ d.clock) (Icc d.a d.b) := by
    intro t ht
    change c.arclengthFactor (c.euclideanLength * t) = c.arclengthFactor (d.clock t)
    rw [hdclock t ht]
  calc
    c.normalizedCurve.rhoLength ρ = d.weightedLength ρ :=
      (weightedLength_ofLRCurve c.normalizedCurve
        c.normalizedParam_lipschitz.lipschitzOnWith hρ).symm
    _ = ∫⁻ t in Ioo 0 d.euclideanLength, ρ (c.arclengthFactor t) :=
      d.weightedLength_eq_of_factor ρ hfactor
    _ = c.weightedLength ρ := by rw [hdlength]; rfl

/-- Every rectifiable curve in a domain has a source-admissible Lipschitz
representative with the same endpoints and all weighted lengths. -/
theorem normalizedCurve_isPathIn (c : RectifiableCurve) {D : Set ℂ}
    (hD : c.curve '' Icc c.a c.b ⊆ D) :
    LiZhongQC.IsPathIn D (c.curve c.a) (c.curve c.b) c.normalizedCurve := by
  exact ⟨⟨_, c.normalizedParam_lipschitz.lipschitzOnWith⟩,
    c.normalizedCurve_endpoints.1, c.normalizedCurve_endpoints.2,
    by rw [c.normalizedCurve_closedTrace]; exact hD⟩

end LowDimensionalTopology.Geometry.RectifiableCurve
