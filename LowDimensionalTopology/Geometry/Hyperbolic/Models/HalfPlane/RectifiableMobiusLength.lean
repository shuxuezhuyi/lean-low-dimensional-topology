module

public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.RectifiableMonotoneReparam
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.CurveLength
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Möbius invariance of the full continuous rectifiable Poincaré arclength

The original singular curve is compared with the transformed actual Euclidean
arclength factor through its genuine monotone variation clock. Only the factor
is differentiated. On its compact positive trace the actual Möbius map is
Lipschitz, and the native tangent identity preserves its weighted speed.
The zero-length case uses the same clock proof, without division by length.
-/

public section
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane Topology MatrixGroups ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The actual half-plane matrix action in ambient complex coordinates. Its
values away from the upper half-plane do not enter admissible curve lengths. -/
@[expose] def halfPlaneSLComplexAction
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) : ℂ :=
  ((A • UpperHalfPlane.ofComplex z : ℍ) : ℂ)

private theorem halfPlaneSLComplexAction_hasStrictDerivAt
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    HasStrictDerivAt (halfPlaneSLComplexAction A)
      ((1 : ℂ) / UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ A) z ^ 2)
      (z : ℂ) := by
  have hpos : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ A).val.det := by simp
  change HasStrictDerivAt
    (fun w : ℂ => (((Matrix.SpecialLinearGroup.mapGL ℝ A) •
      UpperHalfPlane.ofComplex w : ℍ) : ℂ))
    ((1 : ℂ) / UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ A) z ^ 2)
    (z : ℂ)
  simpa only [← Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.SpecialLinearGroup.det_mapGL, Units.val_one, Complex.ofReal_one] using
    UpperHalfPlane.hasStrictDerivAt_smul hpos z

/-- The genuine complex action is Lipschitz on every compact trace contained
in the upper half-plane, without a global boundary-distance assumption. -/
theorem halfPlaneSLComplexAction_exists_lipschitzOnWith
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) {K : Set ℂ} (hK : IsCompact K)
    (hpos : ∀ z ∈ K, 0 < z.im) :
    ∃ C : ℝ≥0, LipschitzOnWith C (halfPlaneSLComplexAction A) K := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro z hz
  let τ : ℍ := ⟨z, hpos z hz⟩
  obtain ⟨C, U, hU, hLip⟩ :=
    (halfPlaneSLComplexAction_hasStrictDerivAt A τ).hasStrictFDerivAt.exists_lipschitzOnWith
  exact ⟨C, U, mem_nhdsWithin_of_mem_nhds hU, hLip⟩

end LowDimensionalTopology.Geometry.Hyperbolic

namespace LowDimensionalTopology.Geometry.RectifiableCurve
open LowDimensionalTopology.Geometry.Hyperbolic

/-- Apply an actual matrix to the original continuous BV half-plane curve.
Both continuity and BV of the transformed curve are proved from its compact trace. -/
@[expose] def mapHalfPlaneSL2 (c : RectifiableCurve)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hpos : ∀ t ∈ Icc c.a c.b, 0 < (c.curve t).im) : RectifiableCurve where
  a := c.a
  b := c.b
  ordered := c.ordered
  curve := halfPlaneSLComplexAction A ∘ c.curve
  continuous := by
    have hK := isCompact_Icc.image_of_continuousOn c.continuous
    obtain ⟨C, hLip⟩ := halfPlaneSLComplexAction_exists_lipschitzOnWith A hK
      (by rintro z ⟨t, ht, rfl⟩; exact hpos t ht)
    exact hLip.continuousOn.comp c.continuous (mapsTo_image c.curve _)
  boundedVariation := by
    have hK := isCompact_Icc.image_of_continuousOn c.continuous
    obtain ⟨C, hLip⟩ := halfPlaneSLComplexAction_exists_lipschitzOnWith A hK
      (by rintro z ⟨t, ht, rfl⟩; exact hpos t ht)
    exact hLip.comp_boundedVariationOn (mapsTo_image c.curve _) c.boundedVariation

/-- An actual matrix preserves the full Poincaré line integral for every
continuous rectifiable half-plane curve, including singular parametrizations,
pauses and repeated traversals. No derivative of the original curve is used. -/
theorem mapHalfPlaneSL2_weightedLength (c : RectifiableCurve)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hpos : ∀ t ∈ Icc c.a c.b, 0 < (c.curve t).im) :
    (c.mapHalfPlaneSL2 A hpos).weightedLength
        (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) =
      c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) := by
  let ρ : ℂ → ℝ≥0∞ := fun ζ => ENNReal.ofReal (1 / ζ.im)
  have hρ : Measurable ρ := by fun_prop
  have hfactorpos (u : ℝ) (hu : u ∈ Icc 0 c.euclideanLength) :
      0 < (c.arclengthFactor u).im := by
    rw [← c.clock_spec.2.2.2.2] at hu
    obtain ⟨t, ht, htu⟩ := hu
    have heq : c.curve t = c.arclengthFactor u := by
      simpa only [Function.comp_apply, htu] using c.arclengthFactor_spec.2.1 ht
    rw [← heq]
    exact hpos t ht
  let n : RectifiableCurve :=
    { a := 0
      b := c.euclideanLength
      ordered := c.clock_spec.1
      curve := c.arclengthFactor
      continuous := c.arclengthFactor_spec.1.continuous.continuousOn
      boundedVariation := by
        simpa only [Function.comp_id] using c.arclengthFactor_spec.1.comp_boundedVariationOn
          (BoundedVariationOn.id_Icc 0 c.euclideanLength) }
  let m := n.mapHalfPlaneSL2 A hfactorpos
  have hnormalized : (c.mapHalfPlaneSL2 A hpos).weightedLength ρ = m.weightedLength ρ := by
    apply weightedLength_eq_of_monotone_onto_reparam
      (c.mapHalfPlaneSL2 A hpos) m c.clock c.clock_spec.2.2.1 c.clock_spec.2.2.2.2
      c.clock_spec.2.2.2.1 rfl
    intro t ht
    change halfPlaneSLComplexAction A (c.curve t) =
      halfPlaneSLComplexAction A (c.arclengthFactor (c.clock t))
    exact congrArg (halfPlaneSLComplexAction A) (c.arclengthFactor_spec.2.1 ht)
  obtain ⟨C, hLip⟩ := halfPlaneSLComplexAction_exists_lipschitzOnWith A
    (isCompact_Icc.image_of_continuousOn c.arclengthFactor_spec.1.continuous.continuousOn)
    (by rintro z ⟨t, ht, rfl⟩; exact hfactorpos t ht)
  have hmLip : LipschitzOnWith (C * 1) m.curve (Icc 0 c.euclideanLength) :=
    hLip.comp c.arclengthFactor_spec.1.lipschitzOnWith
      (mapsTo_image c.arclengthFactor _)
  have hdiff : ∀ᵐ t : ℝ ∂volume, DifferentiableAt ℝ c.arclengthFactor t :=
    c.arclengthFactor_spec.1.ae_differentiableAt
  have hlength : m.weightedLength ρ = c.weightedLength ρ := by
    rw [m.weightedLength_eq_lintegral_deriv hmLip hρ]
    change (∫⁻ t in Ioo 0 c.euclideanLength, ρ (m.curve t) * ‖deriv m.curve t‖ₑ) =
      ∫⁻ t in Ioo 0 c.euclideanLength, ρ (c.arclengthFactor t)
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hdiff, c.arclengthFactor_unit_speed,
      ae_restrict_mem measurableSet_Ioo] with t hdt hunit ht
    let τ : ℍ := ⟨c.arclengthFactor t, hfactorpos t (Ioo_subset_Icc_self ht)⟩
    have hin : HasDerivAt c.arclengthFactor (deriv c.arclengthFactor t) t :=
      hdt.hasDerivAt
    have hout : HasDerivAt (halfPlaneSLComplexAction A)
        ((1 : ℂ) / UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ A) τ ^ 2)
        (c.arclengthFactor t) :=
      (halfPlaneSLComplexAction_hasStrictDerivAt A τ).hasDerivAt
    have hcomp : HasDerivAt (halfPlaneSLComplexAction A ∘ c.arclengthFactor)
        (deriv c.arclengthFactor t •
          ((1 : ℂ) / UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ A) τ ^ 2)) t :=
      hout.scomp t hin
    have hderiv : deriv m.curve t =
        ((1 : ℂ) / UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ A) τ ^ 2) *
          deriv c.arclengthFactor t := by
      change deriv (halfPlaneSLComplexAction A ∘ c.arclengthFactor) t = _
      calc
        _ = deriv c.arclengthFactor t •
            ((1 : ℂ) / UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ A) τ ^ 2) :=
          hcomp.deriv
        _ = _ := by rw [smul_eq_mul, mul_comm]
    have hmap : m.curve t = ((A • τ : ℍ) : ℂ) := by
      change ((A • UpperHalfPlane.ofComplex (τ : ℂ) : ℍ) : ℂ) = ((A • τ : ℍ) : ℂ)
      rw [UpperHalfPlane.ofComplex_apply]
    have hspeed : ρ (m.curve t) * ‖deriv m.curve t‖ₑ =
        ρ (c.arclengthFactor t) * ‖deriv c.arclengthFactor t‖ₑ := by
      rw [hderiv, hmap]
      simp only [ρ, ← ofReal_norm]
      change ENNReal.ofReal (1 / (A • τ).im) *
          ENNReal.ofReal ‖((1 : ℂ) /
            UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ A) τ ^ 2) *
              deriv c.arclengthFactor t‖ =
        ENNReal.ofReal (1 / τ.im) * ENNReal.ofReal ‖deriv c.arclengthFactor t‖
      rw [← ENNReal.ofReal_mul (one_div_nonneg.mpr (A • τ).im_pos.le),
        ← ENNReal.ofReal_mul (one_div_nonneg.mpr τ.im_pos.le)]
      apply congrArg ENNReal.ofReal
      simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
        sl2_weighted_tangent_norm A τ (deriv c.arclengthFactor t)
    rw [hspeed, hunit, mul_one]
  exact hnormalized.trans hlength

end LowDimensionalTopology.Geometry.RectifiableCurve
