module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneDescendedFlatQuadratic

/-!
# A nondegenerate unit-area flat quadratic on the actual normalized torus

The explicit dz-descent premise produces a quadratic differential in the
unchanged original atlas. Its coefficients are nonzero on every chart target.
Its absolute line element pulls back to the positive constant flat metric,
and its literal period-domain area is one.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces
open LowDimensionalTopology.Unproved.Teichmuller

/-- A nonzero constant cover quadratic is nonzero on every original chart target. -/
theorem descendedFlatQuadratic_ne_zero (τ : ℍ) (h : NormalizedTorusDzDescent τ)
    {c : ℂ} (hc : c ≠ 0) :
    letI := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
    ∀ (x : ComplexTorusCarrier) (w : ℂ), w ∈ (chartAt ℂ x).target →
      (descendedFlatQuadratic τ h c : ComplexTorusCarrier → ℂ → ℂ) x w ≠ 0 := by
  let := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
  intro x w hw
  obtain ⟨z, hz⟩ := (normalizedTorusModel τ).surjective ((chartAt ℂ x).symm w)
  have hp : (normalizedTorusModel τ).projection z ∈ (chartAt ℂ x).source := by
    rw [hz]
    exact (chartAt ℂ x).map_target hw
  have he : (chartAt ℂ x) ((normalizedTorusModel τ).projection z) = w := by
    rw [hz]
    exact (chartAt ℂ x).right_inv hw
  have hdz := (descendedDz_spec τ h).2 x z hp
  rw [he] at hdz
  have hη : (descendedDz τ h).val x w ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hdz
    exact zero_ne_one hdz
  change c * ((descendedDz τ h).val x w) ^ 2 ≠ 0
  exact mul_ne_zero hc (pow_ne_zero 2 hη)

/-- The unit-area absolute quadratic line element is positive on every nonzero
coordinate vector in every original chart target. -/
theorem descendedUnitFlatQuadratic_lineElement_pos (τ : ℍ) (h : NormalizedTorusDzDescent τ) :
    letI := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
    ∀ (x : ComplexTorusCarrier) (w v : ℂ), w ∈ (chartAt ℂ x).target → v ≠ 0 →
      0 < ‖(descendedFlatQuadratic τ h ((τ.im⁻¹ : ℝ) : ℂ) :
        ComplexTorusCarrier → ℂ → ℂ) x w‖ * ‖v‖ ^ 2 := by
  let := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
  intro x w v hw hv
  have hc : ((τ.im⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (inv_ne_zero τ.im_ne_zero)
  exact mul_pos (norm_pos_iff.mpr (descendedFlatQuadratic_ne_zero τ h hc x w hw))
    (pow_pos (norm_pos_iff.mpr hv) 2)

/-- The concrete source normalization: a positive length density, the same native
quadratic line element on the actual cover, and its genuine period-domain area. -/
theorem descendedUnitFlatQuadratic_source (τ : ℍ) (h : NormalizedTorusDzDescent τ) :
    letI := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
    0 < normalizedTorusFlatDensity τ ∧
      (∀ (x : ComplexTorusCarrier) (z v : ℂ),
        (normalizedTorusModel τ).projection z ∈ (chartAt ℂ x).source →
        ‖(descendedFlatQuadratic τ h ((τ.im⁻¹ : ℝ) : ℂ) :
          ComplexTorusCarrier → ℂ → ℂ) x
            ((chartAt ℂ x) ((normalizedTorusModel τ).projection z))‖ *
          ‖deriv ((chartAt ℂ x) ∘ (normalizedTorusModel τ).projection) z * v‖ ^ 2 =
            normalizedTorusFlatDensity τ ^ 2 * ‖v‖ ^ 2) ∧
      (∫ z in normalizedTorusFlatDomain τ, descendedFlatCoverDensity τ h z
        ∂(volume : Measure ℂ)) = 1 := by
  let := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
  refine ⟨normalizedTorusFlatDensity_pos τ, ?_, integral_descendedFlatCoverDensity τ h⟩
  intro x z v hz
  rw [descendedFlatQuadratic_unit_lineElement τ h x z v hz,
    normalizedTorusFlatDensity_sq]
  exact div_eq_inv_mul _ _

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
