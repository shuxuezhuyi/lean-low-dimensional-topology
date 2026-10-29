module

public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicAxes
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicSegments
public import Mathlib.Tactic.Ring

/-!
# A genuine unit-speed periodic geodesic for every hyperbolic matrix

The actual normalizing matrix conjugates the given transformation to a
positive vertical dilation. The sign of its logarithm chooses the orientation,
and the period is the full translation length of the original matrix. No
primitive generator is selected.
-/

public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Every actual hyperbolic matrix has a complete unit-speed axis parameter
with its full positive translation length as the actual equivariant period. -/
theorem exists_unitSpeed_axis_with_actual_period
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2) :
    ∃ γ : ℝ → ℍ, IsHGeodesicParam γ ∧
      range γ = (hHyperbolicAxis A hA ht).carrier ∧
      0 < hTranslationLength (hSLIsometry A) ∧
      ∀ t : ℝ, γ (t + hTranslationLength (hSLIsometry A)) = A • γ t := by
  obtain ⟨s, k, hk, _hk1, haxis, hlen, hact⟩ :=
    hHyperbolicAxis_normalizer A hA ht
  let β : ℝ → ℍ := fun t => s⁻¹ • imaginaryAxisParam t
  have hβrange : range β = (hHyperbolicAxis A hA ht).carrier := by
    rw [haxis]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      change (s • (s⁻¹ • imaginaryAxisParam t)).re = 0
      rw [smul_inv_smul]
      rfl
    · intro hz
      refine ⟨Real.log (s • z).im, ?_⟩
      apply (hSLIsometry s).injective
      change s • (s⁻¹ • imaginaryAxisParam (Real.log (s • z).im)) = s • z
      rw [smul_inv_smul]
      apply UpperHalfPlane.ext
      apply Complex.ext
      · change 0 = (s • z).re
        exact hz.symm
      · change Real.exp (Real.log (s • z).im) = (s • z).im
        exact Real.exp_log (s • z).im_pos
  have hβ : IsHGeodesicParam β :=
    ⟨(isometry_smul ℍ s⁻¹).comp imaginaryAxisParam_isometry,
      hβrange.symm ▸ (hHyperbolicAxis A hA ht).isHLine⟩
  have himag (t : ℝ) :
      imaginaryAxisParam (t + Real.log k) = verticalDilationSL k hk • imaginaryAxisParam t := by
    apply UpperHalfPlane.ext
    rw [imaginaryAxisParam_coe, verticalDilationSL_coe, imaginaryAxisParam_coe,
      Real.exp_add, Real.exp_log hk, Complex.ofReal_mul]
    ring
  have hbase (t : ℝ) : β (t + Real.log k) = A • β t := by
    apply (hSLIsometry s).injective
    change s • (s⁻¹ • imaginaryAxisParam (t + Real.log k)) =
      s • (A • (s⁻¹ • imaginaryAxisParam t))
    rw [smul_inv_smul]
    calc
      imaginaryAxisParam (t + Real.log k) =
          verticalDilationSL k hk • imaginaryAxisParam t := himag t
      _ = (s * A * s⁻¹) • imaginaryAxisParam t := (hact _).symm
      _ = s • (A • (s⁻¹ • imaginaryAxisParam t)) := by simp only [mul_smul]
  have hpositive := hHyperbolic_translationLength_pos A hA ht
  rcases le_total 0 (Real.log k) with hlog | hlog
  · have hperiod (t : ℝ) :
        β (t + hTranslationLength (hSLIsometry A)) = A • β t := by
      rw [hlen, abs_of_nonneg hlog]
      exact hbase t
    exact ⟨β, hβ, hβrange, hpositive, hperiod⟩
  · let γ : ℝ → ℍ := fun t => β (-t)
    have hrange : range γ = range β := by
      ext z
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨-t, rfl⟩
      · rintro ⟨t, rfl⟩
        exact ⟨-t, by change β (- -t) = β t; rw [neg_neg]⟩
    have hγ : IsHGeodesicParam γ :=
      ⟨hβ.1.comp (show Isometry (fun t : ℝ => -t) from isometry_neg),
        hrange.symm ▸ hβ.2⟩
    have hperiod (t : ℝ) :
        γ (t + hTranslationLength (hSLIsometry A)) = A • γ t := by
      change β (-(t + hTranslationLength (hSLIsometry A))) = A • β (-t)
      rw [hlen, abs_of_nonpos hlog]
      have hparam : -(t + -Real.log k) = -t + Real.log k := by ring
      rw [hparam]
      exact hbase (-t)
    exact ⟨γ, hγ, hrange.trans hβrange, hpositive, hperiod⟩

end LowDimensionalTopology.Geometry.Hyperbolic
