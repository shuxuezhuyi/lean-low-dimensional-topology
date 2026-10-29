module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.RectifiableDistance
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.RectifiableWeightedSubpaths
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.ContinuousSegmentTraversal

/-!
# Full rectifiable half-plane minimizers have the unique geodesic trace

The original continuous BV curve is retained, including singular parameters.
Only its normalized Lipschitz traversal is used inside the proof. The resulting
trace statement therefore applies directly to a book geodesic arc, without
requiring the original parameter to be unit-speed or absolutely continuous.
-/

public section
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane ENNReal

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Every actual continuous rectifiable half-plane minimizer has precisely the
genuine hyperbolic segment as its original trace, for arbitrary parameters. -/
theorem rectifiable_trace_eq_closedHSegment_of_minimizing
    (c : RectifiableCurve) {z w : ℍ} (hzw : z ≠ w)
    (hc : c.IsPathIn LiZhongQC.upperHalf z w)
    (hmin : c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) =
      ENNReal.ofReal (dist z w)) :
    c.curve '' Icc c.a c.b = ((↑) : ℍ → ℂ) '' closedHSegment z w := by
  let ρ : ℂ → ℝ≥0∞ := fun ζ => ENNReal.ofReal (1 / ζ.im)
  have hρ : Measurable ρ := measurable_halfPlane_poincareDensity
  have hdist (u v : ℍ) : LiZhongQC.metricDist LiZhongQC.upperHalf ρ u v =
      ENNReal.ofReal (dist u v) :=
    (rectifiableMetricDist_eq_metricDist _ hρ (u : ℂ) (v : ℂ)).symm.trans
      (halfPlane_rectifiable_distance u v)
  have hD : c.normalizedParam '' Icc 0 1 ⊆ LiZhongQC.upperHalf := by
    change c.normalizedCurve.closedTrace ⊆ _
    rw [c.normalizedCurve_closedTrace]
    exact hc.2.2
  let η : ℝ → ℍ := fun t =>
    ⟨c.normalizedParam (projIcc 0 1 zero_le_one t),
      hD ⟨_, (projIcc 0 1 zero_le_one t).property, rfl⟩⟩
  have hηval {t : ℝ} (ht : t ∈ Icc 0 1) : (η t : ℂ) = c.normalizedParam t := by
    change c.normalizedParam (projIcc 0 1 zero_le_one t) = _
    rw [projIcc_of_mem zero_le_one ht]
  have hηcont : Continuous η :=
    Continuous.upperHalfPlaneMk
      (c.normalizedParam_lipschitz.continuous.comp
        (continuous_subtype_val.comp continuous_projIcc)) _
  have hη0 : η 0 = z := by
    apply UpperHalfPlane.ext
    rw [hηval ⟨le_rfl, zero_le_one⟩]
    exact c.normalizedCurve_endpoints.1.trans hc.1
  have hη1 : η 1 = w := by
    apply UpperHalfPlane.ext
    rw [hηval ⟨zero_le_one, le_rfl⟩]
    exact c.normalizedCurve_endpoints.2.trans hc.2.1
  have htotal : (∫⁻ r in Ioo 0 1, ρ (c.normalizedParam r) *
      ‖deriv c.normalizedParam r‖ₑ) = ENNReal.ofReal (dist z w) := by
    change c.normalizedCurve.rhoLength ρ = _
    rw [c.normalizedCurve_rhoLength hρ]
    exact hmin
  have hsub : η '' Icc 0 1 ⊆ closedHSegment z w := by
    rintro _ ⟨t, ht, rfl⟩
    have hbound := metricDist_add_le_lipschitz_length
      c.normalizedParam_lipschitz hD ht hρ
    rw [← hηval ⟨le_rfl, zero_le_one⟩, ← hηval ht,
      ← hηval ⟨zero_le_one, le_rfl⟩, hη0, hη1, hdist, hdist, htotal] at hbound
    rw [← ENNReal.ofReal_add dist_nonneg dist_nonneg] at hbound
    have hle : dist z (η t) + dist (η t) w ≤ dist z w :=
      (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hbound
    exact mem_closedHSegment_of_dist_triangle_eq hzw
      (le_antisymm hle (dist_triangle z (η t) w))
  have htrace := image_eq_closedHSegment_of_subset hzw hηcont.continuousOn hη0 hη1 hsub
  calc
    c.curve '' Icc c.a c.b = c.normalizedParam '' Icc 0 1 :=
      c.normalizedCurve_closedTrace.symm
    _ = ((↑) : ℍ → ℂ) '' (η '' Icc 0 1) := by
      rw [image_image]
      simpa only [Function.comp_def] using
        (show EqOn c.normalizedParam (((↑) : ℍ → ℂ) ∘ η) (Icc 0 1) from
          fun t ht => (hηval ht).symm).image_eq
    _ = _ := by rw [htrace]

end LowDimensionalTopology.Geometry.Hyperbolic
