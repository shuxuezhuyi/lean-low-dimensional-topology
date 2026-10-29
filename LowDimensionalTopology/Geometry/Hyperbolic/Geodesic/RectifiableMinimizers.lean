module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.RectifiableDistance
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.RectifiableWeightedSubpaths
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.ContinuousSegmentTraversal

/-! # The full rectifiable minimizing disk arc has the unique geometric trace -/

public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Every continuous rectifiable disk minimizer has exactly the genuine geometric
segment as its trace. Repeated traversals are accounted for by the length premise. -/
theorem rectifiable_trace_eq_closedDiscHSegment_of_minimizing
    (c : RectifiableCurve) {z w : 𝔻} (hzw : z ≠ w)
    (hc : c.IsPathIn LiZhongQC.unitDisc z w)
    (hmin : c.weightedLength
      (fun ζ => ENNReal.ofReal (LiZhongQC.poincareDensityDisc ζ)) =
        ENNReal.ofReal (discPathDist z w)) :
    c.curve '' Icc c.a c.b = ((↑) : 𝔻 → ℂ) '' closedDiscHSegment z w := by
  let ρ : ℂ → ℝ≥0∞ := fun ζ => ENNReal.ofReal (LiZhongQC.poincareDensityDisc ζ)
  have hρ : Measurable ρ := measurable_disc_poincareDensity
  have hdist (u v : 𝔻) : LiZhongQC.metricDist LiZhongQC.unitDisc ρ u v =
      ENNReal.ofReal (discPathDist u v) :=
    (rectifiableMetricDist_eq_metricDist _ hρ (u : ℂ) (v : ℂ)).symm.trans
      (discRectifiableEDist_eq_pathDist u v)
  have hnonneg (u v : 𝔻) : 0 ≤ discPathDist u v := by
    rw [discPathDist_eq_halfPlane]; exact dist_nonneg
  have hD : c.normalizedParam '' Icc 0 1 ⊆ LiZhongQC.unitDisc := by
    change c.normalizedCurve.closedTrace ⊆ _
    rw [c.normalizedCurve_closedTrace]
    exact hc.2.2
  let η : ℝ → 𝔻 := fun t => ⟨c.normalizedParam (projIcc 0 1 zero_le_one t),
    hD ⟨_, (projIcc 0 1 zero_le_one t).property, rfl⟩⟩
  have hηval {t : ℝ} (ht : t ∈ Icc 0 1) : (η t : ℂ) = c.normalizedParam t := by
    change c.normalizedParam (projIcc 0 1 zero_le_one t) = _
    rw [projIcc_of_mem zero_le_one ht]
  have hηcont : Continuous η := by
    apply Complex.UnitDisc.isEmbedding_coe.continuous_iff.mpr
    exact c.normalizedParam_lipschitz.continuous.comp
      (continuous_subtype_val.comp continuous_projIcc)
  have hη0 : η 0 = z := by
    apply Complex.UnitDisc.coe_injective
    rw [hηval ⟨le_rfl, zero_le_one⟩]
    exact c.normalizedCurve_endpoints.1.trans hc.1
  have hη1 : η 1 = w := by
    apply Complex.UnitDisc.coe_injective
    rw [hηval ⟨zero_le_one, le_rfl⟩]
    exact c.normalizedCurve_endpoints.2.trans hc.2.1
  have htotal : (∫⁻ r in Ioo 0 1, ρ (c.normalizedParam r) *
      ‖deriv c.normalizedParam r‖ₑ) = ENNReal.ofReal (discPathDist z w) := by
    change c.normalizedCurve.rhoLength ρ = _
    rw [c.normalizedCurve_rhoLength hρ]
    exact hmin
  have hsub : η '' Icc 0 1 ⊆ closedDiscHSegment z w := by
    rintro _ ⟨t, ht, rfl⟩
    have hbound := metricDist_add_le_lipschitz_length
      c.normalizedParam_lipschitz hD ht hρ
    rw [← hηval ⟨le_rfl, zero_le_one⟩, ← hηval ht,
      ← hηval ⟨zero_le_one, le_rfl⟩, hη0, hη1, hdist, hdist, htotal] at hbound
    rw [← ENNReal.ofReal_add (hnonneg z (η t)) (hnonneg (η t) w)] at hbound
    have hle := (ENNReal.ofReal_le_ofReal_iff (hnonneg z w)).mp hbound
    have htri : discPathDist z w ≤ discPathDist z (η t) + discPathDist (η t) w := by
      simp only [discPathDist_eq_halfPlane]
      exact dist_triangle _ _ _
    exact (disc_triangle_eq_iff_mem_closedDiscHSegment hzw).mp (le_antisymm hle htri)
  have htrace := image_eq_closedDiscHSegment_of_subset hzw
    hηcont.continuousOn hη0 hη1 hsub
  calc
    c.curve '' Icc c.a c.b = c.normalizedParam '' Icc 0 1 :=
      c.normalizedCurve_closedTrace.symm
    _ = ((↑) : 𝔻 → ℂ) '' (η '' Icc 0 1) := by
      rw [image_image]
      simpa only [Function.comp_def] using
        (show EqOn c.normalizedParam (((↑) : 𝔻 → ℂ) ∘ η) (Icc 0 1) from
          fun t ht => (hηval ht).symm).image_eq
    _ = _ := by rw [htrace]

/-- A zero-length rectifiable disk loop has only its basepoint in its trace. -/
theorem rectifiable_trace_eq_singleton_of_length_zero
    (c : RectifiableCurve) {z : 𝔻}
    (hc : c.IsPathIn LiZhongQC.unitDisc z z)
    (hzero : c.weightedLength
      (fun ζ => ENNReal.ofReal (LiZhongQC.poincareDensityDisc ζ)) = 0) :
    c.curve '' Icc c.a c.b = {(z : ℂ)} := by
  let ρ : ℂ → ℝ≥0∞ := fun ζ => ENNReal.ofReal (LiZhongQC.poincareDensityDisc ζ)
  have hρ : Measurable ρ := measurable_disc_poincareDensity
  have hD : c.normalizedParam '' Icc 0 1 ⊆ LiZhongQC.unitDisc := by
    change c.normalizedCurve.closedTrace ⊆ _
    rw [c.normalizedCurve_closedTrace]
    exact hc.2.2
  have h0 : c.normalizedParam 0 = (z : ℂ) := c.normalizedCurve_endpoints.1.trans hc.1
  have htotal : (∫⁻ r in Ioo 0 1, ρ (c.normalizedParam r) *
      ‖deriv c.normalizedParam r‖ₑ) = 0 := by
    change c.normalizedCurve.rhoLength ρ = _
    rw [c.normalizedCurve_rhoLength hρ]
    exact hzero
  rw [← c.normalizedCurve_closedTrace]
  refine subset_antisymm ?_ (singleton_subset_iff.mpr ?_)
  · rintro _ ⟨t, ht, rfl⟩
    change c.normalizedParam t = (z : ℂ)
    let v : 𝔻 := ⟨c.normalizedParam t, hD ⟨t, ht, rfl⟩⟩
    have hbound := metricDist_add_le_lipschitz_length
      c.normalizedParam_lipschitz hD ht hρ
    rw [h0, htotal] at hbound
    have hle : LiZhongQC.metricDist LiZhongQC.unitDisc ρ z v ≤ 0 :=
      le_trans le_self_add hbound
    have hdist : LiZhongQC.metricDist LiZhongQC.unitDisc ρ z v =
        ENNReal.ofReal (discPathDist z v) :=
      (rectifiableMetricDist_eq_metricDist _ hρ (z : ℂ) (v : ℂ)).symm.trans
        (discRectifiableEDist_eq_pathDist z v)
    rw [hdist] at hle
    have hd : discPathDist z v ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp (le_antisymm hle bot_le)
    rw [discPathDist_eq_halfPlane] at hd
    have hzv : z = v := cayleyHomeomorph.symm.injective
      (dist_eq_zero.mp (le_antisymm hd dist_nonneg))
    exact congrArg ((↑) : 𝔻 → ℂ) hzv.symm
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, h0⟩

end LowDimensionalTopology.Geometry.Hyperbolic
