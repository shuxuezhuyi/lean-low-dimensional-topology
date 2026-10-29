module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.RectifiableDistance

/-! # Genuine rectifiable Poincaré minimizers, including coincident endpoints -/

public section
noncomputable section

open Set MeasureTheory LiZhongQC
open scoped ENNReal NNReal ComplexConjugate Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- A complex radial segment is an actual source path, including the zero segment. -/
private theorem isPathIn_complex_segCurve {v : ℂ} (hv : ‖v‖ < 1) :
    IsPathIn unitDisc 0 v (segCurve v) := by
  refine ⟨⟨‖v‖₊, ?_⟩, by simp, by simp, ?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro a _ b _
    apply le_of_eq
    rw [segCurve_apply, segCurve_apply, Complex.dist_eq, ← sub_mul, ← Complex.ofReal_sub,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.dist_eq, coe_nnnorm, mul_comm]
  · rintro _ ⟨t, ht, rfl⟩
    apply mem_ball_zero_iff.mpr
    rw [segCurve_norm ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg v) ht.2).trans_lt hv

/-- Every pair of disk points admits a genuine continuous rectifiable curve
whose literal weighted arclength is the full Poincaré distance. -/
private theorem exists_rectifiable_disk_minimizer_data (z w : 𝔻) :
    ∃ c : RectifiableCurve, c.IsPathIn unitDisc z w ∧
      c.weightedLength (fun ζ => ENNReal.ofReal (poincareDensityDisc ζ)) =
        ENNReal.ofReal (discPathDist z w) ∧
      (z ≠ w → InjOn c.curve (Icc c.a c.b)) := by
  let ρ : ℂ → ℝ≥0∞ := fun ζ => ENNReal.ofReal (poincareDensityDisc ζ)
  let v : ℂ := blaschke z w
  have hv : ‖v‖ < 1 := blaschke_mem_unitDisc z.norm_lt_one w.norm_lt_one
  have hz : ‖-(z : ℂ)‖ < 1 := by simpa only [norm_neg] using z.norm_lt_one
  have hseg := isPathIn_complex_segCurve hv
  have hgmaps : MapsTo (blaschke (-(z : ℂ))) unitDisc unitDisc :=
    (isConformalOnto_blaschke hz).mapsTo
  obtain ⟨γ, hγeq, hγpath⟩ := exists_isPathIn_comp Metric.isOpen_ball
    (differentiableOn_blaschke hz) hgmaps hseg
  have hg0 : blaschke (-(z : ℂ)) 0 = (z : ℂ) := by simp [blaschke]
  have hgv : blaschke (-(z : ℂ)) v = (w : ℂ) :=
    blaschke_neg_blaschke z.norm_lt_one w.norm_lt_one
  rw [hg0, hgv] at hγpath
  have hlenγ : γ.rhoLength ρ = (segCurve v).rhoLength ρ := by
    apply rhoLength_comp_rotBlaschke (c := 1) (a := -(z : ℂ)) (by simp) hz
    · rintro _ ⟨t, ht, rfl⟩
      exact hseg.2.2.2 ⟨t, Ioo_subset_Icc_self ht, rfl⟩
    · intro t _
      simpa only [Function.comp_apply, one_mul] using congrFun hγeq t
  have hseglen : (segCurve v).rhoLength ρ = metricDist unitDisc ρ z w := by
    calc
      (segCurve v).rhoLength ρ = ENNReal.ofReal
          (Real.log ((1 + ‖v‖) / (1 - ‖v‖))) :=
        rhoLength_segCurve_of_nonneg (norm_nonneg v) hv rfl
      _ = metricDist unitDisc ρ z w := by
        have hcross : ((w : ℂ) - z) / (1 - (starRingEnd ℂ) (z : ℂ) * w) = v := rfl
        have hdist := eq14_3 (z₁ := (z : ℂ)) (z₂ := (w : ℂ)) z.property w.property
        rw [hcross] at hdist
        exact hdist.symm
  obtain ⟨K, hLip⟩ := hγpath.1
  refine ⟨RectifiableCurve.ofLRCurve γ hLip,
    ⟨hγpath.2.1, hγpath.2.2.1, hγpath.2.2.2⟩, ?_, ?_⟩
  · calc
      (RectifiableCurve.ofLRCurve γ hLip).weightedLength ρ = γ.rhoLength ρ :=
        RectifiableCurve.weightedLength_ofLRCurve γ hLip measurable_disc_poincareDensity
      _ = metricDist unitDisc ρ z w := hlenγ.trans hseglen
      _ = ENNReal.ofReal (discPathDist z w) :=
        (rectifiableMetricDist_eq_metricDist _ measurable_disc_poincareDensity
          (z : ℂ) (w : ℂ)).symm.trans (discRectifiableEDist_eq_pathDist z w)
  · intro hzw
    change InjOn γ.toFun (Icc (0 : ℝ) 1)
    have hv0 : v ≠ 0 := by
      intro he
      rw [he] at hgv
      exact hzw (Complex.UnitDisc.coe_injective (hg0.symm.trans hgv))
    have hγpoint (u : ℝ) : γ.toFun u =
        blaschke (-(z : ℂ)) ((segCurve v).toFun u) := by
      simpa only [Function.comp_apply] using congrFun hγeq u
    intro a ha b hb hab
    have he : (segCurve v).toFun a = (segCurve v).toFun b :=
      (isConformalOnto_blaschke hz).2.1
        (hseg.2.2.2 ⟨a, ha, rfl⟩) (hseg.2.2.2 ⟨b, hb, rfl⟩)
        ((hγpoint a).symm.trans (hab.trans (hγpoint b)))
    rw [segCurve_apply, segCurve_apply] at he
    exact Complex.ofReal_injective (mul_right_cancel₀ hv0 he)

/-- Every pair of disk points admits a genuine continuous rectifiable curve
whose literal weighted arclength is the full Poincaré distance. -/
theorem exists_rectifiable_disk_minimizer (z w : 𝔻) :
    ∃ c : RectifiableCurve, c.IsPathIn unitDisc z w ∧
      c.weightedLength (fun ζ => ENNReal.ofReal (poincareDensityDisc ζ)) =
        ENNReal.ofReal (discPathDist z w) := by
  obtain ⟨c, hc, hlen, _hinj⟩ := exists_rectifiable_disk_minimizer_data z w
  exact ⟨c, hc, hlen⟩

/-- Distinct endpoints have a genuine injective minimizing arc, rather than
only a possibly stationary parametrization with the same geometric trace. -/
theorem exists_injective_rectifiable_disk_minimizer (z w : 𝔻) (hzw : z ≠ w) :
    ∃ c : RectifiableCurve, c.IsPathIn unitDisc z w ∧
      c.weightedLength (fun ζ => ENNReal.ofReal (poincareDensityDisc ζ)) =
        ENNReal.ofReal (discPathDist z w) ∧ InjOn c.curve (Icc c.a c.b) := by
  obtain ⟨c, hc, hlen, hinj⟩ := exists_rectifiable_disk_minimizer_data z w
  exact ⟨c, hc, hlen, hinj hzw⟩


end LowDimensionalTopology.Geometry.Hyperbolic
