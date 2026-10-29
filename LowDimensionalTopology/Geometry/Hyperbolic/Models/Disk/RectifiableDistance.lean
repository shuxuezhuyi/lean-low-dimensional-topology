module

public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.RectifiableDistance
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.SchwarzPickDistance
public import Mathlib.Tactic.FunProp

/-!
# Poincaré distance over all continuous rectifiable disk curves

The distance is the literal infimum of the density-weighted arclength integral
of every continuous bounded-variation curve joining the given points. The proved
comparison with the existing model distance gives Schwarz--Pick for this full
rectifiable definition.
-/

public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal ComplexConjugate Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The literal disk Poincaré density is a Borel nonnegative weight. -/
theorem measurable_disc_poincareDensity :
    Measurable (fun z : ℂ => ENNReal.ofReal (LiZhongQC.poincareDensityDisc z)) := by
  unfold LiZhongQC.poincareDensityDisc
  fun_prop

/-- Poincaré extended distance defined using every continuous rectifiable curve
and the literal density `2 / (1 - |z|²)`. -/
@[expose] def discRectifiableEDist (z w : 𝔻) : ℝ≥0∞ :=
  rectifiableMetricDist LiZhongQC.unitDisc
    (fun ζ => ENNReal.ofReal (LiZhongQC.poincareDensityDisc ζ)) z w

/-- The real-valued distance attached to the full rectifiable infimum. -/
@[expose] def discRectifiableDist (z w : 𝔻) : ℝ := (discRectifiableEDist z w).toReal

/-- The full rectifiable infimum equals the actual model distance. -/
theorem discRectifiableEDist_eq_pathDist (z w : 𝔻) :
    discRectifiableEDist z w = ENNReal.ofReal (discPathDist z w) := by
  have hden : ‖1 - conj (z : ℂ) * (w : ℂ)‖ = ‖1 - (z : ℂ) * conj (w : ℂ)‖ := by
    calc
      ‖1 - conj (z : ℂ) * (w : ℂ)‖ = ‖conj (1 - conj (z : ℂ) * (w : ℂ))‖ :=
        (Complex.norm_conj _).symm
      _ = ‖1 - (z : ℂ) * conj (w : ℂ)‖ := by
        simp only [map_sub, map_one, map_mul, Complex.conj_conj]
  have hcross : ‖((w : ℂ) - z) / (1 - conj (z : ℂ) * w)‖ =
      Real.tanh (discPathDist z w / 2) := by
    rw [disc_tanh_half_distance, norm_div, hden, norm_sub_rev (w : ℂ) (z : ℂ)]
  have ht : Real.tanh (discPathDist z w / 2) ∈ Icc (-1 : ℝ) 1 :=
    ⟨(Real.neg_one_lt_tanh _).le, (Real.tanh_lt_one _).le⟩
  have hlog : Real.log ((1 + Real.tanh (discPathDist z w / 2)) /
      (1 - Real.tanh (discPathDist z w / 2))) = discPathDist z w := by
    have h := Real.artanh_tanh (discPathDist z w / 2)
    rw [Real.artanh_eq_half_log ht] at h
    linarith
  rw [discRectifiableEDist,
    rectifiableMetricDist_eq_metricDist _ measurable_disc_poincareDensity]
  have hsource := LiZhongQC.eq14_3 (z₁ := (z : ℂ)) (z₂ := (w : ℂ)) z.property w.property
  simpa only [hcross, hlog] using hsource

theorem discRectifiableEDist_ne_top (z w : 𝔻) : discRectifiableEDist z w ≠ ∞ := by
  rw [discRectifiableEDist_eq_pathDist]
  exact ENNReal.ofReal_ne_top

theorem discRectifiableDist_eq_pathDist (z w : 𝔻) :
    discRectifiableDist z w = discPathDist z w := by
  have hd : 0 ≤ discPathDist z w := by
    rw [discPathDist_eq_halfPlane]
    exact dist_nonneg
  rw [discRectifiableDist, discRectifiableEDist_eq_pathDist, ENNReal.toReal_ofReal hd]

/-- Every holomorphic disk self-map contracts the literal full-rectifiable
Poincaré distance. -/
theorem disc_schwarz_pick_rectifiable_distance {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f LiZhongQC.unitDisc)
    (hm : MapsTo f LiZhongQC.unitDisc LiZhongQC.unitDisc) (z w : 𝔻) :
    discRectifiableDist (discSelfMap f hm z) (discSelfMap f hm w) ≤
      discRectifiableDist z w := by
  simpa only [discRectifiableDist_eq_pathDist] using disc_schwarz_pick_distance hf hm z w

/-- The same contraction retains the literal extended-distance infimum. -/
theorem disc_schwarz_pick_rectifiable_edistance {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f LiZhongQC.unitDisc)
    (hm : MapsTo f LiZhongQC.unitDisc LiZhongQC.unitDisc) (z w : 𝔻) :
    discRectifiableEDist (discSelfMap f hm z) (discSelfMap f hm w) ≤
      discRectifiableEDist z w := by
  rw [discRectifiableEDist_eq_pathDist, discRectifiableEDist_eq_pathDist]
  exact ENNReal.ofReal_le_ofReal (disc_schwarz_pick_distance hf hm z w)

end LowDimensionalTopology.Geometry.Hyperbolic
