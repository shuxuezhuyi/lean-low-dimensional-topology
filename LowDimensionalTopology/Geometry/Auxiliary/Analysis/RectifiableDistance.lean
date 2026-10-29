module

public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.RectifiableNormalizedLength

/-!
# Weighted distance using every continuous rectifiable curve

For Borel densities, the literal infimum over all continuous BV curves agrees
with the existing Lipschitz-curve infimum. Each comparison uses the actual
curve's weighted length, and the normalized representative preserves traversal.
-/

public section
noncomputable section

open Set
open scoped ENNReal

namespace LowDimensionalTopology.Geometry

/-- A traversed rectifiable curve in a domain with specified endpoints. -/
@[expose] def RectifiableCurve.IsPathIn (c : RectifiableCurve) (D : Set ℂ)
    (z w : ℂ) : Prop :=
  c.curve c.a = z ∧ c.curve c.b = w ∧ c.curve '' Icc c.a c.b ⊆ D

/-- The distance infimum over every continuous rectifiable curve, with the
ordinary arclength line integral as length. -/
@[expose] def rectifiableMetricDist (D : Set ℂ) (ρ : ℂ → ℝ≥0∞) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ c ∈ {c : RectifiableCurve | c.IsPathIn D z w}, c.weightedLength ρ

/-- Normalized Lipschitz curves suffice for the full rectifiable distance
infimum, for every Borel nonnegative density. -/
theorem rectifiableMetricDist_eq_metricDist (D : Set ℂ) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) (z w : ℂ) :
    rectifiableMetricDist D ρ z w = LiZhongQC.metricDist D ρ z w := by
  change (⨅ c ∈ {c : RectifiableCurve | c.IsPathIn D z w}, c.weightedLength ρ) =
    ⨅ γ ∈ {γ : LiZhongQC.LRCurve | LiZhongQC.IsPathIn D z w γ}, γ.rhoLength ρ
  apply le_antisymm
  · refine le_iInf fun γ => le_iInf fun hγ => ?_
    obtain ⟨⟨K, hLip⟩, h0, h1, htrace⟩ := hγ
    let c := RectifiableCurve.ofLRCurve γ hLip
    have hc : c.IsPathIn D z w := ⟨h0, h1, htrace⟩
    calc
      (⨅ c ∈ {c : RectifiableCurve | c.IsPathIn D z w}, c.weightedLength ρ) ≤
          c.weightedLength ρ := iInf_le_of_le c (iInf_le _ hc)
      _ = γ.rhoLength ρ := RectifiableCurve.weightedLength_ofLRCurve γ hLip hρ
  · refine le_iInf fun c => le_iInf fun hc => ?_
    have hpath : LiZhongQC.IsPathIn D z w c.normalizedCurve := by
      simpa only [hc.1, hc.2.1] using c.normalizedCurve_isPathIn hc.2.2
    calc
      (⨅ γ ∈ {γ : LiZhongQC.LRCurve | LiZhongQC.IsPathIn D z w γ}, γ.rhoLength ρ) ≤
          c.normalizedCurve.rhoLength ρ := iInf_le_of_le c.normalizedCurve (iInf_le _ hpath)
      _ = c.weightedLength ρ := c.normalizedCurve_rhoLength hρ

end LowDimensionalTopology.Geometry
