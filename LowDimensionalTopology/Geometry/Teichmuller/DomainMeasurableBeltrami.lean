module

public import LowDimensionalTopology.Geometry.Teichmuller.MeasurableBeltrami

/-!
# Measurable Beltrami classes on a planar set

The ambient complex Banach space uses the actual restricted measure. Its open
unit ball consists of almost-everywhere classes on that set. No measurability,
openness or finite-volume assumption on the set is required for these facts.
For a planar domain this is the usual measurable Beltrami coefficient space.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller

/-- The complex L-infinity Banach space on the actual restricted measure. -/
abbrev DomainMeasurableBeltramiSpace (D : Set ℂ) :=
  Lp ℂ (⊤ : ℝ≥0∞) (volume.restrict D)

/-- The actual open unit ball in the restricted-measure Banach space. -/
abbrev DomainMeasurableBeltramiBall (D : Set ℂ) :=
  ↥(Metric.ball (0 : DomainMeasurableBeltramiSpace D) 1)

namespace DomainMeasurableBeltramiSpace

variable {D : Set ℂ}

/-- Completeness is inherited from Mathlib Lp for the arbitrary measure
`volume.restrict D`; no finite-volume hypothesis is needed at exponent infinity. -/
theorem completeSpace (D : Set ℂ) : CompleteSpace (DomainMeasurableBeltramiSpace D) :=
  inferInstance

/-- The chosen representative satisfies the actual coefficient predicate on D
with its own class norm as an almost-everywhere bound. -/
theorem isBeltramiCoeff (μ : DomainMeasurableBeltramiSpace D) :
    LiZhongQC.IsBeltramiCoeff μ D ‖μ‖ :=
  ⟨Lp.aestronglyMeasurable μ, lpInfinity_norm_ae_le μ⟩

/-- The Banach open-ball condition is exactly an essentially bounded measurable
coefficient with one nonnegative bound strictly below one. -/
theorem norm_lt_one_iff (μ : DomainMeasurableBeltramiSpace D) :
    ‖μ‖ < 1 ↔ ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ LiZhongQC.IsBeltramiCoeff μ D k := by
  constructor
  · intro hμ
    exact ⟨‖μ‖, norm_nonneg μ, hμ, isBeltramiCoeff μ⟩
  · rintro ⟨k, hk₀, hk, hμ⟩
    exact (lpInfinity_norm_le_of_ae_bound μ hk₀ hμ.2).trans_lt hk

end DomainMeasurableBeltramiSpace

/-- The coefficient predicate depends only on restricted-measure a.e. values. -/
theorem domain_isBeltramiCoeff_congr_ae {D : Set ℂ} {μ ν : ℂ → ℂ} {k : ℝ}
    (hμν : μ =ᵐ[volume.restrict D] ν) :
    LiZhongQC.IsBeltramiCoeff μ D k ↔ LiZhongQC.IsBeltramiCoeff ν D k := by
  simp only [LiZhongQC.IsBeltramiCoeff]
  constructor
  · rintro ⟨hμ, hbound⟩
    refine ⟨hμ.congr hμν, ?_⟩
    filter_upwards [hμν, hbound] with z hz hb
    rw [← hz]
    exact hb
  · rintro ⟨hν, hbound⟩
    refine ⟨hν.congr hμν.symm, ?_⟩
    filter_upwards [hμν, hbound] with z hz hb
    rw [hz]
    exact hb

namespace DomainMeasurableBeltramiBall

variable {D : Set ℂ}

/-- The ball's inherited metric condition is the strict class-norm bound. -/
theorem norm_lt_one (μ : DomainMeasurableBeltramiBall D) : ‖μ.val‖ < 1 := by
  simpa only [Metric.mem_ball, dist_zero_right] using μ.property

/-- A raw coefficient on D belongs to L-infinity for the restricted measure,
even when D has infinite volume or is not assumed measurable. -/
theorem coefficientMemLp {μ : ℂ → ℂ} {k : ℝ}
    (hμ : LiZhongQC.IsBeltramiCoeff μ D k) :
    MemLp μ (⊤ : ℝ≥0∞) (volume.restrict D) :=
  memLp_top_of_bound hμ.1 k hμ.2

/-- Encode a raw coefficient into its genuine restricted-measure a.e. class. -/
def ofCoefficient {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : LiZhongQC.IsBeltramiCoeff μ D k) : DomainMeasurableBeltramiBall D :=
  ⟨(coefficientMemLp hμ).toLp μ, by
    rw [Metric.mem_ball, dist_zero_right]
    apply (DomainMeasurableBeltramiSpace.norm_lt_one_iff _).2
    refine ⟨k, hk₀, hk, ?_⟩
    exact (domain_isBeltramiCoeff_congr_ae (D := D)
      (coefficientMemLp hμ).coeFn_toLp).2 hμ⟩

/-- Encoding retains the original coefficient almost everywhere on D. -/
theorem ofCoefficient_coe_ae {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : LiZhongQC.IsBeltramiCoeff μ D k) :
    ((ofCoefficient hk₀ hk hμ).val : ℂ → ℂ) =ᵐ[volume.restrict D] μ :=
  (coefficientMemLp hμ).coeFn_toLp

/-- The encoding is independent of the representative and the supplied bound. -/
theorem ofCoefficient_congr_ae {μ ν : ℂ → ℂ} {k l : ℝ}
    (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : LiZhongQC.IsBeltramiCoeff μ D k)
    (hl₀ : 0 ≤ l) (hl : l < 1) (hν : LiZhongQC.IsBeltramiCoeff ν D l)
    (hμν : μ =ᵐ[volume.restrict D] ν) :
    ofCoefficient hk₀ hk hμ = ofCoefficient hl₀ hl hν := by
  apply Subtype.ext
  apply Lp.ext
  exact (ofCoefficient_coe_ae hk₀ hk hμ).trans
    (hμν.trans (ofCoefficient_coe_ae hl₀ hl hν).symm)

/-- Equality of encoded classes is exactly restricted-measure a.e. equality. -/
theorem ofCoefficient_eq_iff {μ ν : ℂ → ℂ} {k l : ℝ}
    (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : LiZhongQC.IsBeltramiCoeff μ D k)
    (hl₀ : 0 ≤ l) (hl : l < 1) (hν : LiZhongQC.IsBeltramiCoeff ν D l) :
    ofCoefficient hk₀ hk hμ = ofCoefficient hl₀ hl hν ↔
      μ =ᵐ[volume.restrict D] ν := by
  constructor
  · intro h
    exact (MemLp.toLp_eq_toLp_iff (coefficientMemLp hμ)
      (coefficientMemLp hν)).1 (congrArg Subtype.val h)
  · exact ofCoefficient_congr_ae hk₀ hk hμ hl₀ hl hν

/-- Every ball element is recovered by encoding its own chosen representative
with its intrinsic norm bound. -/
theorem ofCoefficient_representative (μ : DomainMeasurableBeltramiBall D) :
    ofCoefficient (norm_nonneg μ.val) (norm_lt_one μ)
      (DomainMeasurableBeltramiSpace.isBeltramiCoeff μ.val) = μ := by
  apply Subtype.ext
  exact Lp.toLp_coeFn μ.val
    (coefficientMemLp (DomainMeasurableBeltramiSpace.isBeltramiCoeff μ.val))

end DomainMeasurableBeltramiBall

end LowDimensionalTopology.Geometry.Teichmuller
