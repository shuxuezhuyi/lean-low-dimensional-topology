module

public import LowDimensionalTopology.Geometry.Quasiconformal.MeasurableRiemannMapping
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Measurable planar Beltrami classes and their normalized solutions

The coefficient space is Mathlib's complex Banach space `Lp ℂ ∞ volume`.
Its elements are almost-everywhere classes. Strictly subunit classes form its
actual open unit ball. The normalized measurable Riemann mapping is defined
on that ball, and the representative-independence statements below use the
almost-everywhere congruence theorem for the actual Beltrami equation.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller

/-- The complex Banach space of essentially bounded planar coefficients. -/
abbrev MeasurableBeltramiSpace := Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure ℂ)

/-- The actual open unit ball in the complex L-infinity Banach space. -/
abbrev MeasurableBeltramiBall :=
  ↥(Metric.ball (0 : MeasurableBeltramiSpace) 1)

section Norm

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {m : Measure α}

/-- An L-infinity representative is bounded by its class norm almost everywhere. -/
theorem lpInfinity_norm_ae_le (f : Lp E (⊤ : ℝ≥0∞) m) :
    ∀ᵐ x ∂m, ‖f x‖ ≤ ‖f‖ := by
  have h := enorm_ae_le_eLpNormEssSup f m
  rw [← eLpNorm_exponent_top (Lp.aestronglyMeasurable f), ← Lp.enorm_def] at h
  simpa only [enorm_le_iff_norm_le] using h

/-- A uniform almost-everywhere bound controls the L-infinity norm even when
its domain has infinite measure. -/
theorem lpInfinity_norm_le_of_ae_bound (f : Lp E (⊤ : ℝ≥0∞) m)
    {k : ℝ} (hk : 0 ≤ k) (hfk : ∀ᵐ x ∂m, ‖f x‖ ≤ k) : ‖f‖ ≤ k := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
  calc
    _ ≤ (ENNReal.ofReal k).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound hfk)
    _ = k := ENNReal.toReal_ofReal hk

/-- Strictly subunit L-infinity norm is equivalent to a fixed a.e. bound below one. -/
theorem lpInfinity_norm_lt_one_iff (f : Lp E (⊤ : ℝ≥0∞) m) :
    ‖f‖ < 1 ↔ ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ ∀ᵐ x ∂m, ‖f x‖ ≤ k := by
  constructor
  · intro hf
    exact ⟨‖f‖, norm_nonneg f, hf, lpInfinity_norm_ae_le f⟩
  · rintro ⟨k, hk₀, hk, hfk⟩
    exact (lpInfinity_norm_le_of_ae_bound f hk₀ hfk).trans_lt hk

end Norm

namespace MeasurableBeltramiSpace

/-- The chosen measurable representative satisfies the genuine source
coefficient definition with the exact essential norm bound. -/
theorem isBeltramiCoeff (μ : MeasurableBeltramiSpace) :
    LiZhongQC.IsBeltramiCoeff μ univ ‖μ‖ := by
  simpa only [LiZhongQC.IsBeltramiCoeff, Measure.restrict_univ] using
    And.intro (Lp.aestronglyMeasurable μ) (lpInfinity_norm_ae_le μ)

/-- Membership in the Banach open unit ball is precisely the usual measurable
Beltrami condition with an explicit nonnegative constant below one. -/
theorem norm_lt_one_iff (μ : MeasurableBeltramiSpace) :
    ‖μ‖ < 1 ↔ ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ LiZhongQC.IsBeltramiCoeff μ univ k := by
  constructor
  · intro hμ
    exact ⟨‖μ‖, norm_nonneg μ, hμ, isBeltramiCoeff μ⟩
  · rintro ⟨k, hk₀, hk, hμ⟩
    have hbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k := by
      simpa only [Measure.restrict_univ] using hμ.2
    exact (lpInfinity_norm_le_of_ae_bound μ hk₀ hbound).trans_lt hk

end MeasurableBeltramiSpace

/-- The coefficient predicate respects almost-everywhere equality on the plane. -/
theorem planar_isBeltramiCoeff_congr_ae {μ ν : ℂ → ℂ} {k : ℝ}
    (hμν : μ =ᵐ[volume] ν) :
    LiZhongQC.IsBeltramiCoeff μ univ k ↔ LiZhongQC.IsBeltramiCoeff ν univ k := by
  simp only [LiZhongQC.IsBeltramiCoeff, Measure.restrict_univ]
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

namespace MeasurableBeltramiBall

/-- The ball's inherited metric condition gives its strictly subunit class norm. -/
theorem norm_lt_one (μ : MeasurableBeltramiBall) : ‖μ.val‖ < 1 := by
  simpa only [Metric.mem_ball, dist_zero_right] using μ.property

/-- Every source Beltrami coefficient on the plane represents an L-infinity class. -/
theorem coefficientMemLp {μ : ℂ → ℂ} {k : ℝ}
    (hμ : LiZhongQC.IsBeltramiCoeff μ univ k) :
    MemLp μ (⊤ : ℝ≥0∞) (volume : Measure ℂ) := by
  have hmeas : AEStronglyMeasurable μ (volume : Measure ℂ) := by
    simpa only [Measure.restrict_univ] using hμ.1
  have hbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k := by
    simpa only [Measure.restrict_univ] using hμ.2
  exact memLp_top_of_bound hmeas k hbound

/-- Encode a genuine coefficient into its a.e. class in the actual open unit ball. -/
def ofCoefficient {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : LiZhongQC.IsBeltramiCoeff μ univ k) : MeasurableBeltramiBall :=
  ⟨(coefficientMemLp hμ).toLp μ, by
    rw [Metric.mem_ball, dist_zero_right]
    apply (MeasurableBeltramiSpace.norm_lt_one_iff _).2
    refine ⟨k, hk₀, hk, ?_⟩
    exact (planar_isBeltramiCoeff_congr_ae (coefficientMemLp hμ).coeFn_toLp).2 hμ⟩

/-- Encoding retains the original coefficient almost everywhere. -/
theorem ofCoefficient_coe_ae {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : LiZhongQC.IsBeltramiCoeff μ univ k) :
    ((ofCoefficient hk₀ hk hμ).val : ℂ → ℂ) =ᵐ[volume] μ :=
  (coefficientMemLp hμ).coeFn_toLp

/-- Encoding is independent of the representative and of its supplied bound. -/
theorem ofCoefficient_congr_ae {μ ν : ℂ → ℂ} {k l : ℝ}
    (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : LiZhongQC.IsBeltramiCoeff μ univ k)
    (hl₀ : 0 ≤ l) (hl : l < 1) (hν : LiZhongQC.IsBeltramiCoeff ν univ l)
    (hμν : μ =ᵐ[volume] ν) :
    ofCoefficient hk₀ hk hμ = ofCoefficient hl₀ hl hν := by
  apply Subtype.ext
  apply Lp.ext
  exact (ofCoefficient_coe_ae hk₀ hk hμ).trans
    (hμν.trans (ofCoefficient_coe_ae hl₀ hl hν).symm)

/-- Existence and uniqueness use the class's own essential norm as the sharp bound. -/
theorem normalized_existsUnique (μ : MeasurableBeltramiBall) :
    ∃! f : ℂ ≃ₜ ℂ,
      LiZhongQC.IsNormalizedSolution f μ.val ∧
      LiZhongQC.IsKQC f univ ((1 + ‖μ.val‖) / (1 - ‖μ.val‖)) ∧
      LiZhongQC.IsACL f univ ∧ LiZhongQC.IsGenHomeoSolution f μ.val univ 2 := by
  exact Quasiconformal.normalized_beltrami_homeomorph_existsUnique
    (norm_nonneg μ.val) (norm_lt_one μ) (MeasurableBeltramiSpace.isBeltramiCoeff μ.val)

/-- The unique normalized plane homeomorphism associated with a Beltrami a.e. class. -/
def normalizedSolution (μ : MeasurableBeltramiBall) : ℂ ≃ₜ ℂ :=
  Classical.choose (normalized_existsUnique μ)

/-- The selected map has the genuine Beltrami equation, sharp distortion bound,
ACL regularity and generalized L2 homeomorphic solution property. -/
theorem normalizedSolution_spec (μ : MeasurableBeltramiBall) :
    LiZhongQC.IsNormalizedSolution (normalizedSolution μ) μ.val ∧
    LiZhongQC.IsKQC (normalizedSolution μ) univ ((1 + ‖μ.val‖) / (1 - ‖μ.val‖)) ∧
    LiZhongQC.IsACL (normalizedSolution μ) univ ∧
      LiZhongQC.IsGenHomeoSolution (normalizedSolution μ) μ.val univ 2 :=
  (Classical.choose_spec (normalized_existsUnique μ)).1

/-- Changing to any representative of the coefficient class preserves the actual
normalized solution predicate. -/
theorem normalizedSolution_isNormalized_of_ae (μ : MeasurableBeltramiBall)
    {ν : ℂ → ℂ} (hμν : (μ.val : ℂ → ℂ) =ᵐ[volume] ν) :
    LiZhongQC.IsNormalizedSolution (normalizedSolution μ) ν :=
  (Quasiconformal.isNormalizedSolution_congr_ae hμν).1 (normalizedSolution_spec μ).1

/-- The selected homeomorphism is uniquely determined even when a different
representative is used, without prescribing a bound in the uniqueness hypothesis. -/
theorem normalizedSolution_eq_of_ae (μ : MeasurableBeltramiBall)
    {ν : ℂ → ℂ} (hμν : (μ.val : ℂ → ℂ) =ᵐ[volume] ν)
    (f : ℂ ≃ₜ ℂ) (hf : LiZhongQC.IsNormalizedSolution f ν) :
    normalizedSolution μ = f := by
  exact Quasiconformal.normalized_beltrami_homeomorph_unique
    (normalizedSolution_isNormalized_of_ae μ hμν) hf

/-- Distinct coefficient classes give distinct genuine normalized homeomorphisms. -/
theorem normalizedSolution_injective : Function.Injective normalizedSolution := by
  intro μ ν h
  apply Subtype.ext
  apply Lp.ext
  have hμ := (normalizedSolution_spec μ).1.2.2.2.2
  have hν := (normalizedSolution_spec ν).1.2.2.2.2
  rw [h] at hμ
  exact Filter.EventuallyEq.trans (Filter.EventuallyEq.symm hμ) hν

/-- The actual sphere extensions retain three-point normalization. -/
theorem normalizedSolution_sphere_normalization (μ : MeasurableBeltramiBall) :
    (normalizedSolution μ).onePointCongr (OnePoint.infty : OnePoint ℂ) = OnePoint.infty ∧
      (normalizedSolution μ).onePointCongr ((0 : ℂ) : OnePoint ℂ) =
        ((0 : ℂ) : OnePoint ℂ) ∧
      (normalizedSolution μ).onePointCongr ((1 : ℂ) : OnePoint ℂ) =
        ((1 : ℂ) : OnePoint ℂ) := by
  exact Quasiconformal.normalized_solution_sphere_normalization
    (normalizedSolution μ) (normalizedSolution_spec μ).1

end MeasurableBeltramiBall

end LowDimensionalTopology.Geometry.Teichmuller
