module

public import LowDimensionalTopology.Geometry.Quasiconformal.RealHilbertPairedKernel
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The literal principal value in the real-line Riesz proof

The paired quotient is absolutely integrable.
Splitting the real line into its positive and negative tails identifies
the original symmetric truncations with its positive-tail integral.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

private def shiftedRealCauchyKernel (φ : ℝ → ℂ) (ξ x : ℝ) : ℂ :=
  φ (ξ + x) / (x : ℂ)

private theorem paired_eq_shifted_add_neg (φ : ℝ → ℂ) (ξ : ℝ) {x : ℝ} (hx : x ≠ 0) :
    realHilbertPairedKernel φ ξ x =
      shiftedRealCauchyKernel φ ξ x + shiftedRealCauchyKernel φ ξ (-x) := by
  rw [realHilbertPairedKernel_of_ne φ ξ hx]
  simp only [shiftedRealCauchyKernel, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_neg, ← sub_eq_add_neg, div_neg]
  ring

private theorem shifted_integrableOn_tail {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ) (ξ : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (shiftedRealCauchyKernel φ ξ) {x : ℝ | ε < |x|} := by
  have hi := (hφ.continuous.integrable_of_hasCompactSupport
    (μ := (volume : Measure ℝ)) hcompact).comp_add_left ξ
  apply ((hi.norm.const_mul (1 / ε)).integrableOn).mono'
  · exact ((hφ.continuous.comp (continuous_const.add continuous_id)).measurable.div
      Complex.continuous_ofReal.measurable).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict
      (isOpen_lt continuous_const continuous_abs).measurableSet] with x hx
    change ‖φ (ξ + x) / (x : ℂ)‖ ≤ (1 / ε) * ‖φ (ξ + x)‖
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖φ (ξ + x)‖ / |x| ≤ ‖φ (ξ + x)‖ / ε :=
        div_le_div_of_nonneg_left (norm_nonneg _) hε hx.le
      _ = (1 / ε) * ‖φ (ξ + x)‖ := by ring

private theorem shifted_truncation_eq (φ : ℝ → ℂ) (ξ ε : ℝ) :
    (∫ x in {x : ℝ | ε < |x - ξ|}, φ x / ((x - ξ : ℝ) : ℂ)) =
      ∫ x in {x : ℝ | ε < |x|}, shiftedRealCauchyKernel φ ξ x := by
  let s : Set ℝ := {x | ε < |x - ξ|}
  have hs : MeasurableSet s := (isOpen_lt continuous_const
    ((continuous_id.sub continuous_const).abs)).measurableSet
  have ht : MeasurableSet {x : ℝ | ε < |x|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  rw [← integral_indicator hs]
  rw [← integral_add_left_eq_self
    (s.indicator (fun x => φ x / ((x - ξ : ℝ) : ℂ))) ξ]
  rw [← integral_indicator ht]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : ε < |x| <;>
      simp [s, hx, shiftedRealCauchyKernel, add_sub_cancel_left]

/-- The book's exact paired-tail identity for every positive truncation radius. -/
theorem realHilbertTruncation_eq_paired_tail {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ) (ξ : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    realHilbertTruncation φ ξ ε = (1 / (Real.pi : ℂ)) *
      ∫ x in Ioi ε, realHilbertPairedKernel φ ξ x := by
  have hset : {x : ℝ | ε < |x|} = Iio (-ε) ∪ Ioi ε := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi]
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      constructor <;> intro h
      · exact Or.inr h
      · rcases h with h | h
        · linarith
        · exact h
    · rw [abs_of_neg hx]
      constructor <;> intro h
      · exact Or.inl (by linarith)
      · rcases h with h | h <;> linarith
  have hi := shifted_integrableOn_tail hφ hcompact ξ hε
  rw [hset] at hi
  have hneg := hi.mono_set (subset_union_left : Iio (-ε) ⊆ Iio (-ε) ∪ Ioi ε)
  have hpos := hi.mono_set (subset_union_right : Ioi ε ⊆ Iio (-ε) ∪ Ioi ε)
  have hq := (integrable_realHilbertPairedKernel hφ hcompact ξ).integrableOn (s := Ioi ε)
  have hm : IntegrableOn (fun x => shiftedRealCauchyKernel φ ξ (-x)) (Ioi ε) := by
    apply (hq.sub hpos).congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have heq := paired_eq_shifted_add_neg φ ξ (ne_of_gt (lt_trans hε hx))
    simp only [Pi.sub_apply]
    rw [heq]
    exact add_sub_cancel_left _ _
  have hreflection :
      (∫ x in Iio (-ε), shiftedRealCauchyKernel φ ξ x) =
        ∫ x in Ioi ε, shiftedRealCauchyKernel φ ξ (-x) := by
    rw [← integral_Iic_eq_integral_Iio]
    exact (integral_comp_neg_Ioi ε (shiftedRealCauchyKernel φ ξ)).symm
  rw [realHilbertTruncation, shifted_truncation_eq, hset,
    setIntegral_union (by
      rw [Set.disjoint_left]
      intro x hx hy
      have : x < -ε := hx
      have : ε < x := hy
      linarith) measurableSet_Ioi hneg hpos,
    hreflection, ← integral_add hm hpos]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  rw [paired_eq_shifted_add_neg φ ξ (ne_of_gt (lt_trans hε hx))]
  exact add_comm _ _

/-- All original complex compact C1 tests have the genuine symmetric principal
value, with its exact positive-half-line paired representation. -/
theorem realHilbert_principalValue_and_eq_paired {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ) (ξ : ℝ) :
    HasRealHilbertPrincipalValue φ ξ ∧
      realHilbertTransform φ ξ = (1 / (Real.pi : ℂ)) *
        ∫ x in Ioi (0 : ℝ), realHilbertPairedKernel φ ξ x := by
  have hi := integrable_realHilbertPairedKernel hφ hcompact ξ
  have hc := continuous_realHilbertPairedKernel hφ ξ
  have hsmall : Tendsto (fun ε : ℝ => ∫ x in (0 : ℝ)..ε,
      realHilbertPairedKernel φ ξ x) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((hc.integral_hasStrictDerivAt 0 0).hasDerivAt.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)
  have htail : Tendsto (fun ε : ℝ => ∫ x in Ioi ε, realHilbertPairedKernel φ ξ x)
      (𝓝[>] 0) (𝓝 (∫ x in Ioi (0 : ℝ), realHilbertPairedKernel φ ξ x)) := by
    have h : Tendsto (fun ε : ℝ =>
        (∫ x in Ioi (0 : ℝ), realHilbertPairedKernel φ ξ x) -
          ∫ x in (0 : ℝ)..ε, realHilbertPairedKernel φ ξ x)
        (𝓝[>] 0) (𝓝 ((∫ x in Ioi (0 : ℝ), realHilbertPairedKernel φ ξ x) - 0)) :=
      tendsto_const_nhds.sub hsmall
    simp only [sub_zero] at h
    apply h.congr'
    exact Eventually.of_forall fun ε => (eq_sub_iff_add_eq.2 (by
      simpa only [add_comm] using
        intervalIntegral.integral_interval_add_Ioi hi.integrableOn hi.integrableOn)).symm
  have htrunc : Tendsto (realHilbertTruncation φ ξ) (𝓝[>] (0 : ℝ))
      (𝓝 ((1 / (Real.pi : ℂ)) *
        ∫ x in Ioi (0 : ℝ), realHilbertPairedKernel φ ξ x)) := by
    apply (tendsto_const_nhds.mul htail).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (realHilbertTruncation_eq_paired_tail hφ hcompact ξ hε).symm
  have heq : realHilbertTransform φ ξ = (1 / (Real.pi : ℂ)) *
      ∫ x in Ioi (0 : ℝ), realHilbertPairedKernel φ ξ x := htrunc.limUnder_eq
  exact ⟨by simpa only [HasRealHilbertPrincipalValue, heq] using htrunc, heq⟩

end LowDimensionalTopology.Geometry.Quasiconformal
