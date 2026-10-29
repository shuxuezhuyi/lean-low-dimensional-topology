module

public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.ArcLength
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S26_TeichmullerUniqueness
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Weighted length of continuous rectifiable curves

The conformal density is integrated against Euclidean arclength along every
rectifiable curve. We implement this line integral in the actual
cumulative-variation parameter. We prove
independence of the chosen arclength factor and agreement with the integral of
weighted speed whenever the original parametrization is Lipschitz. The original
curve need not be injective or absolutely continuous in the general definition.
-/

public section
noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace LowDimensionalTopology.Geometry

/-- A continuous rectifiable plane curve, with its complete traversed parameter
interval. Bounded variation is Euclidean rectifiability. -/
structure RectifiableCurve where
  a : ℝ
  b : ℝ
  curve : ℝ → ℂ
  ordered : a ≤ b
  continuous : ContinuousOn curve (Icc a b)
  boundedVariation : BoundedVariationOn curve (Icc a b)

namespace RectifiableCurve

/-- The actual cumulative Euclidean arclength. -/
@[expose] def clock (c : RectifiableCurve) : ℝ → ℝ :=
  variationOnFromTo c.curve (Icc c.a c.b) c.a

/-- Euclidean length, retaining repeated traversal. -/
@[expose] def euclideanLength (c : RectifiableCurve) : ℝ := c.clock c.b

/-- The actual variation clock admits a global factor with exact subinterval arclength. -/
theorem exists_arclength_factor (c : RectifiableCurve) :
    ∃ γ : ℝ → ℂ, LipschitzWith 1 γ ∧ EqOn c.curve (γ ∘ c.clock) (Icc c.a c.b) ∧
      ∀ u v : ℝ, u ∈ Icc 0 c.euclideanLength → v ∈ Icc 0 c.euclideanLength → u ≤ v →
        eVariationOn γ (Icc u v) = ENNReal.ofReal (v - u) := by
  obtain ⟨_, _, _, _, _, γ, hγ, hfactor, _, _, _, _, hvar⟩ :=
    exists_arclength_factorization c.ordered c.continuous c.boundedVariation
  exact ⟨γ, hγ, hfactor, hvar⟩

/-- An actual arclength factor, whose existence was proved for every such curve. -/
@[expose] def arclengthFactor (c : RectifiableCurve) : ℝ → ℂ :=
  Classical.choose (exists_arclength_factor c)

theorem arclengthFactor_spec (c : RectifiableCurve) :
    LipschitzWith 1 c.arclengthFactor ∧
      EqOn c.curve (c.arclengthFactor ∘ c.clock) (Icc c.a c.b) ∧
      ∀ u v : ℝ, u ∈ Icc 0 c.euclideanLength → v ∈ Icc 0 c.euclideanLength → u ≤ v →
        eVariationOn c.arclengthFactor (Icc u v) = ENNReal.ofReal (v - u) :=
  by simpa only [arclengthFactor] using Classical.choose_spec (exists_arclength_factor c)

theorem clock_spec (c : RectifiableCurve) :
    0 ≤ c.euclideanLength ∧ ContinuousOn c.clock (Icc c.a c.b) ∧
      MonotoneOn c.clock (Icc c.a c.b) ∧ c.clock c.a = 0 ∧
      c.clock '' Icc c.a c.b = Icc 0 c.euclideanLength := by
  obtain ⟨hL, hc, hm, h0, hi, _⟩ :=
    exists_arclength_factorization c.ordered c.continuous c.boundedVariation
  exact ⟨hL, hc, hm, h0, hi⟩

/-- Factorization through the actual variation clock determines the factor on
its entire length interval. Equality of images alone would not imply this. -/
theorem factors_eqOn (c : RectifiableCurve) {γ δ : ℝ → ℂ}
    (hγ : EqOn c.curve (γ ∘ c.clock) (Icc c.a c.b))
    (hδ : EqOn c.curve (δ ∘ c.clock) (Icc c.a c.b)) :
    EqOn γ δ (Icc 0 c.euclideanLength) := by
  intro r hr
  obtain ⟨_, _, _, _, hi⟩ := c.clock_spec
  rw [← hi] at hr
  obtain ⟨t, ht, rfl⟩ := hr
  exact (hγ ht).symm.trans (hδ ht)

/-- The usual nonnegative weighted line integral against Euclidean arclength.
The factor is taken in the actual variation clock, so pauses and repeated arcs
are retained. Arbitrary original-parameter derivatives do not define this length. -/
@[expose] def weightedLength (c : RectifiableCurve) (ρ : ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ t in Ioo 0 c.euclideanLength, ρ (c.arclengthFactor t)

/-- The line integral is independent of which factor realizes the actual clock. -/
theorem weightedLength_eq_of_factor (c : RectifiableCurve) (ρ : ℂ → ℝ≥0∞)
    {γ : ℝ → ℂ} (hγ : EqOn c.curve (γ ∘ c.clock) (Icc c.a c.b)) :
    c.weightedLength ρ = ∫⁻ t in Ioo 0 c.euclideanLength, ρ (γ t) := by
  apply lintegral_congr_ae
  apply ae_restrict_of_forall_mem measurableSet_Ioo
  intro t ht
  change ρ (c.arclengthFactor t) = ρ (γ t)
  rw [c.factors_eqOn c.arclengthFactor_spec.2.1 hγ ⟨ht.1.le, ht.2.le⟩]

/-- An arclength factor has speed one almost everywhere on its length interval,
including the vacuous zero-length case. -/
theorem arclengthFactor_unit_speed (c : RectifiableCurve) :
    ∀ᵐ t ∂volume.restrict (Ioo 0 c.euclideanLength),
      ‖deriv c.arclengthFactor t‖ₑ = 1 := by
  have hL := c.clock_spec.1
  have hγ := c.arclengthFactor_spec.1
  have hAC : AbsolutelyContinuousOnInterval c.arclengthFactor 0 c.euclideanLength :=
    hγ.lipschitzOnWith.absolutelyContinuousOnInterval
  have htotal := c.arclengthFactor_spec.2.2 0 c.euclideanLength
    ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩ hL
  have hi : (∫⁻ t in Ioo 0 c.euclideanLength, ‖deriv c.arclengthFactor t‖ₑ) =
      ∫⁻ _t in Ioo (0 : ℝ) c.euclideanLength, (1 : ℝ≥0∞) := by
    rw [← LiZhongQC.s26v_b_eVariation_eq hL hAC, htotal,
      setLIntegral_one, Real.volume_Ioo]
  have hle : (fun t => ‖deriv c.arclengthFactor t‖ₑ) ≤ᵐ[
      volume.restrict (Ioo 0 c.euclideanLength)] (fun _ => (1 : ℝ≥0∞)) := by
    apply Filter.Eventually.of_forall
    intro t
    change ‖deriv c.arclengthFactor t‖ₑ ≤ (1 : ℝ≥0∞)
    rw [← ofReal_norm, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (norm_deriv_le_of_lipschitz hγ)
  have hfin : (∫⁻ t in Ioo 0 c.euclideanLength, ‖deriv c.arclengthFactor t‖ₑ) ≠ ∞ := by
    rw [hi, setLIntegral_one, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  exact ae_eq_of_ae_le_of_lintegral_le hle hfin aemeasurable_const hi.ge

/-- On every Lipschitz parametrization the arclength line integral is the usual
integral of density times speed. The equality uses the original clock and actual
factorization, so it also holds for repeated traversal and flat intervals. -/
theorem weightedLength_eq_lintegral_deriv (c : RectifiableCurve) {K : ℝ≥0}
    (hLip : LipschitzOnWith K c.curve (Icc c.a c.b))
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    c.weightedLength ρ = ∫⁻ t in Ioo c.a c.b, ρ (c.curve t) * ‖deriv c.curve t‖ₑ := by
  let σ : ℝ → ℝ := fun t => c.clock (Set.projIcc c.a c.b c.ordered t)
  obtain ⟨_, hc, hm, h0, _⟩ := c.clock_spec
  have hσm : Monotone σ := fun x y hxy =>
    hm (Set.projIcc c.a c.b c.ordered x).property
      (Set.projIcc c.a c.b c.ordered y).property (Set.monotone_projIcc c.ordered hxy)
  have hσc : Continuous σ := hc.domRestrict.comp continuous_projIcc
  have hσeq (t : ℝ) (ht : t ∈ Icc c.a c.b) : σ t = c.clock t := by
    dsimp only [σ]
    rw [Set.projIcc_of_mem c.ordered ht]
  have hσa : σ c.a = 0 := (hσeq c.a ⟨le_rfl, c.ordered⟩).trans h0
  have hσb : σ c.b = c.euclideanLength := hσeq c.b ⟨c.ordered, le_rfl⟩
  have heq : EqOn (c.arclengthFactor ∘ σ) c.curve (Icc c.a c.b) := by
    intro t ht
    change c.arclengthFactor (σ t) = c.curve t
    rw [hσeq t ht]
    exact (c.arclengthFactor_spec.2.1 ht).symm
  have hAC : AbsolutelyContinuousOnInterval c.curve c.a c.b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le c.ordered] using hLip
  have hG : AbsolutelyContinuousOnInterval (c.arclengthFactor ∘ σ) c.a c.b :=
    hAC.congr (by simpa only [uIcc_of_le c.ordered] using heq.symm)
  have hF : AbsolutelyContinuousOnInterval c.arclengthFactor (σ c.a) (σ c.b) := by
    rw [hσa, hσb]
    exact c.arclengthFactor_spec.1.lipschitzOnWith.absolutelyContinuousOnInterval
  have hw : Measurable (fun t => ρ (c.arclengthFactor t)) :=
    hρ.comp c.arclengthFactor_spec.1.continuous.measurable
  have hchange := LiZhongQC.s26v_b_reparam_lintegral c.ordered hσm hσc hF hG hw
  rw [hσa, hσb] at hchange
  have hd : ∀ᵐ t ∂volume.restrict (Ioo c.a c.b),
      deriv (c.arclengthFactor ∘ σ) t = deriv c.curve t := by
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact heq ⟨hu.1.le, hu.2.le⟩
  calc
    c.weightedLength ρ =
        ∫⁻ t in Ioo 0 c.euclideanLength,
          ρ (c.arclengthFactor t) * ‖deriv c.arclengthFactor t‖ₑ := by
      apply lintegral_congr_ae
      filter_upwards [c.arclengthFactor_unit_speed] with t ht
      rw [ht, mul_one]
    _ = ∫⁻ t in Ioo c.a c.b,
        ρ (c.arclengthFactor (σ t)) * ‖deriv (c.arclengthFactor ∘ σ) t‖ₑ := hchange.symm
    _ = ∫⁻ t in Ioo c.a c.b, ρ (c.curve t) * ‖deriv c.curve t‖ₑ := by
      apply lintegral_congr_ae
      filter_upwards [hd, ae_restrict_mem measurableSet_Ioo] with t hdt ht
      rw [show c.arclengthFactor (σ t) = c.curve t from heq ⟨ht.1.le, ht.2.le⟩, hdt]

/-- Every Lipschitz source curve is an actual continuous rectifiable curve. -/
@[expose] def ofLRCurve (γ : LiZhongQC.LRCurve) {K : ℝ≥0}
    (hLip : LipschitzOnWith K γ.toFun (Icc 0 1)) : RectifiableCurve where
  a := 0
  b := 1
  curve := γ.toFun
  ordered := zero_le_one
  continuous := hLip.continuousOn
  boundedVariation := by
    simpa only [inter_self] using hLip.locallyBoundedVariationOn 0 1
      (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
      (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)

/-- Exact agreement with the existing LiZhong Poincaré/weighted-length API. -/
theorem weightedLength_ofLRCurve (γ : LiZhongQC.LRCurve) {K : ℝ≥0}
    (hLip : LipschitzOnWith K γ.toFun (Icc 0 1))
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    (ofLRCurve γ hLip).weightedLength ρ = γ.rhoLength ρ := by
  exact (ofLRCurve γ hLip).weightedLength_eq_lintegral_deriv hLip hρ

end RectifiableCurve

end LowDimensionalTopology.Geometry
