module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.RectifiableFreeClassBound

/-!
# Free-class infima over all actual continuous rectifiable lifts

A lift retains the actual continuous BV curve and its pointwise projection.
The free-class infimum agrees with the source Lipschitz free-class infimum,
even though fixed-parameter loop lengths can differ for singular parameters.
-/

public section
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane unitInterval ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- An actual continuous rectifiable lift of the complete parametrized loop. -/
@[expose] def IsRectifiableLoopLift {X : Type*} [TopologicalSpace X]
    (p : ℍ → X) (α : LiZhongQC.Loop X) (c : RectifiableCurve) : Prop :=
  c.a = 0 ∧ c.b = 1 ∧
    ∃ hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c.curve t).im,
      ∀ t : I, p ⟨c.curve t, hpos t t.property⟩ = α.2 t

/-- Literal arclength infimum over every continuous BV lift of this loop. -/
@[expose] def rectifiableLoopLength {X : Type*} [TopologicalSpace X]
    (p : ℍ → X) (α : LiZhongQC.Loop X) : ℝ≥0∞ :=
  ⨅ c : RectifiableCurve, ⨅ _ : IsRectifiableLoopLift p α c,
    c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im))

/-- The free-class infimum over all actual continuous rectifiable lifted loops. -/
@[expose] def rectifiableFreeHomotopyLength {X : Type*} [TopologicalSpace X]
    (p : ℍ → X) (α : LiZhongQC.Loop X) : ℝ≥0∞ :=
  ⨅ β : LiZhongQC.Loop X, ⨅ _ : LiZhongQC.FreelyHomotopic α β,
    rectifiableLoopLength p β

/-- Every source-admissible Lipschitz lift is an actual BV lift of equal literal
length. This direction does not need any regularity of the projection. -/
theorem rectifiableLoopLength_le_source
    {X : Type*} [TopologicalSpace X] (p : ℍ → X) (α : LiZhongQC.Loop X) :
    rectifiableLoopLength p α ≤ LiZhongQC.poincareLengthLoop p α := by
  let ρ : ℂ → ℝ≥0∞ := fun ζ => ENNReal.ofReal (1 / ζ.im)
  unfold LiZhongQC.poincareLengthLoop
  refine le_iInf₂ fun f hf => ?_
  obtain ⟨⟨K, hLip⟩, hpos, hproj⟩ := hf
  let c : RectifiableCurve :=
    { a := 0
      b := 1
      curve := f
      ordered := zero_le_one
      continuous := hLip.continuousOn
      boundedVariation := by
        simpa only [inter_self] using hLip.locallyBoundedVariationOn 0 1
          (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
          (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩) }
  have hclift : IsRectifiableLoopLift p α c := by
    refine ⟨rfl, rfl, hpos, ?_⟩
    intro t
    simpa only [Path.extend_apply α.2 t.property] using hproj t t.property (hpos t t.property)
  have hlen : c.weightedLength ρ = LiZhongQC.hypLength f := by
    rw [c.weightedLength_eq_lintegral_deriv hLip measurable_halfPlane_poincareDensity]
    unfold LiZhongQC.hypLength
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    change ENNReal.ofReal (1 / (f t).im) * ‖deriv f t‖ₑ =
      ‖deriv f t‖ₑ / ENNReal.ofReal (f t).im
    rw [ENNReal.ofReal_div_of_pos (hpos t (Ioo_subset_Icc_self ht)), ENNReal.ofReal_one]
    rw [one_div, div_eq_mul_inv]
    exact mul_comm _ _
  calc
    rectifiableLoopLength p α ≤ c.weightedLength ρ := iInf₂_le c hclift
    _ = LiZhongQC.hypLength f := hlen

/-- The full continuous-rectifiable free-class infimum equals the source
Lipschitz free-class infimum. The forward comparison uses an actual homotopy of
the BV curve to its equal-weight normalized representative. -/
theorem rectifiableFreeHomotopyLength_eq_source
    {X : Type*} [TopologicalSpace X] (p : ℍ → X) (hp : Continuous p)
    (α : LiZhongQC.Loop X) :
    rectifiableFreeHomotopyLength p α = LiZhongQC.freeHomotopyLength p α := by
  apply le_antisymm
  · unfold LiZhongQC.freeHomotopyLength
    refine le_iInf₂ fun β hβ => ?_
    exact (iInf₂_le β hβ).trans (rectifiableLoopLength_le_source p β)
  · unfold rectifiableFreeHomotopyLength
    refine le_iInf₂ fun β hβ => ?_
    rw [LiZhongQC.s30b_fhl_congr p hβ]
    unfold rectifiableLoopLength
    refine le_iInf₂ fun c hc => ?_
    obtain ⟨ha, hb, hpos, hproj⟩ := hc
    exact RectifiableCurve.freeHomotopyLength_le_weightedLength p hp c ha hb hpos β hproj

end LowDimensionalTopology.Geometry.Surfaces
