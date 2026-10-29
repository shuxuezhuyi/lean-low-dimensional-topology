module

public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.RectifiableWeightedLength

/-!
# Full weighted arclength is unchanged by monotone onto reparametrization

The actual cumulative Euclidean variation clocks agree under the given
reparametrization. This identifies the entire arclength factors, rather than
merely their trace sets, and therefore retains pauses and traversal counts.
No derivative of the original reparametrization is used.
-/

public section
noncomputable section
open Set
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.RectifiableCurve

/-- A monotone onto change of the traversed compact interval preserves the
literal line integral for every density, including singular parameter changes. -/
theorem weightedLength_eq_of_monotone_onto_reparam
    (c d : RectifiableCurve) (σ : ℝ → ℝ)
    (hσ : MonotoneOn σ (Icc c.a c.b))
    (himage : σ '' Icc c.a c.b = Icc d.a d.b)
    (ha : σ c.a = d.a) (hb : σ c.b = d.b)
    (hpoint : EqOn c.curve (d.curve ∘ σ) (Icc c.a c.b))
    (ρ : ℂ → ℝ≥0∞) : c.weightedLength ρ = d.weightedLength ρ := by
  have hclock (t : ℝ) (ht : t ∈ Icc c.a c.b) : c.clock t = d.clock (σ t) := by
    have hvar := variationOnFromTo.comp_eq_of_monotoneOn d.curve σ hσ
      (left_mem_Icc.mpr c.ordered) ht
    rw [himage, ha] at hvar
    have hcongr : variationOnFromTo c.curve (Icc c.a c.b) c.a t =
        variationOnFromTo (d.curve ∘ σ) (Icc c.a c.b) c.a t := by
      rw [variationOnFromTo.eq_of_le _ _ ht.1,
        variationOnFromTo.eq_of_le _ _ ht.1]
      exact congrArg ENNReal.toReal (eVariationOn.congr (hpoint.mono inter_subset_left))
    exact hcongr.trans hvar
  have hlength : c.euclideanLength = d.euclideanLength := by
    change c.clock c.b = d.clock d.b
    rw [hclock c.b (right_mem_Icc.mpr c.ordered), hb]
  have hfactor : EqOn c.curve (d.arclengthFactor ∘ c.clock) (Icc c.a c.b) := by
    intro t ht
    have hσt : σ t ∈ Icc d.a d.b := himage ▸ (mem_image_of_mem σ ht)
    calc
      c.curve t = d.curve (σ t) := hpoint ht
      _ = d.arclengthFactor (d.clock (σ t)) := d.arclengthFactor_spec.2.1 hσt
      _ = d.arclengthFactor (c.clock t) := congrArg d.arclengthFactor (hclock t ht).symm
  calc
    c.weightedLength ρ = ∫⁻ t in Ioo 0 c.euclideanLength, ρ (d.arclengthFactor t) :=
      c.weightedLength_eq_of_factor ρ hfactor
    _ = d.weightedLength ρ := by rw [hlength]; rfl

end LowDimensionalTopology.Geometry.RectifiableCurve
