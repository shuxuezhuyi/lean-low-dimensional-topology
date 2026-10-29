module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Bounded variation from genuine local neighborhoods

Neighborhood-local variation on a real compact interval implies global bounded
variation. This is different from Mathlib's compact-subinterval predicate.
The proof glues adjacent intervals and uses connectedness of the parameter
interval; it does not require differentiability or absolute continuity.
-/

public section
noncomputable section
open Set Filter
open scoped Topology ENNReal

namespace LowDimensionalTopology.Geometry

variable {E : Type*} [PseudoEMetricSpace E] {f : ℝ → E}

private theorem boundedVariationOn_Icc_glue {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z)
    (h₁ : BoundedVariationOn f (Icc x y)) (h₂ : BoundedVariationOn f (Icc y z)) :
    BoundedVariationOn f (Icc x z) := by
  have he : eVariationOn f (Icc x y) + eVariationOn f (Icc y z) =
      eVariationOn f (Icc x z) := by
    simpa only [univ_inter] using
      eVariationOn.Icc_add_Icc f (s := univ) hxy hyz (mem_univ y)
  change eVariationOn f (Icc x z) ≠ ∞
  rw [← he]
  exact ENNReal.add_ne_top.mpr ⟨h₁, h₂⟩

private theorem boundedVariationOn_uIcc_trans {x y z : ℝ}
    (h₁ : BoundedVariationOn f (uIcc x y)) (h₂ : BoundedVariationOn f (uIcc y z)) :
    BoundedVariationOn f (uIcc x z) := by
  have hordered : ∀ x y z : ℝ, x ≤ z →
      BoundedVariationOn f (uIcc x y) → BoundedVariationOn f (uIcc y z) →
        BoundedVariationOn f (uIcc x z) := by
    intro x y z hxz h₁ h₂
    by_cases hxy : x ≤ y
    · by_cases hyz : y ≤ z
      · rw [uIcc_of_le hxz]
        apply boundedVariationOn_Icc_glue hxy hyz
        · simpa only [uIcc_of_le hxy] using h₁
        · simpa only [uIcc_of_le hyz] using h₂
      · exact h₁.mono (uIcc_subset_uIcc left_mem_uIcc
          (mem_uIcc_of_le hxz (le_of_not_ge hyz)))
    · exact h₂.mono (uIcc_subset_uIcc
        (mem_uIcc_of_le (le_of_not_ge hxy) hxz) right_mem_uIcc)
  rcases le_total x z with hxz | hzx
  · exact hordered x y z hxz h₁ h₂
  · have h₂' : BoundedVariationOn f (uIcc z y) := by
      simpa only [uIcc_comm z y] using h₂
    have h₁' : BoundedVariationOn f (uIcc y x) := by
      simpa only [uIcc_comm y x] using h₁
    simpa only [uIcc_comm z x] using hordered z y x hzx h₂' h₁'

/-- Genuine point-neighborhood bounded variation on a compact parameter interval
implies bounded variation on the whole interval, including both endpoints. -/
theorem boundedVariationOn_Icc_of_nhdsWithin {a b : ℝ}
    (hloc : ∀ x ∈ Icc a b, ∃ U ∈ 𝓝[Icc a b] x, BoundedVariationOn f U) :
    BoundedVariationOn f (Icc a b) := by
  by_cases hab : a ≤ b
  · have hnear : ∀ x ∈ Icc a b,
        ∀ᶠ y in 𝓝[Icc a b] x, BoundedVariationOn f (uIcc x y) := by
      intro x hx
      obtain ⟨U, hU, hBV⟩ := hloc x hx
      obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hU
      have hb : OrdConnected (Metric.ball x ε) := by
        rw [Real.ball_eq_Ioo]
        infer_instance
      have hxball : x ∈ Metric.ball x ε := by
        simpa only [Metric.mem_ball, dist_self] using hε
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hε),
        self_mem_nhdsWithin] with y hy hys
      apply hBV.mono
      intro z hz
      exact hsub ⟨hb.uIcc_subset hxball hy hz, uIcc_subset_Icc hx hys hz⟩
    have hglobal := isPreconnected_Icc.induction₂
      (fun x y : ℝ => BoundedVariationOn f (uIcc x y)) hnear
      (fun x y z _ _ _ => boundedVariationOn_uIcc_trans)
      (fun x y _ _ h => by simpa only [uIcc_comm y x] using h)
      (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    simpa only [uIcc_of_le hab] using hglobal
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hab)]
    exact BoundedVariationOn.of_subsingleton Set.subsingleton_empty

end LowDimensionalTopology.Geometry
