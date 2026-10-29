module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicSegments
public import Mathlib.Topology.Order.IntermediateValue

public section
open Set
open scoped UpperHalfPlane Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- A continuous traversal inside a genuine h-segment, reaching both ends,
contains the whole segment. No monotonicity or regularity is assumed. -/
theorem image_eq_closedHSegment_of_subset {η : ℝ → ℍ} {z w : ℍ}
    (hzw : z ≠ w) (hη : ContinuousOn η (Icc 0 1))
    (h0 : η 0 = z) (h1 : η 1 = w)
    (htrace : η '' Icc 0 1 ⊆ closedHSegment z w) :
    η '' Icc 0 1 = closedHSegment z w := by
  refine subset_antisymm htrace ?_
  intro u hu
  have huCopy := hu
  obtain ⟨γ, hγ, s, t, hst, hs, ht, r, hr, hru⟩ := huCopy
  have hst' : s < t := lt_of_le_of_ne hst (fun he =>
    hzw (hs.symm.trans ((congrArg γ he).trans ht)))
  have hseg : closedHSegment z w = γ '' Icc s t := by
    rw [← hs, ← ht]
    exact closedHSegment_eq_image_Icc hγ hst'
  have hf : ContinuousOn (fun x => dist z (η x)) (Icc 0 1) :=
    (continuous_const.dist continuous_id).comp_continuousOn hη
  have hbetween : dist z u ∈ Icc (dist z (η 0)) (dist z (η 1)) := by
    rw [h0, h1, dist_self]
    refine ⟨dist_nonneg, ?_⟩
    have he := dist_triangle_eq_of_mem_closedHSegment hu
    linarith [dist_nonneg (x := u) (y := w)]
  obtain ⟨x, hx, hxd⟩ := intermediate_value_Icc zero_le_one hf hbetween
  obtain ⟨q, hq, hηq⟩ := hseg ▸ htrace ⟨x, hx, rfl⟩
  have he : dist (γ s) (γ q) = dist (γ s) (γ r) := by
    rw [hs, hηq, hru]
    exact hxd
  rw [hγ.1.dist_eq, hγ.1.dist_eq, Real.dist_eq, Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr hq.1), abs_of_nonpos (sub_nonpos.mpr hr.1)] at he
  have hqr : q = r := by linarith
  exact ⟨x, hx, hηq.symm.trans ((congrArg γ hqr).trans hru)⟩

/-- The same continuous traversal statement in the actual disc model. -/
theorem image_eq_closedDiscHSegment_of_subset {η : ℝ → 𝔻} {z w : 𝔻}
    (hzw : z ≠ w) (hη : ContinuousOn η (Icc 0 1))
    (h0 : η 0 = z) (h1 : η 1 = w)
    (htrace : η '' Icc 0 1 ⊆ closedDiscHSegment z w) :
    η '' Icc 0 1 = closedDiscHSegment z w := by
  have hD : (discToHalfPlane ∘ η) '' Icc 0 1 =
      closedHSegment (discToHalfPlane z) (discToHalfPlane w) :=
    image_eq_closedHSegment_of_subset
      (fun he => hzw (cayleyHomeomorph.symm.injective he))
      (continuous_discToHalfPlane.comp_continuousOn hη)
      (by simp only [Function.comp_apply, h0])
      (by simp only [Function.comp_apply, h1])
      (by rintro v ⟨t, ht, rfl⟩; exact htrace ⟨t, ht, rfl⟩)
  refine subset_antisymm htrace ?_
  intro u hu
  have huH : discToHalfPlane u ∈
      closedHSegment (discToHalfPlane z) (discToHalfPlane w) := hu
  obtain ⟨t, ht, he⟩ := hD.symm ▸ huH
  exact ⟨t, ht, cayleyHomeomorph.symm.injective he⟩

end LowDimensionalTopology.Geometry.Hyperbolic
