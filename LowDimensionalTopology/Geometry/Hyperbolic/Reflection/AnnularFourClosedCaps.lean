module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularMirrorCapGeometry
public import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- All six pairs of the four literal closed annular Schottky caps are disjoint.
The two reflected caps retain the actual unit reflection and their full images. -/
theorem annular_four_closed_caps_disjoint (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hinner : 1 + r < x) (houter : x + r < E) :
    let σ := (HalfPlaneLine.circle 0 1 zero_lt_one).reflection
    let O := {z : ℍ | E ≤ ‖(z : ℂ)‖}
    let B := {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ ≤ r}
    Disjoint (σ '' O) O ∧ Disjoint (σ '' O) B ∧
      Disjoint (σ '' O) (σ '' B) ∧ Disjoint O B ∧
      Disjoint O (σ '' B) ∧ Disjoint B (σ '' B) := by
  let σ := (HalfPlaneLine.circle 0 1 zero_lt_one).reflection
  let O := {z : ℍ | E ≤ ‖(z : ℂ)‖}
  let B := {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ ≤ r}
  change Disjoint (σ '' O) O ∧ Disjoint (σ '' O) B ∧
    Disjoint (σ '' O) (σ '' B) ∧ Disjoint O B ∧
    Disjoint O (σ '' B) ∧ Disjoint B (σ '' B)
  have hx : 0 ≤ x := by linarith
  have hB (z : ℍ) (hz : z ∈ B) : 1 < ‖(z : ℂ)‖ := by
    have ht := norm_add_le ((x : ℂ) - (z : ℂ)) (z : ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hx, norm_sub_rev] at ht
    have hzr : ‖(z : ℂ) - (x : ℂ)‖ ≤ r := hz
    linarith only [ht, hzr, hinner]
  have houtside (z : ℍ) (hz : z ∈ O ∪ B) : 1 < ‖(z : ℂ)‖ := by
    rcases hz with hz | hz
    · exact hE.trans_le hz
    · exact hB z hz
  have hcross : Disjoint (O ∪ B) (σ '' (O ∪ B)) := by
    apply disjoint_left.mpr
    rintro z hz ⟨w, hw, rfl⟩
    have hin : ‖(σ w : ℂ)‖ < 1 := by
      change ‖((HalfPlaneLine.circle 0 1 zero_lt_one).reflection w : ℂ)‖ < 1
      rw [unitCircle_reflection_norm]
      exact inv_lt_one_of_one_lt₀ (houtside w hw)
    exact (not_lt_of_ge hin.le) (houtside _ hz)
  have hOB : Disjoint O B :=
    annular_closed_outer_disjoint_small E r x hx houter
  have hσ : Function.Injective σ :=
    (HalfPlaneLine.circle 0 1 zero_lt_one).reflection_involutive.injective
  have hIOB : Disjoint (σ '' O) (σ '' B) :=
    Set.disjoint_image_of_injective hσ hOB
  have hOOi : Disjoint O (σ '' O) :=
    hcross.mono subset_union_left (image_mono subset_union_left)
  have hBOi : Disjoint B (σ '' O) :=
    hcross.mono subset_union_right (image_mono subset_union_left)
  have hOBi : Disjoint O (σ '' B) :=
    hcross.mono subset_union_left (image_mono subset_union_right)
  have hBBi : Disjoint B (σ '' B) :=
    hcross.mono subset_union_right (image_mono subset_union_right)
  exact ⟨hOOi.symm, hBOi.symm, hIOB, hOB, hOBi, hBBi⟩

end LowDimensionalTopology.Geometry.Hyperbolic
