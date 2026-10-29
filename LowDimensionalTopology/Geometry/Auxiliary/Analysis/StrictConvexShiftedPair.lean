/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# A pair of shifted values of a strictly convex real function

Two complementary strict convex combinations show that every fixed positive
increment of a strictly convex function is strictly increasing. The pair of
values at a point and at a fixed nonzero shift is therefore injective.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- Values at a point and a fixed nonzero real shift distinguish points for
a strictly convex real function. Both signs of the shift are allowed. -/
theorem strictConvexOn_shifted_pair_injective (f : ℝ → ℝ)
    (hf : StrictConvexOn ℝ Set.univ f) (c : ℝ) (hc : c ≠ 0) :
    Function.Injective (fun s => (f s, f (s + c))) := by
  have hmono (d : ℝ) (hd : 0 < d) : StrictMono (fun s => f (s + d) - f s) := by
    intro x y hxy
    have hden : 0 < y + d - x := by linarith
    let a := d / (y + d - x)
    let b := (y - x) / (y + d - x)
    have ha : 0 < a := div_pos hd hden
    have hb : 0 < b := div_pos (sub_pos.mpr hxy) hden
    have hab : a + b = 1 := by
      dsimp [a, b]
      field_simp [ne_of_gt hden]
      ring
    have hy : a * x + b * (y + d) = y := by
      dsimp [a, b]
      field_simp [ne_of_gt hden]
      ring
    have hxd : b * x + a * (y + d) = x + d := by
      dsimp [a, b]
      field_simp [ne_of_gt hden]
      ring
    have hne : x ≠ y + d := ne_of_lt (by linarith)
    have h₁ := hf.2 (Set.mem_univ x) (Set.mem_univ (y + d)) hne ha hb hab
    have h₂ := hf.2 (Set.mem_univ x) (Set.mem_univ (y + d)) hne hb ha (by linarith)
    simp only [smul_eq_mul, hy] at h₁
    simp only [smul_eq_mul, hxd] at h₂
    have hsum : (a * f x + b * f (y + d)) + (b * f x + a * f (y + d)) =
        f x + f (y + d) := by
      calc
        _ = (a + b) * f x + (a + b) * f (y + d) := by ring
        _ = _ := by rw [hab, one_mul, one_mul]
    linarith
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · intro x y hpair
    have hshift : x + c = y + c :=
      (hmono (-c) (neg_pos.mpr hcneg)).injective (by
        simpa only [add_neg_cancel_right] using
          congrArg (fun p : ℝ × ℝ => p.1 - p.2) hpair)
    exact add_right_cancel hshift
  · intro x y hpair
    apply (hmono c hcpos).injective
    exact congrArg (fun p : ℝ × ℝ => p.2 - p.1) hpair

end LowDimensionalTopology.Geometry.Auxiliary.Analysis
