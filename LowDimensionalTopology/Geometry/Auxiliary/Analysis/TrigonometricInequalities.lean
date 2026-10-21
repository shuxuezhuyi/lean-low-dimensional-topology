/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

public section

namespace LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- tangent is convex on the positive acute interval. -/
theorem convexOn_tan : ConvexOn ℝ (Set.Ioo 0 (Real.pi / 2)) Real.tan := by
  have hd : DifferentiableOn ℝ Real.tan (Set.Ioo 0 (Real.pi / 2)) := by
    intro x hx
    apply (Real.differentiableAt_tan_of_mem_Ioo ?_).differentiableWithinAt
    exact ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩
  apply MonotoneOn.convexOn_of_deriv (convex_Ioo _ _) hd.continuousOn
    (by simpa only [interior_Ioo] using hd)
  simp only [interior_Ioo]
  intro x hx y hy hxy
  have hcx := (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩).ne'
  have hcy := (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hy.1], hy.2⟩).ne'
  simp only [Real.deriv_tan, one_div, ← Real.inv_one_add_tan_sq hcx,
    ← Real.inv_one_add_tan_sq hcy, inv_inv]
  have ht : Real.tan x ≤ Real.tan y :=
    Real.strictMonoOn_tan.monotoneOn ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩
      ⟨by linarith [Real.pi_pos, hy.1], hy.2⟩ hxy
  have htx := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hx.1.le hx.2.le
  gcongr

/-- cotangent is convex on the positive acute interval. -/
theorem convexOn_cot : ConvexOn ℝ (Set.Ioo 0 (Real.pi / 2)) Real.cot := by
  refine ⟨convex_Ioo _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := convexOn_tan.2
    (show Real.pi / 2 - x ∈ Set.Ioo 0 (Real.pi / 2) from ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    (show Real.pi / 2 - y ∈ Set.Ioo 0 (Real.pi / 2) from ⟨by linarith [hy.2], by linarith [hy.1]⟩)
    ha hb hab
  have he : a * (Real.pi / 2 - x) + b * (Real.pi / 2 - y) =
      Real.pi / 2 - (a * x + b * y) := by
    calc
      _ = (a + b) * (Real.pi / 2) - (a * x + b * y) := by ring
      _ = _ := by rw [hab, one_mul]
  simpa only [smul_eq_mul, he, Real.tan_pi_div_two_sub, Real.tan_inv_eq_cot] using h

/-- squared cotangent is convex on the positive acute interval. -/
theorem convexOn_cot_sq :
    ConvexOn ℝ (Set.Ioo 0 (Real.pi / 2)) (fun x => Real.cot x ^ 2) := by
  apply convexOn_cot.pow _ 2
  intro x hx
  rw [← Real.tan_inv_eq_cot]
  exact inv_nonneg.mpr (Real.tan_nonneg_of_nonneg_of_le_pi_div_two hx.1.le hx.2.le)

open scoped BigOperators


theorem mean_cotangent {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (θ : ι → ℝ)
    (hθ : ∀ i ∈ s, θ i ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cot ((∑ i ∈ s, θ i) / s.card) ≤ (∑ i ∈ s, Real.cot (θ i)) / s.card := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have h := convexOn_cot.map_sum_le (t := s) (w := fun _ => (s.card : ℝ)⁻¹)
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by simp [Finset.sum_const, nsmul_eq_mul, hc]) hθ
  simpa only [div_eq_inv_mul, Finset.mul_sum, smul_eq_mul] using h

private theorem tangent_add_cross {x y : ℝ} (hx : Real.cos x ≠ 0)
    (hy : Real.cos y ≠ 0) (hxy : Real.cos (x + y) ≠ 0) :
    Real.tan (x + y) * (1 - Real.tan x * Real.tan y) = Real.tan x + Real.tan y := by
  simp only [Real.tan_eq_sin_div_cos]
  field_simp
  rw [Real.sin_add, Real.cos_add]
  ring


theorem tangent_product {x y : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 2))
    (hy : y ∈ Set.Ioo 0 (Real.pi / 2)) (hxy : x + y < Real.pi / 2) :
    Real.tan x * Real.tan y ≤ Real.tan ((x + y) / 2) ^ 2 := by
  have hc : ∀ z ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos z ≠ 0 := by
    intro z hz
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hz.1], hz.2⟩).ne'
  have hm : (x + y) / 2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hx.1, hy.1], by linarith [Real.pi_pos]⟩
  have hs : x + y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨by linarith [hx.1, hy.1], hxy⟩
  have hp := tangent_add_cross (hc x hx) (hc y hy) (hc _ hs)
  have he : (x + y) / 2 + (x + y) / 2 = x + y := by ring
  have hq := tangent_add_cross (hc _ hm) (hc _ hm)
    (by rw [he]; exact hc _ hs)
  rw [he] at hq
  have hj : Real.tan ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ≤
      (1 / 2 : ℝ) • Real.tan x + (1 / 2 : ℝ) • Real.tan y :=
    convexOn_tan.2 hx hy (by norm_num) (by norm_num) (by norm_num)
  have hm' : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y = (x + y) / 2 := by ring
  simp only [smul_eq_mul, hm'] at hj
  have ht : 0 < Real.tan (x + y) := by
    exact Real.tan_pos_of_pos_of_lt_pi_div_two hs.1 hs.2
  apply (mul_le_mul_iff_right₀ ht).mp
  nlinarith [hp, hq, hj]

end LowDimensionalTopology.Geometry.Auxiliary.Analysis
