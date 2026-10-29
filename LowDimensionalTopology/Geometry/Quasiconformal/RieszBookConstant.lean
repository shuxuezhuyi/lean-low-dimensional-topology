module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# An explicit real-line Riesz constant

The scalar family is
`A p = 1 / (((p / (p - 1)) ^ (2 / p) - 1) ^ (p / 2))`.
This file proves the constant's required continuity, positivity and exact
value at two. The singular-integral estimate is a separate obligation.
-/

@[expose] public section
noncomputable section

open Set Topology

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The positive scalar obtained after the book's horizontal-slice calculation. -/
def rieszBookDenominator (p : ℝ) : ℝ := (p / (p - 1)) ^ (2 / p) - 1

/-- The actual constant printed at the end of the real-line Riesz proof. -/
def rieszBookConstant (p : ℝ) : ℝ := 1 / (rieszBookDenominator p) ^ (p / 2)

private theorem riesz_base_bounds {p : ℝ} (hp : 2 ≤ p) :
    1 < p / (p - 1) ∧ p / (p - 1) ≤ 2 := by
  have hden : 0 < p - 1 := by linarith
  constructor
  · rw [lt_div_iff₀ hden]
    linarith
  · rw [div_le_iff₀ hden]
    linarith

/-- The denominator is in `(0,1]` throughout the original range `p≥2`. -/
theorem rieszBookDenominator_bounds {p : ℝ} (hp : 2 ≤ p) :
    0 < rieszBookDenominator p ∧ rieszBookDenominator p ≤ 1 := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hb, hb2⟩ := riesz_base_bounds hp
  have he0 : 0 < 2 / p := div_pos (by norm_num) hp0
  have he1 : 2 / p ≤ 1 := (div_le_one hp0).2 hp
  have hlo := Real.one_lt_rpow hb he0
  have hhi := Real.rpow_le_rpow_of_exponent_le hb.le he1
  rw [Real.rpow_one] at hhi
  constructor <;> dsimp [rieszBookDenominator] <;> linarith

/-- The book's constant is at least one; in particular it is a genuine
positive bound, including the endpoint `p=2`. -/
theorem one_le_rieszBookConstant {p : ℝ} (hp : 2 ≤ p) :
    1 ≤ rieszBookConstant p := by
  obtain ⟨hd, hd1⟩ := rieszBookDenominator_bounds hp
  have hv : 0 < (rieszBookDenominator p) ^ (p / 2) := Real.rpow_pos_of_pos hd _
  have hv1 : (rieszBookDenominator p) ^ (p / 2) ≤ 1 :=
    Real.rpow_le_one hd.le hd1 (by linarith)
  exact (le_div_iff₀ hv).2 (by simpa using hv1)

/-- The exact Hilbert-space normalization in the printed formula. -/
theorem rieszBookConstant_two : rieszBookConstant 2 = 1 := by
  norm_num [rieszBookConstant, rieszBookDenominator, Real.rpow_one]

/-- Continuity of the same explicit constants on the complete book range,
including the one-sided endpoint at two. -/
theorem rieszBookConstant_continuousOn : ContinuousOn rieszBookConstant (Ici 2) := by
  intro p hp
  have hp2 : 2 ≤ p := hp
  have hp0 : 0 < p := by linarith
  have hm : p - 1 ≠ 0 := by linarith
  have hb : p / (p - 1) ≠ 0 := (lt_trans zero_lt_one (riesz_base_bounds hp2).1).ne'
  have hd := (rieszBookDenominator_bounds hp2).1
  have hcbase : ContinuousAt (fun q : ℝ => q / (q - 1)) p :=
    continuousAt_id.div (continuousAt_id.sub continuousAt_const) hm
  have hcexp : ContinuousAt (fun q : ℝ => 2 / q) p :=
    continuousAt_const.div continuousAt_id hp0.ne'
  have hcden : ContinuousAt rieszBookDenominator p :=
    (hcbase.rpow hcexp (Or.inl hb)).sub continuousAt_const
  have hcpower : ContinuousAt (fun q : ℝ => (rieszBookDenominator q) ^ (q / 2)) p :=
    hcden.rpow (continuousAt_id.div_const 2) (Or.inl hd.ne')
  exact (continuousAt_const.div hcpower (Real.rpow_pos_of_pos hd _).ne').continuousWithinAt

end LowDimensionalTopology.Geometry.Quasiconformal
