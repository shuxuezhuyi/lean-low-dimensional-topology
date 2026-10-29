module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A literal lower power bound from a Holder upper bound

The radius and the bounded quantity may vanish. The coefficient of the
lower estimate is explicit and strictly positive.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Inverting the original Holder exponent gives an explicit lower bound,
including both zero boundary cases. -/
theorem power_lower_bound_of_holder_upper_bound {β A r s : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hA : 0 ≤ A)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hs0 : 0 ≤ s)
    (h : s ≤ A * r ^ β + r) :
    0 < (A + 1) ^ (-(1 / β)) ∧
      (A + 1) ^ (-(1 / β)) * s ^ (1 / β) ≤ r := by
  have hA1 : 0 < A + 1 := add_pos_of_nonneg_of_pos hA zero_lt_one
  have hrr : r ≤ r ^ β := Real.self_le_rpow_of_le_one hr0 hr1 hβ1
  have hb : s ≤ (A + 1) * r ^ β :=
    (h.trans (add_le_add_right hrr _)).trans_eq (add_one_mul A (r ^ β)).symm
  have hdiv : s / (A + 1) ≤ r ^ β := (div_le_iff₀ hA1).mpr
    (by simpa only [mul_comm] using hb)
  have hroot : (s / (A + 1)) ^ (1 / β) ≤ r := by
    have hpow := Real.rpow_le_rpow (div_nonneg hs0 hA1.le) hdiv
      (one_div_nonneg.mpr hβ.le)
    simpa only [one_div, Real.rpow_rpow_inv hr0 hβ.ne'] using hpow
  have heq : (s / (A + 1)) ^ (1 / β) =
      (A + 1) ^ (-(1 / β)) * s ^ (1 / β) := by
    rw [Real.div_rpow hs0 hA1.le, Real.rpow_neg hA1.le, div_eq_mul_inv, mul_comm]
  exact ⟨Real.rpow_pos_of_pos hA1 _, heq ▸ hroot⟩

end LowDimensionalTopology.Geometry.Quasiconformal
