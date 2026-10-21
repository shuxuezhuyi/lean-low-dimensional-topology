/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace LowDimensionalTopology.Geometry.DiscreteGroups

/-- The ordered positive-curvature branch orders have precisely the spherical profiles. -/
theorem finiteRotation_branch_profiles {n₁ n₂ n₃ : ℕ}
    (h₁ : 2 ≤ n₁) (h₁₂ : n₁ ≤ n₂) (h₂₃ : n₂ ≤ n₃)
    (hsum : (1 : ℝ) / n₁ + 1 / n₂ + 1 / n₃ > 1) :
    n₁ = 2 ∧ (n₂ = 2 ∨ (n₂ = 3 ∧ (n₃ = 3 ∨ n₃ = 4 ∨ n₃ = 5))) := by
  have hrecip (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
      (1 : ℝ) / n ≤ 1 / m :=
    one_div_le_one_div_of_le (Nat.cast_pos.mpr hm) (by exact_mod_cast hmn)
  have hn₁ : n₁ = 2 := by
    by_contra hn₁
    have h₃₁ : 3 ≤ n₁ := by omega
    have ha := hrecip 3 n₁ (by decide) h₃₁
    have hb := hrecip 3 n₂ (by decide) (h₃₁.trans h₁₂)
    have hc := hrecip 3 n₃ (by decide) (h₃₁.trans (h₁₂.trans h₂₃))
    norm_num at ha hb hc hsum
    linarith
  refine ⟨hn₁, ?_⟩
  subst n₁
  by_cases hn₂ : n₂ = 2
  · exact Or.inl hn₂
  · right
    have hn₂' : n₂ = 3 := by
      by_contra hn₂'
      have h₄₂ : 4 ≤ n₂ := by omega
      have hb := hrecip 4 n₂ (by decide) h₄₂
      have hc := hrecip 4 n₃ (by decide) (h₄₂.trans h₂₃)
      norm_num at hb hc hsum
      linarith
    refine ⟨hn₂', ?_⟩
    subst n₂
    have hn₃ : n₃ < 6 := by
      by_contra hn₃
      have hc := hrecip 6 n₃ (by decide) (by omega)
      norm_num at hc hsum
      linarith
    omega

/-- Conversely, each of these ordered spherical profiles has reciprocal sum greater than one. -/
theorem finiteRotation_branch_profiles_iff {n₁ n₂ n₃ : ℕ}
    (h₁ : 2 ≤ n₁) (h₁₂ : n₁ ≤ n₂) (h₂₃ : n₂ ≤ n₃) :
    (1 : ℝ) / n₁ + 1 / n₂ + 1 / n₃ > 1 ↔
      n₁ = 2 ∧ (n₂ = 2 ∨ (n₂ = 3 ∧ (n₃ = 3 ∨ n₃ = 4 ∨ n₃ = 5))) := by
  refine ⟨finiteRotation_branch_profiles h₁ h₁₂ h₂₃, ?_⟩
  rintro ⟨rfl, hn₂ | ⟨rfl, hn₃⟩⟩
  · subst n₂
    have hn₃ : (0 : ℝ) < n₃ := by exact_mod_cast (show 0 < n₃ by omega)
    have hpos : (0 : ℝ) < 1 / n₃ := div_pos zero_lt_one hn₃
    norm_num
    linarith
  · rcases hn₃ with rfl | rfl | rfl <;> norm_num

/-- The finite set notation version of the three exceptional branch profiles. -/
theorem finiteRotation_branch_profiles_mem {n₁ n₂ n₃ : ℕ}
    (h₁ : 2 ≤ n₁) (h₁₂ : n₁ ≤ n₂) (h₂₃ : n₂ ≤ n₃)
    (hsum : (1 : ℝ) / n₁ + 1 / n₂ + 1 / n₃ > 1) :
    n₁ = 2 ∧ (n₂ = 2 ∨ (n₂ = 3 ∧ n₃ ∈ ({3, 4, 5} : Set ℕ))) := by
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
    finiteRotation_branch_profiles h₁ h₁₂ h₂₃ hsum

/-- The Euler reciprocal-sum identity determines the group order in every branch profile. -/
theorem finiteRotation_branch_order_profiles {h n₁ n₂ n₃ : ℕ}
    (hh : 2 ≤ h) (h₁ : 2 ≤ n₁) (h₁₂ : n₁ ≤ n₂) (h₂₃ : n₂ ≤ n₃)
    (heq : (1 : ℝ) / n₁ + 1 / n₂ + 1 / n₃ = 1 + 2 / h) :
    (h = 2 * n₃ ∧ n₁ = 2 ∧ n₂ = 2) ∨
      (h = 12 ∧ n₁ = 2 ∧ n₂ = 3 ∧ n₃ = 3) ∨
      (h = 24 ∧ n₁ = 2 ∧ n₂ = 3 ∧ n₃ = 4) ∨
      (h = 60 ∧ n₁ = 2 ∧ n₂ = 3 ∧ n₃ = 5) := by
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
  have hpos : (0 : ℝ) < 2 / h := div_pos (by norm_num) (by exact_mod_cast (show 0 < h by omega))
  have hsum : (1 : ℝ) / n₁ + 1 / n₂ + 1 / n₃ > 1 := by linarith
  obtain ⟨rfl, hn₂ | ⟨rfl, hn₃⟩⟩ := finiteRotation_branch_profiles h₁ h₁₂ h₂₃ hsum
  · subst n₂
    have hn₃R : (n₃ : ℝ) ≠ 0 := by exact_mod_cast (show n₃ ≠ 0 by omega)
    norm_num at heq
    field_simp [hhR, hn₃R] at heq
    have horder : h = 2 * n₃ := by
      exact_mod_cast (show (h : ℝ) = 2 * (n₃ : ℝ) by nlinarith [heq])
    exact Or.inl ⟨horder, rfl, rfl⟩
  · rcases hn₃ with rfl | rfl | rfl
    · norm_num at heq
      field_simp [hhR] at heq
      have horder : h = 12 := by exact_mod_cast (show (h : ℝ) = 12 by nlinarith [heq])
      exact Or.inr (Or.inl ⟨horder, rfl, rfl, rfl⟩)
    · norm_num at heq
      field_simp [hhR] at heq
      have horder : h = 24 := by exact_mod_cast (show (h : ℝ) = 24 by nlinarith [heq])
      exact Or.inr (Or.inr (Or.inl ⟨horder, rfl, rfl, rfl⟩))
    · norm_num at heq
      field_simp [hhR] at heq
      have horder : h = 60 := by exact_mod_cast (show (h : ℝ) = 60 by nlinarith [heq])
      exact Or.inr (Or.inr (Or.inr ⟨horder, rfl, rfl, rfl⟩))

/-- The same arithmetic classification expressed as exact quadruples of natural numbers. -/
theorem finiteRotation_branch_order_quadruples {h n₁ n₂ n₃ : ℕ}
    (hh : 2 ≤ h) (h₁ : 2 ≤ n₁) (h₁₂ : n₁ ≤ n₂) (h₂₃ : n₂ ≤ n₃)
    (heq : (1 : ℝ) / n₁ + 1 / n₂ + 1 / n₃ = 1 + 2 / h) :
    (h, n₁, n₂, n₃) = (2 * n₃, 2, 2, n₃) ∨
      (h, n₁, n₂, n₃) = (12, 2, 3, 3) ∨
      (h, n₁, n₂, n₃) = (24, 2, 3, 4) ∨
      (h, n₁, n₂, n₃) = (60, 2, 3, 5) := by
  rcases finiteRotation_branch_order_profiles hh h₁ h₁₂ h₂₃ heq with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

end LowDimensionalTopology.Geometry.DiscreteGroups
