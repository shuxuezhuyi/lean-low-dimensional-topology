module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularFourCapMappings
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularFourClosedCaps
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane Pointwise

namespace LowDimensionalTopology.Geometry.Hyperbolic

private theorem capPair_positive_powers {G α : Type*} [Group G] [MulAction G α]
    (g : G) (X Y : Set α) (hXY : Disjoint X Y) (hX : g • Yᶜ ⊆ X) (n : ℕ) :
    g ^ (n + 1) • Yᶜ ⊆ X := by
  induction n with
  | zero => simpa only [Nat.zero_add, pow_one] using hX
  | succ n ih =>
    rw [pow_succ', mul_smul]
    exact (smul_set_mono (ih.trans hXY.subset_compl_right)).trans hX

private theorem capPair_zpow_gap {G α : Type*} [Group G] [MulAction G α]
    (g : G) (X Y : Set α) (hXY : Disjoint X Y)
    (hX : g • Yᶜ ⊆ X) (hY : g⁻¹ • Xᶜ ⊆ Y) (n : ℤ) (hn : n ≠ 0) :
    g ^ n • (X ∪ Y)ᶜ ⊆ X ∪ Y := by
  have hp (m : ℕ) : g ^ (m + 1) • (X ∪ Y)ᶜ ⊆ X ∪ Y :=
    ((smul_set_mono (compl_subset_compl.mpr subset_union_right)).trans
      (capPair_positive_powers g X Y hXY hX m)).trans subset_union_left
  have hm (m : ℕ) : (g⁻¹) ^ (m + 1) • (X ∪ Y)ᶜ ⊆ X ∪ Y :=
    ((smul_set_mono (compl_subset_compl.mpr subset_union_left)).trans
      (capPair_positive_powers g⁻¹ Y X hXY.symm hY m)).trans subset_union_right
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · cases m with
    | zero => exact (hn rfl).elim
    | succ m => simpa only [zpow_natCast] using hp m
  · cases m with
    | zero => exact (hn rfl).elim
    | succ m => simpa only [zpow_neg, zpow_natCast, inv_pow] using hm m

/-- Every nonzero integer power of either actual generator sends the complement
of its closed cap pair into that same pair. -/
theorem annular_four_closed_caps_zpow_gap (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hinner : 1 + r < x) (houter : x + r < E) :
    let σ0 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one)
    let σ1 := halfPlaneLineReflectionIsometry
      (HalfPlaneLine.circle 0 E (zero_lt_one.trans hE))
    let σ2 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)
    let a : Fin 2 → (ℍ ≃ᵢ ℍ) := ![σ0 * σ1, σ2 * σ0]
    let O := {z : ℍ | E ≤ ‖(z : ℂ)‖}
    let B := {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ ≤ r}
    let A : Fin 2 → Set ℍ := ![σ0 '' O ∪ O, B ∪ σ0 '' B]
    ∀ i (n : ℤ), n ≠ 0 → a i ^ n • (A i)ᶜ ⊆ A i := by
  let σ0 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one)
  let σ1 := halfPlaneLineReflectionIsometry
    (HalfPlaneLine.circle 0 E (zero_lt_one.trans hE))
  let σ2 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)
  let O := {z : ℍ | E ≤ ‖(z : ℂ)‖}
  let B := {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ ≤ r}
  have hd : Disjoint (σ0 '' O) O ∧ Disjoint (σ0 '' O) B ∧
      Disjoint (σ0 '' O) (σ0 '' B) ∧ Disjoint O B ∧
      Disjoint O (σ0 '' B) ∧ Disjoint B (σ0 '' B) :=
    annular_four_closed_caps_disjoint E r x hE hr hinner houter
  rcases hd with ⟨h00, _, _, _, _, h11⟩
  have hm : (σ0 * σ1) • Oᶜ ⊆ σ0 '' O ∧
      (σ0 * σ1)⁻¹ • (σ0 '' O)ᶜ ⊆ O ∧
      (σ2 * σ0) • (σ0 '' B)ᶜ ⊆ B ∧
      (σ2 * σ0)⁻¹ • Bᶜ ⊆ σ0 '' B :=
    annular_four_closed_caps_pingPong_mappings E r x (zero_lt_one.trans hE) hr
  rcases hm with ⟨h0, h0inv, h1, h1inv⟩
  dsimp only
  intro i n hn
  fin_cases i
  · exact capPair_zpow_gap (σ0 * σ1) (σ0 '' O) O h00 h0 h0inv n hn
  · exact capPair_zpow_gap (σ2 * σ0) B (σ0 '' B) h11 h1 h1inv n hn

end LowDimensionalTopology.Geometry.Hyperbolic
