module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularFourCapMappings
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularFourClosedCaps
public import Mathlib.GroupTheory.CoprodI
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane Pointwise

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The two literal annular reflection products freely generate a rank-two subgroup
of the original native half-plane isometry group. -/
theorem annular_reflection_products_free (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hinner : 1 + r < x) (houter : x + r < E) :
    let σ0 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one)
    let σ1 := halfPlaneLineReflectionIsometry
      (HalfPlaneLine.circle 0 E (zero_lt_one.trans hE))
    let σ2 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)
    Function.Injective
      (FreeGroup.lift (![σ0 * σ1, σ2 * σ0] : Fin 2 → (ℍ ≃ᵢ ℍ))) := by
  have hE0 : 0 < E := zero_lt_one.trans hE
  let σ0 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one)
  let σ1 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 E hE0)
  let σ2 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)
  let O := {z : ℍ | E ≤ ‖(z : ℂ)‖}
  let B := {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ ≤ r}
  let a : Fin 2 → (ℍ ≃ᵢ ℍ) := ![σ0 * σ1, σ2 * σ0]
  let X : Fin 2 → Set ℍ := ![σ0 '' O, B]
  let Y : Fin 2 → Set ℍ := ![O, σ0 '' B]
  change Function.Injective (FreeGroup.lift a)
  have hOn : O.Nonempty := by
    refine ⟨⟨(E : ℂ) * Complex.I, by simpa using hE0⟩, ?_⟩
    change E ≤ ‖(E : ℂ) * Complex.I‖
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE0,
      Complex.norm_I, mul_one, le_refl]
  have hBn : B.Nonempty := by
    refine ⟨⟨(x : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I,
      by simpa using (half_pos hr)⟩, ?_⟩
    change ‖((x : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I) - (x : ℂ)‖ ≤ r
    simpa only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hr), Complex.norm_I, mul_one] using
      (half_le_self_iff.mpr hr.le : r / 2 ≤ r)
  have hd : Disjoint (σ0 '' O) O ∧ Disjoint (σ0 '' O) B ∧
      Disjoint (σ0 '' O) (σ0 '' B) ∧ Disjoint O B ∧
      Disjoint O (σ0 '' B) ∧ Disjoint B (σ0 '' B) :=
    annular_four_closed_caps_disjoint E r x hE hr hinner houter
  rcases hd with ⟨h00, hXX, h01, h10, hYY, h11⟩
  have hm : (σ0 * σ1) • Oᶜ ⊆ σ0 '' O ∧
      (σ0 * σ1)⁻¹ • (σ0 '' O)ᶜ ⊆ O ∧
      (σ2 * σ0) • (σ0 '' B)ᶜ ⊆ B ∧
      (σ2 * σ0)⁻¹ • Bᶜ ⊆ σ0 '' B :=
    annular_four_closed_caps_pingPong_mappings E r x hE0 hr
  rcases hm with ⟨hγ1, hγ1inv, hγ2, hγ2inv⟩
  refine FreeGroup.injective_lift_of_ping_pong a X Y ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact hOn.image σ0
    · exact hBn
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hXX
    · exact hXX.symm
    · exact (hij rfl).elim
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hYY
    · exact hYY.symm
    · exact (hij rfl).elim
  · intro i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact h10.symm
    · exact h11
  · intro i
    fin_cases i
    · exact hγ1
    · exact hγ2
  · intro i
    fin_cases i
    · exact hγ1inv
    · exact hγ2inv

end LowDimensionalTopology.Geometry.Hyperbolic
