module
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- The three source-ordered literal peripheral words in the fixed rank-two free group. -/
def pantsThreeFreeWords : Fin 3 → FreeGroup (Fin 2) :=
  ![FreeGroup.of 0, FreeGroup.of 1, (FreeGroup.of 1 * FreeGroup.of 0)⁻¹]

/-- One of the two integer exponent coordinates of the fixed rank-two free group. -/
def pantsFreeWordCoordinate (k : Fin 2) : FreeGroup (Fin 2) →* Multiplicative ℤ :=
  FreeGroup.lift fun j => Multiplicative.ofAdd (if j = k then (1 : ℤ) else 0)

/-- Each of the three literal words has no integer power presentation of exponent other than ±1. -/
theorem pantsThreeFreeWords_zpow_exponent (i : Fin 3) (a : FreeGroup (Fin 2)) (n : ℤ)
    (h : pantsThreeFreeWords i = a ^ n) : n = 1 ∨ n = -1 := by
  have hcoord (k : Fin 2) :
      (pantsFreeWordCoordinate k (pantsThreeFreeWords i)).toAdd =
        n * (pantsFreeWordCoordinate k a).toAdd := by
    have hh := congrArg
      (fun w : FreeGroup (Fin 2) => (pantsFreeWordCoordinate k w).toAdd) h
    simpa only [map_zpow, toAdd_zpow, Int.zsmul_eq_mul] using hh
  fin_cases i
  · exact Int.eq_one_or_neg_one_of_mul_eq_one
      (u := n) (v := (pantsFreeWordCoordinate 0 a).toAdd) (by
        simpa [pantsThreeFreeWords, pantsFreeWordCoordinate, FreeGroup.lift_apply_of]
          using (hcoord 0).symm)
  · exact Int.eq_one_or_neg_one_of_mul_eq_one
      (u := n) (v := (pantsFreeWordCoordinate 1 a).toAdd) (by
        simpa [pantsThreeFreeWords, pantsFreeWordCoordinate, FreeGroup.lift_apply_of]
          using (hcoord 1).symm)
  · exact Int.eq_one_or_neg_one_of_mul_eq_neg_one
      (u := n) (v := (pantsFreeWordCoordinate 0 a).toAdd) (by
        simpa [pantsThreeFreeWords, pantsFreeWordCoordinate, FreeGroup.lift_apply_of]
          using (hcoord 0).symm)

/-- Distinct source-ordered words are not conjugate to any integer power of one another. -/
theorem pantsThreeFreeWords_not_conjugate_zpow (i j : Fin 3) (hij : i ≠ j) :
    ¬ ∃ h : FreeGroup (Fin 2), ∃ n : ℤ,
      pantsThreeFreeWords i = h * pantsThreeFreeWords j ^ n * h⁻¹ := by
  rintro ⟨h, n, heq⟩
  have h0 := congrArg
    (fun w : FreeGroup (Fin 2) => (pantsFreeWordCoordinate 0 w).toAdd) heq
  have h1 := congrArg
    (fun w : FreeGroup (Fin 2) => (pantsFreeWordCoordinate 1 w).toAdd) heq
  fin_cases i <;> fin_cases j <;>
    simp [pantsThreeFreeWords, pantsFreeWordCoordinate, FreeGroup.lift_apply_of,
      map_zpow] at hij h0 h1 <;>
    linarith

end
end LowDimensionalTopology.Geometry.Hyperbolic
