/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteRotationProfiles
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteMobiusVertices
public import Mathlib.Data.Fin.Tuple.Sort
@[expose] public section
noncomputable section
open scoped BigOperators
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius

/-- The branch order attached to an actual vertex orbit is its representative's stabilizer order. -/
def mobiusVertexBranchOrder (H : Subgroup Mobius.complexMobiusGroup) (o : MobiusVertexOrbit H) : ℕ :=
  Nat.card (MulAction.stabilizer H o.out)

/-- A three-orbit vertex quotient enumerated by increasing stabilizer order. -/
def finiteMobius_three_branch_enumeration (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (hm : Nat.card (MobiusVertexOrbit H) = 3) : Fin 3 ≃ MobiusVertexOrbit H :=
  let e : Fin 3 ≃ MobiusVertexOrbit H :=
    (Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hm)).symm
  (Tuple.sort (fun i => mobiusVertexBranchOrder H (e i))).trans e

/-- The resulting actual representative stabilizer orders are monotone. -/
theorem finiteMobius_three_branch_enumeration_monotone
    (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (hm : Nat.card (MobiusVertexOrbit H) = 3) :
    Monotone (fun i => mobiusVertexBranchOrder H (finiteMobius_three_branch_enumeration H hm i)) := by
  let e : Fin 3 ≃ MobiusVertexOrbit H :=
    (Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hm)).symm
  change Monotone ((fun i : Fin 3 => mobiusVertexBranchOrder H (e i)) ∘
    Tuple.sort (fun i : Fin 3 => mobiusVertexBranchOrder H (e i)))
  exact Tuple.monotone_sort (fun i : Fin 3 => mobiusVertexBranchOrder H (e i))

/-- The actual rational Euler identity becomes the real three-branch reciprocal identity. -/
theorem finiteMobius_three_branch_reciprocal_sum
    (H : Subgroup Mobius.complexMobiusGroup) [Finite H] (e : Fin 3 ≃ MobiusVertexOrbit H) :
    (1 : ℝ) / mobiusVertexBranchOrder H (e 0) +
      1 / mobiusVertexBranchOrder H (e 1) + 1 / mobiusVertexBranchOrder H (e 2) =
      1 + 2 / Nat.card H := by
  have heuler : (∑ o : MobiusVertexOrbit H,
      (1 - (1 : ℚ) / mobiusVertexBranchOrder H o)) = 2 - 2 / (Nat.card H : ℚ) := by
    simpa only [mobiusVertexBranchOrder] using finiteMobius_vertex_euler H
  have hs := (e.sum_comp (fun o => 1 - (1 : ℚ) / mobiusVertexBranchOrder H o)).trans heuler
  simp only [Fin.sum_univ_three] at hs
  have hs' : (1 : ℚ) / mobiusVertexBranchOrder H (e 0) +
      1 / mobiusVertexBranchOrder H (e 1) + 1 / mobiusVertexBranchOrder H (e 2) =
      1 + 2 / Nat.card H := by linarith
  have hr := congrArg (fun q : ℚ => (q : ℝ)) hs'
  push_cast at hr
  exact hr

/-- Actual finite nontrivial Mobius groups with three vertex orbits have the four numerical profiles. -/
theorem finiteMobius_three_branch_profiles
    (H : Subgroup Mobius.complexMobiusGroup) [Finite H] [Nontrivial H]
    (hm : Nat.card (MobiusVertexOrbit H) = 3) :
    ∃ e : Fin 3 ≃ MobiusVertexOrbit H,
      (∀ i, 2 ≤ mobiusVertexBranchOrder H (e i)) ∧
      Monotone (fun i => mobiusVertexBranchOrder H (e i)) ∧
      let n : Fin 3 → ℕ := fun i => mobiusVertexBranchOrder H (e i)
      (Nat.card H, n 0, n 1, n 2) = (2 * n 2, 2, 2, n 2) ∨
        (Nat.card H, n 0, n 1, n 2) = (12, 2, 3, 3) ∨
        (Nat.card H, n 0, n 1, n 2) = (24, 2, 3, 4) ∨
        (Nat.card H, n 0, n 1, n 2) = (60, 2, 3, 5) := by
  let e := finiteMobius_three_branch_enumeration H hm
  have hge : ∀ i, 2 ≤ mobiusVertexBranchOrder H (e i) := fun i =>
    finiteMobius_vertex_stabilizer_card_ge_two H (e i).out
  have hmono : Monotone (fun i => mobiusVertexBranchOrder H (e i)) :=
    finiteMobius_three_branch_enumeration_monotone H hm
  refine ⟨e, hge, hmono, ?_⟩
  exact finiteRotation_branch_order_quadruples (Nat.succ_le_of_lt Finite.one_lt_card)
    (hge 0) (hmono (by decide : (0 : Fin 3) ≤ 1)) (hmono (by decide : (1 : Fin 3) ≤ 2))
    (finiteMobius_three_branch_reciprocal_sum H e)

end LowDimensionalTopology.Geometry.DiscreteGroups
