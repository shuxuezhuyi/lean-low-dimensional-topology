/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Integer-lattice basis arguments adapted from Mathlib (Xavier Roblot and contributors).
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
@[expose] public section
noncomputable section
open Set Submodule Module
namespace LowDimensionalTopology.Geometry.Euclidean

/-- The integer rank of a discrete subgroup cannot exceed the real dimension of its ambient Euclidean space. -/
theorem discrete_submodule_finrank_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    Module.finrank ℤ L ≤ Module.finrank ℝ E := by
  have hL : Submodule.span ℤ (L : Set E) = L := Submodule.span_eq L
  have hdisc : DiscreteTopology (Submodule.span ℤ (L : Set E)) := hL.symm ▸ inferInstance
  have hrank := Real.finrank_eq_int_finrank_of_discrete hdisc
  have heq : Module.finrank ℝ (Submodule.span ℝ (L : Set E)) = Module.finrank ℤ L := by
    change Module.finrank ℝ (Submodule.span ℝ (L : Set E)) =
      Module.finrank ℤ (Submodule.span ℤ (L : Set E)) at hrank
    rw [hL] at hrank
    exact hrank
  rw [← heq]
  exact Submodule.finrank_le _

/-- In the complex plane, the integer rank of a discrete subgroup is at most two. -/
theorem discrete_complex_submodule_finrank_le_two (L : Submodule ℤ ℂ) [DiscreteTopology L] :
    Module.finrank ℤ L ≤ 2 := by
  simpa only [Complex.finrank_real_complex] using discrete_submodule_finrank_le L

/-- An integer basis of a discrete real-Euclidean subgroup is real-linearly independent in the ambient space. -/
theorem discrete_submodule_basis_real_linearIndependent
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] (L : Submodule ℤ E) [DiscreteTopology L] (b : Basis ι ℤ L) :
    LinearIndependent ℝ (fun i => (b i : E)) := by
  let v : ι → E := fun i => (b i : E)
  have hspan : Submodule.span ℤ (Set.range v) = L := by
    convert congrArg (Submodule.map L.subtype) b.span_eq using 1
    · rw [Submodule.map_span, ← Set.range_comp]
      rfl
    · exact (Submodule.map_subtype_top L).symm
  have hdisc : DiscreteTopology (Submodule.span ℤ (Set.range v)) := hspan.symm ▸ (inferInstance : DiscreteTopology L)
  have hrank := Real.finrank_eq_int_finrank_of_discrete hdisc
  have hi : LinearIndependent ℤ v := b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  rw [linearIndependent_iff_card_eq_finrank_span] at hi ⊢
  change Fintype.card ι = Set.finrank ℝ (Set.range v)
  rw [hrank]
  exact hi

/-- Every discrete subgroup of the complex plane has an integer basis of zero, one, or two
real-linearly independent complex vectors. -/
theorem discrete_complex_submodule_basis (L : Submodule ℤ ℂ) [DiscreteTopology L] :
    ∃ n : ℕ, n ≤ 2 ∧ ∃ v : Fin n → ℂ,
      LinearIndependent ℝ v ∧ L = Submodule.span ℤ (Set.range v) := by
  let b := Module.finBasis ℤ L
  refine ⟨Module.finrank ℤ L, discrete_complex_submodule_finrank_le_two L,
    (fun i => (b i : ℂ)), discrete_submodule_basis_real_linearIndependent L b, ?_⟩
  symm
  convert congrArg (Submodule.map L.subtype) b.span_eq using 1
  · rw [Submodule.map_span, ← Set.range_comp]
    rfl
  · exact (Submodule.map_subtype_top L).symm

end LowDimensionalTopology.Geometry.Euclidean
