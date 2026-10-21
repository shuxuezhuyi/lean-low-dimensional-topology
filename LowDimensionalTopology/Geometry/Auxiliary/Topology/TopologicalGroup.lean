/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Logic.Function.Iterate

/-!
Topological groups, their translations and quotients, and the
conjugation and commutator iteration observations.
-/

public section

open Filter Topology

universe u v

namespace LowDimensionalTopology.Geometry.Auxiliary.Topology

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- The topological-group property. -/
abbrev topologicalGroup [TopologicalSpace G] : Prop := IsTopologicalGroup G

/-- An isomorphism of topological groups. -/
abbrev topologicalGroupIsomorphism [TopologicalSpace G] [TopologicalSpace H] :=
  ContinuousMulEquiv G H

/-- A discrete group has the discrete topology. -/
abbrev discreteTopologicalGroup [TopologicalSpace G] : Prop := DiscreteTopology G

section Topological

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- right translation as a homeomorphism. -/
@[expose] def rightTranslationHomeomorph (y : G) : G ≃ₜ G := Homeomorph.mulRight y

/-- The homeomorphism is the stated right translation. -/
theorem rightTranslationHomeomorph_apply (x y : G) :
    rightTranslationHomeomorph y x = x * y := rfl

/-- left translation as a homeomorphism. -/
@[expose] def leftTranslationHomeomorph (y : G) : G ≃ₜ G := Homeomorph.mulLeft y

/-- The homeomorphism is the stated left translation. -/
theorem leftTranslationHomeomorph_apply (x y : G) :
    leftTranslationHomeomorph y x = y * x := rfl

/-- one open singleton makes the group discrete. -/
theorem discreteTopology_of_isOpen_singleton {g : G} (hg : IsOpen ({g} : Set G)) : DiscreteTopology G :=
  (MulAction.IsPretransitive.discreteTopology_iff G g).mpr hg

/-- Every singleton is then open. -/
theorem isOpen_singleton_of_isOpen_singleton {g : G} (hg : IsOpen ({g} : Set G)) (y : G) :
    IsOpen ({y} : Set G) := by
  let := discreteTopology_of_isOpen_singleton hg
  exact isOpen_discrete _

/-- With the quotient group and quotient topology. -/
theorem quotient_isTopologicalGroup (N : Subgroup G) [N.Normal] : IsTopologicalGroup (G ⧸ N) :=
  inferInstance

end Topological

/-- The conjugation map with fixed second argument. -/
def conjugationMap (a : G) (x : G) : G := x * a * x⁻¹

/-- The commutator map with fixed second argument. -/
def commutatorMap (a : G) (x : G) : G := x * a * x⁻¹ * a⁻¹

/-- The conjugation map has precisely one fixed point. -/
theorem conjugationMap_fixedPoint_iff (a x : G) : conjugationMap a x = x ↔ x = a := by
  constructor
  · intro h
    have h' := congrArg (fun y => x⁻¹ * y * x) h
    simpa [conjugationMap, mul_assoc] using h'.symm
  · rintro rfl
    simp [conjugationMap]

/-- The relation of the two iterates, indexed positively. -/
theorem conjugationMap_iterate_eq (a x : G) (n : ℕ) :
    (conjugationMap a)^[n + 1] x = (commutatorMap a)^[n + 1] x * a := by
  induction n with
  | zero => simp [conjugationMap, commutatorMap, mul_assoc]
  | succ n ih =>
    rw [Function.iterate_succ_apply' (conjugationMap a) (n + 1) x,
      Function.iterate_succ_apply' (commutatorMap a) (n + 1) x, ih]
    simp [conjugationMap, commutatorMap, mul_assoc]

/-- The two sequences of iterates agree after right translation. -/
theorem conjugationMap_iterates_eventuallyEq (a x : G) :
    (fun n : ℕ => (conjugationMap a)^[n] x) =ᶠ[atTop]
      (fun n : ℕ => (commutatorMap a)^[n] x * a) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact conjugationMap_iterate_eq a x k

section TopologicalIterates

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- convergence of commutator iterates and conjugation iterates. -/
theorem commutatorMap_tendsto_iff (a x : G) :
    Tendsto (fun n : ℕ => (commutatorMap a)^[n] x) atTop (𝓝 1) ↔
      Tendsto (fun n : ℕ => (conjugationMap a)^[n] x) atTop (𝓝 a) := by
  have heq := conjugationMap_iterates_eventuallyEq a x
  have hmul := Filter.tendsto_mul_const_iff (c := (1 : G))
    (f := fun n : ℕ => (commutatorMap a)^[n] x) (l := atTop) a
  simpa only [one_mul] using hmul.symm.trans (tendsto_congr' heq).symm

omit [IsTopologicalGroup G] in
/-- In a discrete group convergent iterates reach the fixed point. -/
theorem conjugationMap_iterate_eq_of_tendsto [DiscreteTopology G] (a x : G)
    (h : Tendsto (fun n : ℕ => (conjugationMap a)^[n] x) atTop (𝓝 a)) :
    ∃ n : ℕ, (conjugationMap a)^[n] x = a := by
  have ha : ({a} : Set G) ∈ 𝓝 a := (isOpen_discrete _).mem_nhds (by simp)
  exact (h.eventually ha).exists

end TopologicalIterates

end LowDimensionalTopology.Geometry.Auxiliary.Topology
