module
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Tactic.Choose

/-!
# Gluing compatible local measures.

Measures agreeing on overlaps glue uniquely over countable measurable covers. For open
covers of second countable spaces, a countable subcover gives the same construction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Topology

namespace LowDimensionalTopology.Geometry.Auxiliary.Measure

/-- Countably many compatible local measures are assembled on the disjointification of
their measurable domains. -/
def countableCompatibleMeasure {X : Type*} [MeasurableSpace X]
    (U : ℕ → Set X) (μ : ℕ → Measure X) : Measure X :=
  Measure.sum (fun n => (μ n).restrict (disjointed U n))

theorem countableCompatibleMeasure_restrict {X : Type*} [MeasurableSpace X]
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (hcover : ⋃ n, U n = Set.univ)
    (μ : ℕ → Measure X)
    (hcompat : ∀ i j, (μ i).restrict (U i ∩ U j) = (μ j).restrict (U i ∩ U j)) (i : ℕ) :
    (countableCompatibleMeasure U μ).restrict (U i) = (μ i).restrict (U i) := by
  have hD : ∀ n, MeasurableSet (disjointed U n) := MeasurableSet.disjointed hU
  rw [countableCompatibleMeasure, Measure.restrict_sum_of_countable]
  have hterm (n : ℕ) : ((μ n).restrict (disjointed U n)).restrict (U i) =
      ((μ i).restrict (U i)).restrict (disjointed U n) := by
    rw [Measure.restrict_restrict (hU i), Measure.restrict_restrict (hD n)]
    have he := Measure.restrict_congr_mono
      (show U i ∩ disjointed U n ⊆ U n ∩ U i from
        fun _ hx => ⟨(disjointed_subset U n) hx.2, hx.1⟩) (hcompat n i)
    simpa only [Set.inter_comm] using he
  simp_rw [hterm]
  rw [← Measure.restrict_iUnion (disjoint_disjointed U) hD,
    iUnion_disjointed, hcover, Measure.restrict_univ]

/-- A countable measurable cover and exact overlap agreement determine a unique global
measure; no finiteness or sigma-finiteness assumptions are introduced. -/
theorem existsUnique_measure_of_countable_compatible_cover {X : Type*} [MeasurableSpace X]
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (hcover : ⋃ n, U n = Set.univ)
    (μ : ℕ → Measure X)
    (hcompat : ∀ i j, (μ i).restrict (U i ∩ U j) = (μ j).restrict (U i ∩ U j)) :
    ∃! ν : Measure X, ∀ i, ν.restrict (U i) = (μ i).restrict (U i) := by
  refine ⟨countableCompatibleMeasure U μ,
    countableCompatibleMeasure_restrict U hU hcover μ hcompat, ?_⟩
  intro ν hν
  have he := Measure.restrict_iUnion_congr.mpr (fun i =>
    (hν i).trans (countableCompatibleMeasure_restrict U hU hcover μ hcompat i).symm)
  simpa only [hcover, Measure.restrict_univ] using he

/-- Equality of measure restrictions is local on a second countable topological space. -/
theorem measure_restrict_eq_of_locally_eq {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [SecondCountableTopology X] (μ ν : Measure X) (S : Set X)
    (hloc : ∀ x ∈ S, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ S ∧ μ.restrict U = ν.restrict U) :
    μ.restrict S = ν.restrict S := by
  classical
  by_cases hS : S.Nonempty
  · let : Nonempty S := hS.to_subtype
    choose U hUo hxU hUS hUeq using (fun x : S => hloc x.val x.property)
    have hcov : S ⊆ ⋃ x : S, U x := fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
    obtain ⟨c, hc⟩ := (HereditarilyLindelofSpace.isLindelof S).indexed_countable_subcover U hUo hcov
    have heU : ⋃ n, U (c n) = S := Set.Subset.antisymm (Set.iUnion_subset fun n => hUS (c n)) hc
    have he := Measure.restrict_iUnion_congr.mpr (fun n => hUeq (c n))
    rwa [heU] at he
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    simp [he]

/-- Compatible local measures on any open cover of a second countable space glue uniquely;
only a countable subcover is used in the construction. -/
theorem existsUnique_measure_of_secondCountable_open_cover {X ι : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [Nonempty ι]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ)
    (μ : ι → Measure X)
    (hcompat : ∀ i j, (μ i).restrict (U i ∩ U j) = (μ j).restrict (U i ∩ U j)) :
    ∃! ν : Measure X, ∀ i, ν.restrict (U i) = (μ i).restrict (U i) := by
  classical
  obtain ⟨c, hc⟩ := isLindelof_univ.indexed_countable_subcover U hU (hcover ▸ Set.Subset.rfl)
  have hcov : ⋃ n, U (c n) = Set.univ := Set.eq_univ_of_univ_subset hc
  obtain ⟨ν, hν, hνu⟩ := existsUnique_measure_of_countable_compatible_cover
    (fun n => U (c n)) (fun n => (hU (c n)).measurableSet) hcov
    (fun n => μ (c n)) (fun n m => hcompat (c n) (c m))
  have hall (i : ι) : ν.restrict (U i) = (μ i).restrict (U i) := by
    have hun : ⋃ n, U (c n) ∩ U i = U i := by rw [← Set.iUnion_inter, hcov, Set.univ_inter]
    have he := Measure.restrict_iUnion_congr.mpr (fun n =>
      (Measure.restrict_congr_mono Set.inter_subset_left (hν n)).trans (hcompat (c n) i))
    rwa [hun] at he
  refine ⟨ν, hall, ?_⟩
  intro ξ hξ
  exact hνu ξ (fun n => hξ (c n))

end LowDimensionalTopology.Geometry.Auxiliary.Measure
