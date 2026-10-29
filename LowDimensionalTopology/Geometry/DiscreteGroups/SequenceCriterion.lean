module

public import LowDimensionalTopology.Geometry.Mobius.Topology
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Discreteness and convergent sequences of distinct group elements

The limit is allowed in the entire ambient group. Thus the forward implication
uses closedness of discrete subgroups rather than assuming that the limit is
already a subgroup element. For the converse, a nonstationary sequence tending
to the identity yields an injective convergent sequence by enumerating an
infinite range and selecting its actual indices.
-/

@[expose] public section
noncomputable section

open Filter Topology Set

namespace LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T1Space G] [FirstCountableTopology G]

/-- A subgroup is discrete exactly when no injective sequence in it converges
to any point of the ambient group. -/
theorem discrete_iff_no_injective_convergent_sequence (K : Subgroup G) :
    DiscreteTopology K ↔ ∀ u : ℕ → K, Function.Injective u →
      ∀ x : G, ¬ Tendsto (fun n => (u n : G)) atTop (𝓝 x) := by
  constructor
  · intro hK u hu x hlim
    let := hK
    obtain ⟨N, hN⟩ := eventually_atTop.mp (discrete_sequence_eventually_eq K u x hlim)
    have heq : u N = u (N + 1) := Subtype.ext
      ((hN N le_rfl).trans (hN (N + 1) (Nat.le_succ N)).symm)
    exact (Nat.ne_of_lt (Nat.lt_succ_self N)) (hu heq)
  · intro h
    apply (discrete_iff_identity_sequences K).2
    intro u hu
    by_contra hstationary
    have hfreq : ∃ᶠ n in atTop, u n ≠ 1 := by
      simpa only [Filter.Frequently, not_not] using hstationary
    obtain ⟨φ, hφ, hne⟩ := extraction_of_frequently_atTop hfreq
    let v : ℕ → K := u ∘ φ
    have hv : Tendsto v atTop (𝓝 (1 : K)) :=
      (Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr hu).comp hφ.tendsto_atTop
    have hinfinite : (range v).Infinite := by
      intro hfinite
      have hmem : (1 : K) ∈ range v := hfinite.isClosed.mem_of_tendsto hv
        (Eventually.of_forall fun n => mem_range_self n)
      obtain ⟨n, hn⟩ := hmem
      exact hne n hn
    let e : ℕ ↪ range v := hinfinite.natEmbedding (range v)
    let w : ℕ → K := fun n => (e n).val
    have hw : Function.Injective w := Subtype.val_injective.comp e.injective
    choose ψ hψ using fun n => (e n).property
    have hψinjective : Function.Injective ψ := by
      intro i j hij
      apply hw
      change (e i).val = (e j).val
      rw [← hψ i, ← hψ j, hij]
    have heq : v ∘ ψ = w := funext hψ
    have hwlim : Tendsto w atTop (𝓝 (1 : K)) := by
      have hlim := hv.comp hψinjective.nat_tendsto_atTop
      rwa [heq] at hlim
    exact h w hw (1 : G) ((continuous_subtype_val.tendsto (1 : K)).comp hwlim)

end LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups

namespace LowDimensionalTopology.Geometry.Mobius

/-- The criterion applies to the actual Mobius topology, hence in particular
to half-plane automorphism subgroups with their induced topology. -/
theorem mobiusSubgroup_discrete_iff_distinct_sequences
    (K : Subgroup complexMobiusGroup) :
    DiscreteTopology K ↔ ∀ u : ℕ → K, Function.Injective u →
      ∀ x : complexMobiusGroup, ¬ Tendsto (fun n => (u n : complexMobiusGroup)) atTop (𝓝 x) :=
  DiscreteGroups.MatrixGroups.discrete_iff_no_injective_convergent_sequence K

end LowDimensionalTopology.Geometry.Mobius
