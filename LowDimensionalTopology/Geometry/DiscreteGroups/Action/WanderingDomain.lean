/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
@[expose] public section
set_option autoImplicit false
open Set
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.DiscreteGroups
universe u v

/-- A genuine nonempty wandering open domain makes a continuous group action discrete. -/
theorem discreteTopology_of_wandering_open
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {X : Type v} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    (U : Set X) (hU : IsOpen U) (hne : U.Nonempty)
    (hdis : ∀g : G,g≠1→Disjoint (g • U) U) : DiscreteTopology G := by
  classical
  obtain ⟨x,hx⟩:=hne
  have hc : Continuous (fun g : G=>g • x):=continuous_id.smul continuous_const
  have he : (fun g : G=>g • x) ⁻¹' U=({1}:Set G):=by
    ext g
    constructor
    · intro hgx
      apply Set.mem_singleton_iff.mpr
      by_contra hg
      have hleft : g • x∈g • U:=⟨x,hx,rfl⟩
      exact Set.disjoint_left.mp (hdis g hg) hleft hgx
    · rintro rfl
      change (1:G) • x∈U
      rw [one_smul]
      exact hx
  apply discreteTopology_of_isOpen_singleton_one
  rw [←he]
  exact hU.preimage hc

end LowDimensionalTopology.Geometry.DiscreteGroups
