module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.LocallyFiniteFundamentalDomains
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Tactic.Ext
@[expose] public section
noncomputable section
open Set Topology
open scoped Pointwise OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- A connected space tiled locally finitely by translates of a nonempty closed set is generated
by the elements whose closed tiles intersect the original tile. -/
theorem connected_closed_tiles_generate {G X : Type*} [Group G] [TopologicalSpace X]
    [ConnectedSpace X] [MulAction G X] [ContinuousConstSMul G X]
    (K : Set X) (hK : IsClosed K) (hnK : K.Nonempty)
    (hlf : LocallyFinite (fun g : G => g • K)) (hcov : (⋃ g : G, g • K) = univ) :
    Subgroup.closure {g : G | (K ∩ g • K).Nonempty} = ⊤ := by
  classical
  let S : Set G := {g : G | (K ∩ g • K).Nonempty}
  let L : Subgroup G := Subgroup.closure S
  let U : Set X := ⋃ g : L, g.val • K
  let V : Set X := ⋃ g : {g : G // g ∉ L}, g.val • K
  have hUc : IsClosed U :=
    (hlf.comp_injective (Subtype.val_injective (p := fun g => g ∈ L))).isClosed_iUnion
      (fun g => (Homeomorph.smul g.val).isClosedMap K hK)
  have hVc : IsClosed V :=
    (hlf.comp_injective (Subtype.val_injective (p := fun g => g ∉ L))).isClosed_iUnion
      (fun g => (Homeomorph.smul g.val).isClosedMap K hK)
  have hd : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro x hxU hxV
    obtain ⟨g, u, hu, hgu⟩ := mem_iUnion.mp hxU
    obtain ⟨h, v, hv, hhv⟩ := mem_iUnion.mp hxV
    change g.val • u = x at hgu
    change h.val • v = x at hhv
    have hs : g.val⁻¹ * h.val ∈ S := by
      refine ⟨u, hu, v, hv, ?_⟩
      change (g.val⁻¹ * h.val) • v = u
      rw [mul_smul, hhv, ← hgu, inv_smul_smul]
    have hh : h.val ∈ L := by
      have hm := L.mul_mem g.property (Subgroup.subset_closure hs)
      simpa only [mul_inv_cancel_left] using hm
    exact h.property hh
  have huv : U ∪ V = univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ g : G, g • K := by rw [hcov]; trivial
    obtain ⟨g, hg⟩ := mem_iUnion.mp hx
    by_cases hgl : g ∈ L
    · exact Or.inl (mem_iUnion.mpr ⟨⟨g, hgl⟩, hg⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨g, hgl⟩, hg⟩)
  have he : U = Vᶜ := by
    ext x
    exact ⟨fun hx hv => Set.disjoint_left.mp hd hx hv,
      fun hx => (show x ∈ U ∪ V by rw [huv]; trivial).resolve_right hx⟩
  have hUo : IsOpen U := by rw [he]; exact hVc.isOpen_compl
  obtain ⟨u, hu⟩ := hnK
  have huU : u ∈ U := mem_iUnion.mpr ⟨⟨1, L.one_mem⟩, u, hu, by simp⟩
  rcases isClopen_iff.mp (show IsClopen U from ⟨hUc, hUo⟩) with hempty | hall
  · simp only [hempty, mem_empty_iff_false] at huU
  · apply top_unique
    intro g _hg
    by_contra hgn
    have hgU : g • u ∈ U := by rw [hall]; trivial
    have hgV : g • u ∈ V := mem_iUnion.mpr ⟨⟨g, hgn⟩, u, hu, rfl⟩
    exact Set.disjoint_left.mp hd hgU hgV

/-- Elements whose translated closed tile meets the closed fundamental domain. -/
def fuchsianDomainAdjacentElements {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) : Set H := {g : H | (closure D ∩ fuchsianDomainTile P D g).Nonempty}

/-- genuine intersecting-closed-tile elements generate the original Fuchsian group. -/
theorem adjacent_elements_generate_of_locallyFinite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsLocallyFiniteFuchsianDomain P D) :
    Subgroup.closure (fuchsianDomainAdjacentElements P D) = ⊤ := by
  apply connected_closed_tiles_generate (closure D) isClosed_closure
    ((isFuchsianFundamentalDomain_iff P D).mp hD.fundamental).2.1.nonempty.closure hD.locallyFinite
  exact hD.fundamental.closure_cover

end LowDimensionalTopology.Geometry.Fuchsian
