/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import Mathlib.Topology.Connected.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LowDimensionalTopology.Geometry.Auxiliary.Topology
open Set

/-- A connected set covered by finitely many closed sets, whose traces on it are pairwise disjoint, lies in one of them. -/
theorem isPreconnected_subset_one_finite_closed_cover {X ι:Type*} [TopologicalSpace X] [Finite ι]
    (s:Set X) (hs:IsPreconnected s) (hne:s.Nonempty) (F:ι→Set X)
    (hclosed:∀i,IsClosed (F i)) (hcover:s⊆⋃i,F i)
    (hdisjoint:∀i j,i≠j→∀x∈s,x∈F i→x∉F j) : ∃i,s⊆F i := by
  classical
  obtain ⟨p,hp⟩:=hne
  obtain ⟨i,hpi⟩:=mem_iUnion.mp (hcover hp)
  refine ⟨i,?_⟩
  intro x hx
  by_contra hxi
  let U:=⋃ (j:ι) (_:j≠i),F j
  have hU:IsClosed U:=isClosed_iUnion_of_finite (fun j=>isClosed_iUnion_of_finite (fun _=>hclosed j))
  have hxU:x∈U:=by
    obtain ⟨j,hj⟩:=mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨fun he=>hxi (he ▸ hj),hj⟩⟩
  have hcover':s⊆F i∪U:=by
    intro y hy
    obtain ⟨j,hj⟩:=mem_iUnion.mp (hcover hy)
    by_cases hji:j=i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hji,hj⟩⟩)
  obtain ⟨y,hy,hyF,hyU⟩:=isPreconnected_closed_iff.mp hs (F i) U (hclosed i) hU hcover'
    ⟨p,hp,hpi⟩ ⟨x,hx,hxU⟩
  obtain ⟨j,hj⟩:=mem_iUnion.mp hyU
  obtain ⟨hji,hyj⟩:=mem_iUnion.mp hj
  exact hdisjoint i j (Ne.symm hji) y hy hyF hyj
end LowDimensionalTopology.Geometry.Auxiliary.Topology
