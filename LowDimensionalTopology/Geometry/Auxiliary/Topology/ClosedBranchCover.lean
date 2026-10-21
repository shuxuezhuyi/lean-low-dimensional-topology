module
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.CoveringFiberCardinality

/-!
# The closed branch locus of a finite open map.

A continuous open map from a compact Hausdorff space, with finite fibers and local
homeomorphisms over dense regular values, is a covering away from its closed branch
locus. A constant fiber cardinality on those regular values extends to this complement.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology

namespace LowDimensionalTopology.Geometry.Auxiliary.Topology

set_option backward.isDefEq.respectTransparency false in
/-- For a compact finite open map, the actual failure-of-local-
homeomorphism values form a closed nowhere-dense branch locus. The map is
a genuine covering of its entire complement, with the same degree already
proved on the dense regular values. Both branch sets are nowhere dense. -/
theorem compact_finite_open_map_closed_branch_cover
    {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [T2Space Y]
    (f:X→Y) (hf:Continuous f) (ho:IsOpenMap f)
    (hfin:∀y:Y,(f ⁻¹' {y}).Finite) (R:Set Y) (hR:Dense R)
    (hlocal:IsLocalHomeomorphOn f (f ⁻¹' R))
    (k:ℕ) (hk:∀y∈R,Nat.card (f ⁻¹' {y})=k) :
    ∃B:Set Y,IsClosed B ∧Dense Bᶜ ∧
      IsClosed (f ⁻¹' B) ∧Dense (f ⁻¹' B)ᶜ ∧
      R⊆Bᶜ ∧IsCoveringMapOn f Bᶜ ∧
      (∀y∈Bᶜ,Nat.card (f ⁻¹' {y})=k) ∧
      B=f '' {x:X|¬∃e:OpenPartialHomeomorph X Y,x∈e.source ∧f=e} ∧
      IsClosed {x:X|¬∃e:OpenPartialHomeomorph X Y,x∈e.source ∧f=e} ∧
      Dense {x:X|∃e:OpenPartialHomeomorph X Y,x∈e.source ∧f=e} := by
  let U:Set X:={x|∃e:OpenPartialHomeomorph X Y,x∈e.source ∧f=e}
  have hU:IsOpen U:=by
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨e,hxe,he⟩
    exact mem_of_superset (e.open_source.mem_nhds hxe) (fun z hz=>⟨e,hz,he⟩)
  let B:=f '' Uᶜ
  have hB:IsClosed B:=hf.isClosedMap _ hU.isClosed_compl
  have hsub:R⊆Bᶜ:=by
    intro y hy
    rintro ⟨x,hx,hxy⟩
    exact hx (hlocal x (show f x∈R from hxy.symm ▸ hy))
  have hd:Dense Bᶜ:=hR.mono hsub
  have hpre:Dense (f ⁻¹' B)ᶜ:=by
    apply dense_iff_inter_open.mpr
    intro V hV hVne
    obtain ⟨y,⟨x,hx,rfl⟩,hy⟩:=hd.inter_open_nonempty (f '' V)
      (ho V hV) (hVne.image f)
    exact ⟨x,hx,hy⟩
  have hc:IsCoveringMapOn f Bᶜ:=by
    apply hf.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn (fun y _=>hfin y)
    intro x hx
    by_contra hn
    exact hx ⟨x,hn,rfl⟩
  have hDenseU:Dense U:=hpre.mono (by
    intro x hx
    by_contra hn
    exact hx ⟨x,hn,rfl⟩)
  exact ⟨B,hB,hd,hB.preimage hf,hpre,hsub,hc,
    coveringOn_fiber_natCard_of_dense hc hR k hk,rfl,hU.isClosed_compl,hDenseU⟩

end LowDimensionalTopology.Geometry.Auxiliary.Topology
