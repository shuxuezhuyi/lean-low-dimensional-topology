/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareDevelopmentTopology
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Topology.Connected.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
namespace LowDimensionalTopology.Geometry.Polygon

/-- A connected actual polygon interior and its actual boundary-closure condition
already make the full original polygon carrier connected. -/
theorem PoincarePolygon.carrier_isConnected {X : Type*} [TopologicalSpace X]
    (P : PoincarePolygon X) (hP : IsConnected P.interior)
    (hcl : P.carrier⊆closure P.interior) : IsConnected P.carrier :=
  hP.subset_closure P.interior_subset_carrier hcl

namespace PoincareSidePairing
universe u v
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X]
variable [TopologicalSpace X] {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)
local instance connectedDevelopmentGeneratedTopology : TopologicalSpace S.Generated := ⊥

/-- The literal image of one whole indexed polygon copy in the genuine quotient. -/
def developmentCopy (g : S.Generated) : Set S.Development :=
  range (fun p : P.Point=>S.project (g,p))

/-- Each actual polygon-copy image is connected in the genuine quotient topology. -/
theorem developmentCopy_isConnected (hP : IsConnected P.carrier) (g : S.Generated) :
    IsConnected (S.developmentCopy g) := by
  have : ConnectedSpace P.Point:=isConnected_iff_connectedSpace.mp hP
  apply isConnected_range
  exact S.continuous_project.comp (continuous_const.prodMk continuous_id)

omit [TopologicalSpace X] in
/-- A genuine nonempty side makes neighboring generated copies intersect through
exactly the original side identification; no ambient tiling property is used. -/
theorem developmentCopy_generator_inter (g : S.Generated) (s : P.Side) :
    (S.developmentCopy g∩S.developmentCopy (g*S.generator s)).Nonempty := by
  obtain ⟨x,hx⟩:=P.side_nonempty s.val s.property
  let p : P.Point:=⟨x,P.side_subset_carrier s hx⟩
  have hy : S.generator s • x∈(S.paired s).val := by
    rw [←S.generator_side_image s]
    exact ⟨x,hx,rfl⟩
  let q : P.Point:=⟨S.generator s • x,P.side_subset_carrier (S.paired s) hy⟩
  have he : S.project (g*S.generator s,p)=S.project (g,q) := by
    apply (S.project_eq_iff _ _).mpr
    exact Relation.EqvGen.rel _ _ (Or.inr ⟨s,hx,rfl,rfl⟩)
  refine ⟨S.project (g,q),⟨q,rfl⟩,p,he⟩

/-- Connectedness propagates across every actual side-pairing generator. -/
theorem developmentCopy_generator_subset_component (hP : IsConnected P.carrier)
    (base : S.Development) (g : S.Generated) (s : P.Side)
    (hg : S.developmentCopy g⊆connectedComponent base) :
    S.developmentCopy (g*S.generator s)⊆connectedComponent base := by
  obtain ⟨q,hq,hq'⟩:=S.developmentCopy_generator_inter g s
  have hqc:=hg hq
  have hc:=(S.developmentCopy_isConnected hP (g*S.generator s)).subset_connectedComponent hq'
  rw [←connectedComponent_eq hqc] at hc
  exact hc

/-- The actual side-gluing development is connected whenever the original full
polygon is connected. The proof propagates through all true generated words,
including inverse generators via the original paired-side involution. -/
theorem development_connectedSpace (hP : IsConnected P.carrier) : ConnectedSpace S.Development := by
  classical
  obtain ⟨x,hx⟩:=P.interior_nonempty
  let p₀ : P.Point:=⟨x,P.interior_subset_carrier hx⟩
  let base:=S.project (1,p₀)
  have hbase : S.developmentCopy 1⊆connectedComponent base :=
    (S.developmentCopy_isConnected hP 1).subset_connectedComponent ⟨p₀,rfl⟩
  have hall (g : Γ) (hg : g∈S.Generated) :
      S.developmentCopy ⟨g,hg⟩⊆connectedComponent base := by
    induction hg using Subgroup.closure_induction_right with
    | one=>exact hbase
    | @mul_right g hg k hk ih=>
      obtain ⟨s,rfl⟩:=hk
      exact S.developmentCopy_generator_subset_component hP base ⟨g,hg⟩ s ih
    | @mul_inv_cancel g hg k hk ih=>
      obtain ⟨s,rfl⟩:=hk
      have hs:=S.developmentCopy_generator_subset_component hP base ⟨g,hg⟩ (S.paired s) ih
      rw [S.generator_paired] at hs
      convert hs using 1
      congr 1
  apply connectedSpace_iff_connectedComponent.mpr
  refine ⟨base,eq_univ_of_forall ?_⟩
  intro q
  obtain ⟨a,rfl⟩:=Quotient.exists_rep q
  exact hall a.1.val a.1.property ⟨a.2,rfl⟩

/-- The source's connected-interior and closure assumptions imply connectedness
of the genuine development, without inserting connectedness as a hypothesis. -/
theorem development_connectedSpace_of_interior (hP : IsConnected P.interior)
    (hcl : P.carrier⊆closure P.interior) : ConnectedSpace S.Development :=
  S.development_connectedSpace (P.carrier_isConnected hP hcl)

end PoincareSidePairing
end LowDimensionalTopology.Geometry.Polygon
