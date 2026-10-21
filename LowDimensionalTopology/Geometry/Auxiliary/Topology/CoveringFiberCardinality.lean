/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Covering.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- A genuine evenly covered neighborhood identifies the actual fibers, so
its actual fiber cardinality is constant on one genuine open neighborhood. -/
theorem evenlyCovered_fiber_natCard_neighborhood
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E→X} {x : X} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) :
    ∃U : Set X,IsOpen U ∧x∈U ∧∀y∈U,Nat.card (f ⁻¹' {y})=Nat.card I := by
  obtain ⟨hI,U,hx,hU,hfU,H,hH⟩:=h
  refine ⟨U,hU,hx,?_⟩
  intro y hy
  have hh : IsEvenlyCovered f y I:=⟨hI,U,hy,hU,hfU,H,hH⟩
  exact (Nat.card_congr hh.fiberHomeomorph.toEquiv).symm

/-- A degree proved on a genuine dense set extends to every point where the
original map is genuinely a covering; no locally constant degree is assumed. -/
theorem coveringOn_fiber_natCard_of_dense
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E→X} {A D : Set X} (hCover : IsCoveringMapOn f A) (hD : Dense D)
    (k : ℕ) (hk : ∀y∈D,Nat.card (f ⁻¹' {y})=k) :
    ∀x∈A,Nat.card (f ⁻¹' {x})=k := by
  intro x hx
  obtain ⟨U,hU,hxU,hCard⟩:=evenlyCovered_fiber_natCard_neighborhood (hCover x hx)
  obtain ⟨y,hyU,hyD⟩:=hD.inter_open_nonempty U hU ⟨x,hxU⟩
  exact (hCard y hyU).symm.trans (hk y hyD)
end LowDimensionalTopology.Geometry.Auxiliary.Topology
