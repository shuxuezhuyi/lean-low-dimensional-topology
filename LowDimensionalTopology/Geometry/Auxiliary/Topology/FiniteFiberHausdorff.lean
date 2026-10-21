/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import Mathlib.Topology.Separation.Hausdorff
@[expose] public section
set_option autoImplicit false
open Set
namespace LowDimensionalTopology.Geometry.Auxiliary.Topology
universe u v

/-- Finite source fibers can be separated upstairs and their saturated neighborhoods descend. -/
theorem finiteFiber_t2Space_of_saturatedNeighborhoods
    {A : Type u} {B : Type v} [TopologicalSpace A] [T2Space A] [TopologicalSpace B]
    (q : A→B) (hq : Function.Surjective q)
    (hfinite : ∀b : B,(q ⁻¹' {b}).Finite)
    (hsat : ∀(b : B)(U : Set A),IsOpen U→q ⁻¹' {b}⊆U→
      ∃V : Set B,IsOpen V ∧ b∈V ∧ q ⁻¹' V⊆U) : T2Space B := by
  constructor
  intro b c hbc
  have hd : Disjoint (q ⁻¹' {b}) (q ⁻¹' {c}) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    change q x=b at hx
    change q x=c at hy
    exact hbc (hx.symm.trans hy)
  obtain ⟨U,W,hU,hW,hbU,hcW,hUW⟩:=SeparatedNhds.of_finite (hfinite b) (hfinite c) hd
  obtain ⟨V,hV,hbV,hVU⟩:=hsat b U hU hbU
  obtain ⟨Z,hZ,hcZ,hZW⟩:=hsat c W hW hcW
  refine ⟨V,Z,hV,hZ,hbV,hcZ,Set.disjoint_left.mpr ?_⟩
  intro d hdV hdZ
  obtain ⟨x,rfl⟩:=hq d
  exact Set.disjoint_left.mp hUW (hVU hdV) (hZW hdZ)

end LowDimensionalTopology.Geometry.Auxiliary.Topology
