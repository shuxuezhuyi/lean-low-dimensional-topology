/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CanonicalHandleCW
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.LowGenusUniqueness
public import LowDimensionalTopology.External.TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Surfaces.HandleCW LowDimensionalTopology.Geometry.Surfaces.HandleSeparation

/-- The Euler characteristic is computed from the genuine finite CW structure on the unchanged handle quotient. -/
theorem canonicalHandleCW_euler (g : ℕ) (hg : 0<g) :
    let _:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleCW.canonicalHandleCW g hg
    TauCeti.cwEulerChar (univ : Set (Quot (CanonicalHandleIdent g)))=2-2*(g : ℤ) := by
  let _:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleCW.canonicalHandleCW g hg
  change TauCeti.cwEulerChar (univ : Set (Quot (CanonicalHandleIdent g)))=2-2*(g : ℤ)
  have hnil : ∀n : ℕ,3≤n→IsEmpty (Topology.RelCWComplex.cell
      (univ : Set (Quot (CanonicalHandleIdent g))) n) := by
    intro n hn
    change IsEmpty (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleCW.Cell g n)
    exact ⟨fun i=>by have hi:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleCW.cell_dimension_le g n i;omega⟩
  rw [TauCeti.cwEulerChar_eq_sum_range (univ : Set (Quot (CanonicalHandleIdent g))) hnil]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.HandleCW.canonicalHandleCW_card_zero g
    hg,_root_.LowDimensionalTopology.Geometry.Surfaces.HandleCW.canonicalHandleCW_card_one g hg,
    _root_.LowDimensionalTopology.Geometry.Surfaces.HandleCW.canonicalHandleCW_card_two g hg]
  push_cast
  ring

/-- A genuine homeomorphism preserves the independently defined topological Euler characteristic of the two actual quotients. -/
theorem canonicalHandleQuot_homeomorphic_genus_eq {g h : ℕ} (hg : 0<g) (hh : 0<h)
    (e : Quot (CanonicalHandleIdent g)≃ₜQuot (CanonicalHandleIdent h)) : g=h := by
  let _ : T2Space (Quot (CanonicalHandleIdent
    g)):=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.canonicalHandleQuotientT2 g
  let _ : T2Space (Quot (CanonicalHandleIdent
    h)):=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.canonicalHandleQuotientT2 h
  let _:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleCW.canonicalHandleCW g hg
  let _:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleCW.canonicalHandleCW h hh
  let _:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleCW.canonicalHandleCW_finite g hg
  let _:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleCW.canonicalHandleCW_finite h hh
  let E : (univ : Set (Quot (CanonicalHandleIdent g)))≃ₜ
      (univ : Set (Quot (CanonicalHandleIdent h))):=
    (Homeomorph.Set.univ _).trans (e.trans (Homeomorph.Set.univ _).symm)
  have hE:=E.eulerChar_eq
  rw [TauCeti.eulerChar_cwComplex,TauCeti.eulerChar_cwComplex,
    canonicalHandleCW_euler g hg,canonicalHandleCW_euler h hh] at hE
  omega

/-- Every actual compact oriented surface has a unique handle-model genus label. -/
theorem hasTopologicalGenus_unique {X : Type*} [TopologicalSpace X] {g h : ℕ}
    (hg : HasTopologicalGenus X g) (hh : HasTopologicalGenus X h) : g=h := by
  by_cases hg0 : g≤1
  · exact hasTopologicalGenus_unique_of_le_one hg hh hg0
  by_cases hh0 : h≤1
  · exact (hasTopologicalGenus_unique_of_le_one hh hg hh0).symm
  obtain ⟨eg⟩:=hg
  obtain ⟨eh⟩:=hh
  cases g with
  | zero=>omega
  | succ g=>
    cases h with
    | zero=>omega
    | succ h=>
      exact canonicalHandleQuot_homeomorphic_genus_eq (by omega) (by omega) (eg.symm.trans eh)

end LowDimensionalTopology.Geometry.Surfaces
