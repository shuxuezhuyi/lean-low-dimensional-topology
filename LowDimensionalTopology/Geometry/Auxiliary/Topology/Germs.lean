module
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Germs of sets under closure and homeomorphisms.

Equality of set membership near a point persists after taking closures and after
transport by a homeomorphism.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology

namespace LowDimensionalTopology.Geometry.Auxiliary.Topology

set_option backward.isDefEq.respectTransparency false in
/-- Equality of actual sets near a point also identifies their true closures near that point. -/
theorem angular_closure_germ {X : Type*} [TopologicalSpace X] {A B : Set X} {x : X}
    (h : ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ B) :
    ∀ᶠ y in 𝓝 x, y ∈ closure A ↔ y ∈ closure B := by
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp h
  have heq : A ∩ U = B ∩ U := by
    ext y
    exact and_congr_left (fun hy => hUsub hy)
  filter_upwards [hUopen.mem_nhds hxU] with y hy
  constructor
  · intro hyA
    have hh := hUopen.closure_inter ⟨hyA,hy⟩
    rw [heq] at hh
    exact closure_mono inter_subset_left hh
  · intro hyB
    have hh := hUopen.closure_inter ⟨hyB,hy⟩
    rw [← heq] at hh
    exact closure_mono inter_subset_left hh

set_option backward.isDefEq.respectTransparency false in
theorem angular_homeomorph_germ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X ≃ₜ Y) {A B : Set X} {x : X}
    (h : ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ B) :
    ∀ᶠ y in 𝓝 (F x), y ∈ F '' A ↔ y ∈ F '' B := by
  have ht := F.symm.continuous.tendsto (F x)
  rw [F.symm_apply_apply] at ht
  filter_upwards [ht.eventually h] with y hy
  have hA : y ∈ F '' A ↔ F.symm y ∈ A := by
    constructor
    · rintro ⟨a, ha, he⟩
      have hae : a = F.symm y := F.injective (he.trans (F.apply_symm_apply y).symm)
      exact hae ▸ ha
    · exact fun ha => ⟨F.symm y, ha, F.apply_symm_apply y⟩
  have hB : y ∈ F '' B ↔ F.symm y ∈ B := by
    constructor
    · rintro ⟨b, hb, he⟩
      have hbe : b = F.symm y := F.injective (he.trans (F.apply_symm_apply y).symm)
      exact hbe ▸ hb
    · exact fun hb => ⟨F.symm y, hb, F.apply_symm_apply y⟩
  exact hA.trans (hy.trans hB.symm)

end LowDimensionalTopology.Geometry.Auxiliary.Topology
