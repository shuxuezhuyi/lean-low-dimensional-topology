module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.ChartwiseRectifiability

/-! # Original-atlas rectifiability under genuine monotone parameter changes -/

public section
noncomputable section
open Set Filter
open scoped Topology

namespace LowDimensionalTopology.Geometry.Surfaces

/-- Changing a curve away from the parameter set does not affect the actual
original-atlas rectifiability predicate. -/
theorem RiemannAtlas.IsChartwiseBVOn.congr
    {X : Type*} [TopologicalSpace X] {A : RiemannAtlas X}
    {α β : ℝ → X} {s : Set ℝ} (hα : A.IsChartwiseBVOn α s)
    (hpoint : EqOn α β s) : A.IsChartwiseBVOn β s := by
  intro x hx
  obtain ⟨e, he, hex, U, hU, hUsub, hUmap, hBV⟩ := hα x hx
  refine ⟨e, he, (hpoint hx) ▸ hex, U, hU, hUsub, ?_, ?_⟩
  · intro t ht
    rw [← hpoint (hUsub ht)]
    exact hUmap ht
  · change eVariationOn (fun t => e (β t)) U ≠ (⊤ : ENNReal)
    rw [← eVariationOn.congr (show EqOn (fun t => e (α t))
      (fun t => e (β t)) U from fun t ht => congrArg e (hpoint (hUsub ht)))]
    exact hBV

/-- Continuous monotone parameter changes preserve chartwise BV in the given
atlas; the proof uses full variation and relative parameter neighborhoods. -/
theorem RiemannAtlas.IsChartwiseBVOn.comp_monotone
    {X : Type*} [TopologicalSpace X] {A : RiemannAtlas X}
    {α : ℝ → X} {s t : Set ℝ} (hα : A.IsChartwiseBVOn α s)
    (σ : ℝ → ℝ) (hc : ContinuousOn σ t) (hm : MonotoneOn σ t)
    (hmap : MapsTo σ t s) : A.IsChartwiseBVOn (α ∘ σ) t := by
  intro x hx
  obtain ⟨e, he, hex, U, hU, _hUsub, hUmap, hBV⟩ := hα (σ x) (hmap hx)
  let V := t ∩ σ ⁻¹' U
  have hV : V ∈ 𝓝[t] x :=
    inter_mem self_mem_nhdsWithin (((hc x hx).tendsto_nhdsWithin hmap) hU)
  refine ⟨e, he, hex, V, hV, inter_subset_left, ?_, ?_⟩
  · intro y hy
    exact hUmap hy.2
  · change eVariationOn ((fun y => e (α y)) ∘ σ) V ≠ (⊤ : ENNReal)
    apply ne_of_lt
    exact lt_of_le_of_lt
      (eVariationOn.comp_le_of_monotoneOn (fun y => e (α y)) σ
        (hm.mono (show V ⊆ t from inter_subset_left)) (fun _ hy => hy.2))
      (lt_top_iff_ne_top.mpr hBV)

end LowDimensionalTopology.Geometry.Surfaces
