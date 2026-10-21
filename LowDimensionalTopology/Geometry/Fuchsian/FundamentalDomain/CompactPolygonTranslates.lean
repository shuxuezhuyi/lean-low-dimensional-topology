module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeIsometryDiscontinuity
public import Mathlib.Topology.Compactness.LocallyFinite
/-!
# Locally finite translates of compact polygons

Proper discontinuity makes the translates of a compact set locally finite.
The union of their frontiers is closed, so its complement is open.
-/

@[expose] public section
noncomputable section
open Set Filter Topology
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
variable (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H]

/-- Compact original polygons have finitely many actual translate labels meeting a
compact test set; no fundamental-domain or packing assumption is used. -/
theorem native_compact_translate_hits_finite {P K : Set ℍ}
    (hP : IsCompact P) (hK : IsCompact K) :
    {g : H | (g • P∩K).Nonempty}.Finite := by
  have hd:=nativeIsometrySubgroup_properlyDiscontinuous H
  simpa only [image_smul] using hd.finite_disjoint_inter_image hP hK

/-- Every discrete native isometry subgroup has a genuinely locally finite family of
translates of any compact original polygon. -/
theorem native_compact_translates_locallyFinite {P : Set ℍ} (hP : IsCompact P) :
    LocallyFinite (fun g : H=>g • P) := by
  intro x
  obtain ⟨K,hK,hxK⟩:=exists_compact_mem_nhds x
  exact ⟨K,hxK,native_compact_translate_hits_finite H hP hK⟩

/-- The full union of actual translated closed polygon boundaries is closed. -/
theorem native_compact_translated_frontiers_isClosed {P : Set ℍ} (hP : IsCompact P) :
    IsClosed (⋃g : H,frontier (g • P)) := by
  have hf:=(native_compact_translates_locallyFinite H hP).closure
  have hh : LocallyFinite (fun g : H=>frontier (g • P)):=
    hf.subset (fun _=>frontier_subset_closure)
  exact hh.isClosed_iUnion (fun _=>isClosed_frontier)

/-- Off all actual tile boundaries, every point has a true open neighborhood avoiding
all of them simultaneously. -/
theorem native_compact_compl_translated_frontiers_isOpen {P : Set ℍ} (hP : IsCompact P) :
    IsOpen ((⋃g : H,frontier (g • P))ᶜ) :=
  (native_compact_translated_frontiers_isClosed H hP).isOpen_compl

end LowDimensionalTopology.Geometry.Fuchsian
