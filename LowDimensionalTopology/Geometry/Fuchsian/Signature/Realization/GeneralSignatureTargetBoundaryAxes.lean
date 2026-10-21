/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureCutAxisIncidence
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
  (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
  (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)

local notation "Qcore" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
  (generalCoreTheta_mem g orders s t ho hdef) hd hb
local notation "Pcore" => _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Qcore
local notation "Saux" => generalCoreAuxSidePairing g orders s t ho hdef d hd hb
local notation "Htarget" => generalCoreTargetGroup g orders s t ho hdef d hd hb
local notation "Wcut" => generalCoreCutWallUnion g orders s t ho hdef d hd hb
local notation "Tcore" => generalCoreTargetTileSaturation g orders s t ho hdef d hd hb

/-- The actual retained group's translates of the finitely many prescribed
complete boundary-cut supports, with no assigned boundary-class census. -/
def generalCoreTargetBoundaryAxes : Set ℍ :=
  ⋃ h ∈ Htarget, h '' (⋃ j : Fin t,
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Qcore (generalCoreBoundarySideIndex g orders s t j 1)).carrier)

/-- Every frontier point of the actual whole target tile saturation lies
on an actual auxiliary cut wall, because the saturation is locally open
at every one of its points away from the walls. -/
theorem generalCoreTargetTileSaturation_frontier_subset_walls :
    frontier Tcore ⊆ Wcut := by
  intro x hx
  have hxS : x ∈ Tcore :=
    (generalCoreTargetTileSaturation_isClosed g orders s t ho hdef d hd hb).frontier_subset hx
  by_contra hxW
  have hopen := generalCoreTargetTileSaturation_off_walls_isOpen g orders s t ho hdef d hd hb
  have hxint : x ∈ interior (Tcore ∩ Wcutᶜ) := by
    rw [hopen.interior_eq]
    exact ⟨hxS, hxW⟩
  exact hx.2 (interior_mono inter_subset_left hxint)

/-- Every boundary point of the actual whole target saturation lies on a
translate by the actual target group of one of its original finitely many
cut supports. No boundary cover or core-identification premise is supplied. -/
theorem generalCoreTargetTileSaturation_frontier_subset_axes :
    frontier Tcore ⊆ generalCoreTargetBoundaryAxes g orders s t ho hdef d hd hb := by
  intro x hx
  have hxS : x ∈ Tcore :=
    (generalCoreTargetTileSaturation_isClosed g orders s t ho hdef d hd hb).frontier_subset hx
  have hxW := generalCoreTargetTileSaturation_frontier_subset_walls g orders s t ho hdef d hd hb hx
  obtain ⟨h, hh, y, hy, rfl⟩ := mem_iUnion₂.mp hxS
  have hhAux : h ∈ (Saux).Generated := generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb hh
  have hyW : y ∈ Wcut := by
    have himage : h y ∈ h '' Wcut := by
      rw [generalCoreCutWallUnion_image g orders s t ho hdef d hd hb h hhAux]
      exact hxW
    obtain ⟨z, hz, he⟩ := himage
    exact h.injective he ▸ hz
  have hyAxes := generalCoreAux_carrier_wall_subset_axes g orders s t ho hdef d hd hb ⟨hy, hyW⟩
  exact mem_iUnion₂.mpr ⟨h, hh, y, hyAxes, rfl⟩

end LowDimensionalTopology.Geometry.Fuchsian
