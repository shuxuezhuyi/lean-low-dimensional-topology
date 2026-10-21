/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetBoundaryAxes
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureNoncutChamber
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetCoreEquality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
open Set Topology
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

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
local notation "Ucore" => generalCoreCutChamber g orders s t ho hdef d hd hb UpperHalfPlane.I
local notation "idx" => generalCoreBoundarySideIndex g orders s t
local notation "Kcut" => (fun j : Fin t => _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Qcore (idx j 1)))
local notation "Fcut" => (fun j : Fin t => generalCoreTargetGenerator g orders s t ho hdef d hd hb (idx j 0))

/-- The actual target tile saturation has precisely the actual open cut
chamber as its interior; no wall or boundary census premise is supplied. -/
theorem generalCoreTargetTileSaturation_interior_eq_chamber : interior Tcore = Ucore := by
  rw [generalCoreTargetTileSaturation_eq_chamber_closure]
  have hIW := generalCoreAux_interior_avoids_cutWalls g orders s t ho hdef d hd hb _
    (generalCoreAux_center_mem_interior g orders s t ho hdef d hd hb)
  have hconv := generalCoreCutChamber_hConvex g orders s t ho hdef d hd hb UpperHalfPlane.I hIW
  have hopen := generalCoreCutChamber_isOpen g orders s t ho hdef d hd hb UpperHalfPlane.I
  have hne : (Ucore).Nonempty := ⟨UpperHalfPlane.I, mem_connectedComponentIn hIW⟩
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective.image_injective
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.image_interior,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.image_closure]
  exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex _).mp hconv).interior_closure_eq_of_isOpen
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isOpenMap _ hopen) (hne.image _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc)

/-- The complete original cut support lies in the actual target saturation,
because powers of the retained genuine boundary generator cover that axis. -/
theorem generalCoreCutAxis_subset_target_saturation (j : Fin t) : Kcut j ⊆ Tcore := by
  intro x hx
  dsimp only at hx
  rw [← generalCoreCutSegment_zpow_cover g orders s t ho hdef d hd hb j] at hx
  obtain ⟨m, z, hz, rfl⟩ := mem_iUnion.mp hx
  exact mem_iUnion₂.mpr ⟨Fcut j ^ m,
    (Htarget).zpow_mem (generalCoreBoundarySideIndex_generator_mem g orders s t ho hdef d hd hb j) m,
    z, (Pcore).side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Qcore (idx j 1)) hz, rfl⟩

/-- Every complete prescribed cut axis belongs to the genuine frontier of
the actual target saturation, including all its translated cut intervals. -/
theorem generalCoreCutAxis_subset_target_frontier (j : Fin t) : Kcut j ⊆ frontier Tcore := by
  intro x hx
  rw [(generalCoreTargetTileSaturation_isClosed g orders s t ho hdef d hd hb).frontier_eq]
  refine ⟨generalCoreCutAxis_subset_target_saturation g orders s t ho hdef d hd hb j hx, ?_⟩
  intro hxint
  rw [generalCoreTargetTileSaturation_interior_eq_chamber] at hxint
  have hxW : x ∈ Wcut := by
    rw [generalCoreCutWallUnion_eq_fullAxes]
    exact mem_iUnion.mpr ⟨1, x, mem_iUnion.mpr ⟨j, hx⟩, rfl⟩
  exact connectedComponentIn_subset Wcutᶜ UpperHalfPlane.I hxint hxW

/-- The actual target group preserves its entire closed tile saturation. -/
theorem generalCoreTargetTileSaturation_image (h : ℍ ≃ᵢ ℍ) (hh : h ∈ Htarget) :
    h '' Tcore = Tcore := by
  rw [generalCoreTargetTileSaturation_eq_chamber_closure]
  have he := h.toHomeomorph.image_closure Ucore
  change h '' closure Ucore = closure (h '' Ucore) at he
  rw [generalCoreTargetGroup_chamber_image g orders s t ho hdef d hd hb h hh] at he
  exact he

/-- The whole actual target boundary consists exactly of target translates
of the finitely many complete original cut axes. -/
theorem generalCoreTargetTileSaturation_frontier_eq_axes :
    frontier Tcore = generalCoreTargetBoundaryAxes g orders s t ho hdef d hd hb := by
  apply subset_antisymm
  · exact generalCoreTargetTileSaturation_frontier_subset_axes g orders s t ho hdef d hd hb
  · intro x hx
    obtain ⟨h, hh, y, hy, rfl⟩ := mem_iUnion₂.mp hx
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
    have hyfront := generalCoreCutAxis_subset_target_frontier g orders s t ho hdef d hd hb j hyj
    have he := h.toHomeomorph.image_frontier Tcore
    change h '' frontier Tcore = frontier (h '' Tcore) at he
    rw [generalCoreTargetTileSaturation_image g orders s t ho hdef d hd hb h hh] at he
    exact he ▸ mem_image_of_mem h hyfront

/-- The same complete finite-orbit support cover is the genuine frontier
of the original open cut chamber. -/
theorem generalCoreCutChamber_frontier_eq_axes :
    frontier Ucore = generalCoreTargetBoundaryAxes g orders s t ho hdef d hd hb := by
  rw [(generalCoreCutChamber_isOpen g orders s t ho hdef d hd hb UpperHalfPlane.I).frontier_eq,
    ← generalCoreTargetTileSaturation_eq_chamber_closure]
  have he := (generalCoreTargetTileSaturation_isClosed g orders s t ho hdef d hd hb).frontier_eq
  rw [generalCoreTargetTileSaturation_interior_eq_chamber] at he
  exact he.symm.trans (generalCoreTargetTileSaturation_frontier_eq_axes g orders s t ho hdef d hd hb)

/-- The source-defined Nielsen region of this same actual target group has
exactly these actual target translates of the prescribed complete cut axes
as its finite native frontier. -/
theorem generalCoreTarget_nielsen_frontier_eq_axes
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (generalCoreTargetMobiusGroup g orders s t ho hdef d hd hb)) :
    frontier (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹'
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.asFuchsianDisc
        (generalCoreTargetMobiusData g orders s t ho hdef d hd hb)).nielsenRegion hNE) =
      generalCoreTargetBoundaryAxes g orders s t ho hdef d hd hb := by
  rw [← generalCoreTarget_chamber_eq_nielsen g orders s t ho hdef d hd hb hNE]
  exact generalCoreCutChamber_frontier_eq_axes g orders s t ho hdef d hd hb

end LowDimensionalTopology.Geometry.Fuchsian
