/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetCore
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenDistanceNoLocalMaximum
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane
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
    (d : ℝ) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
local notation "P₀" => generalCoreTargetMobiusData g orders s t ho hdef d hd hb
local notation "K₀" => generalCoreTargetMobiusGroup g orders s t ho hdef d hd hb
local notation "D₀" => _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.asFuchsianDisc P₀

/-- The entire retained target saturation is exactly its source-defined
closed Nielsen core. Compactness comes from its actual cusps; boundary
containment comes from its actual retained hyperbolic side maps. -/
theorem generalCoreTargetTileSaturation_eq_nielsen_closure
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀) :
    generalCoreTargetTileSaturation g orders s t ho hdef d hd hb =
      closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE) := by
  apply subset_antisymm
  · apply tileSaturation_subset_closedCore_of_compact_defect
      (generalCoreTargetGroup g orders s t ho hdef d hd hb)
      (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon
        (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
          (generalCoreTheta_mem g orders s t ho hdef) hd hb)).carrier
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE)
      (closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE))
      isClosed_closure
      ((generalCoreTarget_nielsen_nonempty g orders s t ho hdef d hd hb hNE).mono subset_closure)
      subset_closure
      (generalCoreTarget_nielsen_closure_image g orders s t ho hdef d hd hb hNE)
      (generalCoreTarget_carrier_sdiff_nielsen_isCompact g orders s t ho hdef d hd hb hNE)
      (generalCoreTargetTileSaturation_frontier_subset_nielsen_closure
        g orders s t ho hdef d hd hb hNE)
    exact halfPlaneNielsen_infDist_not_isLocalMax P₀ hNE
  · exact generalCoreTarget_nielsen_closure_subset_tileSaturation g orders s t ho hdef d hd hb hNE

/-- The actual open hyperbolically convex region is the interior of its
ordinary closure, transported through the genuine Cayley homeomorphism. -/
theorem hConvex_interior_closure_eq_of_isOpen
    (T : Set ℍ)
    (hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex T)
    (ho : IsOpen T) (hne : T.Nonempty) : interior (closure T) = T := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective.image_injective
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.image_interior,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.image_closure]
  exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex T).mp hc).interior_closure_eq_of_isOpen
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isOpenMap T ho) (hne.image _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc)

/-- The genuine open chamber is exactly the original source Nielsen
region in the original half-plane, with no supplied core equality. -/
theorem generalCoreTarget_chamber_eq_nielsen
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀) :
    generalCoreCutChamber g orders s t ho hdef d hd hb UpperHalfPlane.I =
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE) := by
  let U := generalCoreCutChamber g orders s t ho hdef d hd hb UpperHalfPlane.I
  let N := _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE
  have hNimage : _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' N = (D₀).nielsenRegion hNE := by
    rw [image_preimage_eq_inter_range, _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_range]
    exact inter_eq_left.mpr ((D₀).nielsenRegion_properties hNE).1
  have hNconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex N := by
    apply ((D₀).hyperbolicallyConvex_halfPlane rfl N).mp
    change (D₀).HyperbolicallyConvex (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' N)
    rw [hNimage]
    exact ((D₀).nielsenRegion_properties hNE).2.2.2.1
  have hNopen : IsOpen N := ((D₀).nielsenRegion_properties hNE).2.2.1.preimage
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_isOpenEmbedding.continuous
  have hUopen := generalCoreCutChamber_isOpen g orders s t ho hdef d hd hb UpperHalfPlane.I
  have hIW := generalCoreAux_interior_avoids_cutWalls g orders s t ho hdef d hd hb _
    (generalCoreAux_center_mem_interior g orders s t ho hdef d hd hb)
  have hUconv := generalCoreCutChamber_hConvex g orders s t ho hdef d hd hb UpperHalfPlane.I hIW
  have hU := hConvex_interior_closure_eq_of_isOpen U hUconv hUopen
    ⟨UpperHalfPlane.I, mem_connectedComponentIn hIW⟩
  have hN := hConvex_interior_closure_eq_of_isOpen N hNconv hNopen
    (generalCoreTarget_nielsen_nonempty g orders s t ho hdef d hd hb hNE)
  have he : closure U = closure N :=
    (generalCoreTargetTileSaturation_eq_chamber_closure g orders s t ho hdef d hd hb).symm.trans
      (generalCoreTargetTileSaturation_eq_nielsen_closure g orders s t ho hdef d hd hb hNE)
  exact hU.symm.trans ((congrArg interior he).trans hN)

/-- Every original interior point lies in the true target Nielsen region. -/
theorem generalCoreTarget_base_interior_subset_nielsen
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀) :
    (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
        (generalCoreTheta_mem g orders s t ho hdef) hd hb)).interior ⊆
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE) := by
  rw [← generalCoreTarget_chamber_eq_nielsen g orders s t ho hdef d hd hb hNE]
  intro x hx
  apply generalCoreCutChamber_contains_base_tile_off_walls g orders s t ho hdef d hd hb
  exact ⟨(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon _).interior_subset_carrier hx,
    generalCoreAux_interior_avoids_cutWalls g orders s t ho hdef d hd hb x hx⟩

end LowDimensionalTopology.Geometry.Fuchsian
