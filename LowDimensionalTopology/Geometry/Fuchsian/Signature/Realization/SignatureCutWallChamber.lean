/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HalfPlanes
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic

/-- For the cut-axis walls in the general signature construction, the actual complementary component is exactly the intersection of its actual geodesic half-planes. No disjointness of the wall family is required. -/
theorem signatureCutWallChamber_eq (W : Set _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (x : ℍ)
    (hx : x ∉ ⋃ L ∈ W, L.carrier) :
    connectedComponentIn (⋃ L ∈ W, L.carrier)ᶜ x =
      ⋂ L ∈ W, _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHHalfPlane L x := by
  have hxL (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (hL : L ∈ W) : x ∉ L.carrier :=
    fun h => hx (mem_iUnion₂.mpr ⟨L, hL, h⟩)
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (⋂ L ∈ W, _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHHalfPlane L x) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.iInter (fun L => _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.iInter (fun hL =>
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHHalfPlane_hConvex L x (hxL L hL)))
  apply subset_antisymm
  · intro y hy
    apply mem_iInter₂.mpr
    intro L hL
    exact connectedComponentIn_mono x
      (show (⋃ M ∈ W, M.carrier)ᶜ ⊆ L.carrierᶜ from
        fun z hz hzL => hz (mem_iUnion₂.mpr ⟨L, hL, hzL⟩)) hy
  · apply hc.isPreconnected.subset_connectedComponentIn
      (mem_iInter₂.mpr (fun L hL => mem_connectedComponentIn (hxL L hL)))
    intro y hy hwall
    obtain ⟨L, hL, hyL⟩ := mem_iUnion₂.mp hwall
    exact connectedComponentIn_subset L.carrierᶜ x (mem_iInter₂.mp hy L hL) hyL

/-- Convexity of the genuine cut-axis chamber is derived from its geometry,
rather than supplied as an extra hypothesis to the signature construction. -/
theorem signatureCutWallChamber_hConvex
    (W : Set _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (x : ℍ)
    (hx : x ∉ ⋃ L ∈ W, L.carrier) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (connectedComponentIn (⋃ L ∈ W, L.carrier)ᶜ x) := by
  rw [signatureCutWallChamber_eq W x hx]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.iInter (fun L => _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.iInter (fun hL =>
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHHalfPlane_hConvex L x (fun h => hx (mem_iUnion₂.mpr ⟨L, hL, h⟩))))

/-- Openness requires closedness of the actual union of cut-axis walls;
an infinite intersection of open half-planes is not silently called open. -/
theorem signatureCutWallChamber_isOpen (W : Set _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (x : ℍ)
    (hclosed : IsClosed (⋃ L ∈ W, L.carrier)) :
    IsOpen (connectedComponentIn (⋃ L ∈ W, L.carrier)ᶜ x) :=
  hclosed.isOpen_compl.connectedComponentIn

/-- An actual native isometry preserving the complete cut-wall union carries
the original chamber to the chamber containing the image basepoint. -/
theorem signatureCutWallChamber_image (W : Set _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (x : ℍ)
    (hx : x ∉ ⋃ L ∈ W, L.carrier) (g : ℍ ≃ᵢ ℍ)
    (hW : g '' (⋃ L ∈ W, L.carrier) = ⋃ L ∈ W, L.carrier) :
    g '' connectedComponentIn (⋃ L ∈ W, L.carrier)ᶜ x =
      connectedComponentIn (⋃ L ∈ W, L.carrier)ᶜ (g x) := by
  have he : g '' (⋃ L ∈ W, L.carrier)ᶜ = (⋃ L ∈ W, L.carrier)ᶜ := by
    rw [image_compl_eq g.bijective, hW]
  have hc := g.toHomeomorph.image_connectedComponentIn
    (show x ∈ (⋃ L ∈ W, L.carrier)ᶜ from hx)
  change g '' connectedComponentIn (⋃ L ∈ W, L.carrier)ᶜ x =
    connectedComponentIn (g '' (⋃ L ∈ W, L.carrier)ᶜ) (g x) at hc
  rwa [he] at hc

/-- For the actual chamber stabilizer, membership is tested at the original
basepoint; preservation of the complete wall union is the only action input. -/
theorem signatureCutWallChamber_stabilizes_iff
    (W : Set _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (x : ℍ)
    (hx : x ∉ ⋃ L ∈ W, L.carrier) (g : ℍ ≃ᵢ ℍ)
    (hW : g '' (⋃ L ∈ W, L.carrier) = ⋃ L ∈ W, L.carrier) :
    g '' connectedComponentIn (⋃ L ∈ W, L.carrier)ᶜ x =
        connectedComponentIn (⋃ L ∈ W, L.carrier)ᶜ x ↔
      g x ∈ connectedComponentIn (⋃ L ∈ W, L.carrier)ᶜ x := by
  constructor
  · intro he
    exact he ▸ mem_image_of_mem g (mem_connectedComponentIn hx)
  · intro hg
    rw [signatureCutWallChamber_image W x hx g hW]
    exact (connectedComponentIn_eq hg).symm

end LowDimensionalTopology.Geometry.Fuchsian
