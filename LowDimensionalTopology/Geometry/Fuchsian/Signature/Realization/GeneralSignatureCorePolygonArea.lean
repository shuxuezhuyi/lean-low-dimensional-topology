/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureCorePolygon
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped UpperHalfPlane
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
    (d : ℝ) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
  (generalCoreTheta_mem g orders s t ho hdef) hd hb

/-- The physical area of the unchanged original polygon is its original
signature deficit, including every zero and boundary corner. -/
theorem generalCorePolygon_area :
    (Q₀).area = ENNReal.ofReal (2 * Real.pi * generalCoreDeficit g orders s t) := by
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.area_eq_original_angle_defect]
  simp_rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle]
  congr 1
  have hs : ∑ i, generalCoreTheta g orders s t i = (generalCoreAngles g orders s t).sum := by
    change (∑ i : Fin (generalCoreAngles g orders s t).length,
      (generalCoreAngles g orders s t)[i.val]) = (generalCoreAngles g orders s t).sum
    rw [← List.sum_ofFn, List.ofFn_getElem]
  rw [hs]
  exact generalCore_angles_defect g orders s t (by
    have hB := generalCore_base_count g orders s t hdef
    omega)

/-- This is actual upper-half-plane density volume on the original
polygon interior, rather than a supplied area or a signature definition. -/
theorem generalCorePolygon_native_volume :
    volume (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).interior =
      ENNReal.ofReal (2 * Real.pi * generalCoreDeficit g orders s t) := by
  change volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (Q₀).interior) = _
  rw [← _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.area_eq_halfPlane_volume]
  exact generalCorePolygon_area g orders s t ho hdef d hd hb

end LowDimensionalTopology.Geometry.Fuchsian
