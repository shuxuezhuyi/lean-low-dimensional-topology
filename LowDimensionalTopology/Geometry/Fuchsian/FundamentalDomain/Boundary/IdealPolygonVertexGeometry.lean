/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.IdealPolygonVertexBounds
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.StraightConvexAngles
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HyperbolicReflectionPencils
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped Complex.UnitDisc OnePoint UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis

local instance idealPolygonSphereMeasurableSpace : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance idealPolygonSphereBorelSpace : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- Two genuine ideal closure points of a convex region contain their entire actual
joining geodesic in its compactified closure. -/
theorem closedLine_subset_of_ideal_closure_points {S : Set Complex.UnitDisc}
    (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S) (L :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (p q : Complex.UnitClosedDisc)
    (hp : ‖(p : ℂ)‖ = 1) (hq : ‖(q : ℂ)‖ = 1) (hpq : p ≠ q)
    (hpL : p ∈ L.closedCarrier) (hqL : q ∈ L.closedCarrier)
    (hpS : p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S) (hqS : q ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S) :
    L.closedCarrier ⊆ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S := by
  rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_ideal_endpoints L p q hp hq hpq hpL
    hqL]
  exact (discClosedModelClosure_hConvex S hS) p hpS q hqS

/-- The required genuine nondegenerate triangle is constructed from the actual points. -/
def idealBoundaryPointTriangle (v : Complex.UnitDisc) (p q : Complex.UnitClosedDisc)
    (hpq : p ≠ q) (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (hpL : p ∈ L.closedCarrier) (hqL : q
      ∈ L.closedCarrier)
    (hvL : v ∉ L.carrier) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle where
  a := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel v
  b := p
  c := q
  noncollinear := by
    rintro ⟨M, hvM, hpM, hqM⟩
    have he := M.eq_of_two_closed_points L hpq hpM hqM hpL hqL
    rw [he, L.closedCarrier_mem_interior_iff] at hvM
    exact hvL hvM

theorem idealBoundaryPointTriangle_opposite_line (v : Complex.UnitDisc)
    (p q : Complex.UnitClosedDisc) (hpq : p ≠ q) (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine)
    (hpL : p ∈ L.closedCarrier) (hqL : q ∈ L.closedCarrier) (hvL : v ∉ L.carrier) :
    (idealBoundaryPointTriangle v p q hpq L hpL hqL hvL).sideLineA = L := by
  let T := idealBoundaryPointTriangle v p q hpq L hpL hqL hvL
  exact T.sideLineA.eq_of_two_closed_points L hpq
    T.b_mem_sideLineA T.c_mem_sideLineA hpL hqL

/-- A complete geodesic in the genuine closure forces a straight local angle at each
of its finite points. The line and the normalizing isometry are constructed. -/
theorem discHConvex_angle_ge_pi_of_line_closure {S : Set Complex.UnitDisc}
    (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S) (ho : IsOpen S) (hn : S.Nonempty) (L :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine)
    (hline : L.carrier ⊆ closure S) (v : Complex.UnitDisc) (hvL : v ∈ L.carrier) :
    Real.pi ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure S) v := by
  obtain ⟨g, hg, hLg⟩ := L.toHalfPlane.exists_normalizer
  obtain ⟨q, hq⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.positive_realGL_exists_SL g hg
  let F := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Homeomorph q
  let S' := F '' S
  have hF : letI := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric; Isometry F := by
    let idealVertexDiscMetric := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action_isometry q
  have hS' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S' := hS.isometry_image hF
  have ho' : IsOpen S' := F.isOpenMap S ho
  have hn' : S'.Nonempty := hn.image F
  have haxis (x : ℍ) (hx : x.re = 0) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x ∈ closure S' := by
    have hpre : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (q⁻¹ • x) ∈ L.carrier := by
      rw [L.mem_carrier, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc, hLg]
      change (g • (q⁻¹ • x)).re = 0
      rw [← hq, smul_inv_smul]
      exact hx
    have hm := hline hpre
    have he : F (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (q⁻¹ • x)) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x := by
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (q •
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (q⁻¹ • x))) = _
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc, smul_inv_smul]
    rw [← he, ← F.image_closure]
    exact mem_image_of_mem F hm
  have haxisClosed : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
    0).toDiscLine.closedCarrier ⊆
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S' := by
    change closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).toDiscLine.carrier) ⊆ _
    apply isClosed_closure.closure_subset_iff.mpr
    rintro _ ⟨z, hz, rfl⟩
    have hz0 := ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).mem_discCarrier z).mp hz
    have hm := haxis (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z) hz0
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane] at hm
    change z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S'
    rwa [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRelativeClosure_eq_preimage]
  have hiAxis : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint ∈
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).toDiscLine.closedCarrier := by
    rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.cayley_image_closedCarrier]
    apply mem_image_of_mem
    apply ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).closedCarrier_mem_ideal_iff
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint_ideal).mpr
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.vertical_idealEndpoints]
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint]
  let c := q • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane v
  have hc0 : c.re = 0 := by
    have hv := (L.mem_carrier v).mp hvL
    rw [hLg] at hv
    change (g • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane v).re = 0 at hv
    simpa only [← hq] using hv
  let a := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (c.im / 2) (by have := c.im_pos; positivity)
  have haS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S' := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S'
    rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRelativeClosure_eq_preimage]
    exact haxis a rfl
  have hcS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc c) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S' := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc c ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S'
    rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRelativeClosure_eq_preimage]
    exact haxis c hc0
  have hstraight := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_region_angle_ge_pi_of_vertical_closure_points
    hS' ho' hn' (haxisClosed hiAxis) a c
    (by change c.re = 0; exact hc0)
    (by change c.im / 2 < c.im; linarith only [c.im_pos]) haS hcS
  have he : F v = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc c := rfl
  rw [← he] at hstraight
  have hang := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle_isometry F hF (closure S) v
  rw [F.image_closure] at hang
  rwa [hang] at hstraight

/-- A genuine finite polygon point of stabilizer order at least three cannot lie
on the geodesic between two actual ideal closure points. -/
theorem original_ideal_joining_line_excludes_order_ge_three
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (v : P.domain.carrier) (hv : v ∈ closure D)
    (p q : Complex.UnitClosedDisc) (hp : ‖(p : ℂ)‖ = 1) (hq : ‖(q : ℂ)‖ = 1)
    (hpq : p ≠ q) (hpD : p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure
      (P.finiteCoordinate '' D))
    (hqD : q ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D)) (L :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine)
    (hpL : p ∈ L.closedCarrier) (hqL : q ∈ L.closedCarrier)
    (hn : 3 ≤ fuchsianPointOrder P v) : P.finiteCoordinate v ∉ L.carrier := by
  intro hvL
  have hclosed := closedLine_subset_of_ideal_closure_points hD.convex L p q hp hq hpq hpL hqL hpD hqD
  have hline : L.carrier ⊆ closure (P.finiteCoordinate '' D) := by
    intro z hz
    change z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRelativeClosure (P.finiteCoordinate '' D)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRelativeClosure_eq_preimage]
    exact hclosed ((L.closedCarrier_mem_interior_iff z).mpr hz)
  have hstraight := discHConvex_angle_ge_pi_of_line_closure hD.convex
    (P.finiteCoordinate.isOpenMap _ hD.locallyFinite.fundamental.isOpen)
    (hD.locallyFinite.fundamental.nonempty.image P.finiteCoordinate) L hline (P.finiteCoordinate v) hvL
  have hangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure (P.finiteCoordinate '' D))
      (P.finiteCoordinate v) = fuchsianPolygonAngle P D v := by
    rw [← P.finiteCoordinate.image_closure]
    rfl
  rw [hangle] at hstraight
  have hupper := original_polygon_angle_le_order hD v hv
  have hnR : (3 : ℝ) ≤ fuchsianPointOrder P v := by exact_mod_cast hn
  have hpos : (0 : ℝ) < fuchsianPointOrder P v := by linarith only [hnR]
  have hless : 2 * Real.pi / (fuchsianPointOrder P v : ℝ) < Real.pi := by
    apply (div_lt_iff₀ hpos).mpr
    nlinarith only [hnR, Real.pi_pos]
  exact (not_lt_of_ge (hstraight.trans hupper)) hless

/-- The actual ideal joining-line estimate needs only the original points, not a
supplied triangle. The collinear order-two case is included. -/
theorem original_ideal_joining_line_cosh_pointDist_ge_csc_order
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (v : P.domain.carrier) (hv : v ∈ closure D)
    (p q : Complex.UnitClosedDisc) (hp : ‖(p : ℂ)‖ = 1) (hq : ‖(q : ℂ)‖ = 1)
    (hpq : p ≠ q) (hpD : p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure
      (P.finiteCoordinate '' D))
    (hqD : q ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D)) (L :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine)
    (hpL : p ∈ L.closedCarrier) (hqL : q ∈ L.closedCarrier)
    (hn : 2 ≤ fuchsianPointOrder P v) :
    1 / Real.sin (Real.pi / (fuchsianPointOrder P v : ℝ)) ≤
      Real.cosh (L.pointDist (P.finiteCoordinate v)) := by
  by_cases hn2 : fuchsianPointOrder P v = 2
  · rw [hn2]
    norm_num only [Nat.cast_ofNat, Real.sin_pi_div_two, div_one]
    exact Real.one_le_cosh _
  · have hn3 : 3 ≤ fuchsianPointOrder P v := by omega
    have hvL := original_ideal_joining_line_excludes_order_ge_three
      hD v hv p q hp hq hpq hpD hqD L hpL hqL hn3
    let T := idealBoundaryPointTriangle (P.finiteCoordinate v) p q hpq L hpL hqL hvL
    have hbound := original_ideal_triangle_cosh_pointDist_ge_csc_order hD v hv T rfl hpD hqD hp hq hn
    have hline : T.sideLineA = L :=
      idealBoundaryPointTriangle_opposite_line (P.finiteCoordinate v) p q hpq L hpL hqL hvL
    rwa [hline] at hbound

/-- The universal numerical estimate is obtained for arbitrary actual points with the
necessary order-at-least-three restriction, without an extra triangle hypothesis. -/
theorem original_ideal_joining_line_cosh_pointDist_ge_two_div_sqrt_three
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (v : P.domain.carrier) (hv : v ∈ closure D)
    (p q : Complex.UnitClosedDisc) (hp : ‖(p : ℂ)‖ = 1) (hq : ‖(q : ℂ)‖ = 1)
    (hpq : p ≠ q) (hpD : p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure
      (P.finiteCoordinate '' D))
    (hqD : q ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D)) (L :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine)
    (hpL : p ∈ L.closedCarrier) (hqL : q ∈ L.closedCarrier)
    (hn : 3 ≤ fuchsianPointOrder P v) :
    2 / Real.sqrt 3 ≤ Real.cosh (L.pointDist (P.finiteCoordinate v)) :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.csc_pi_div_nat_ge_two_div_sqrt_three _ hn).trans
    (original_ideal_joining_line_cosh_pointDist_ge_csc_order
      hD v hv p q hp hq hpq hpD hqD L hpL hqL (by omega))

end LowDimensionalTopology.Geometry.Fuchsian
