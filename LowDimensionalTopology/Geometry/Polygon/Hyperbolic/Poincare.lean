/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Development.NaturalCyclePoincare
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.NativeDirichletMeasureDomains

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane ENNReal

namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/--
A hyperbolic Jordan polygon with its interior, boundary and geodesic side intervals.
The underlying `PoincarePolygon` records set-and-sides data. This structure supplies
the Jordan curve, containment and side geometry used to recover topological regularity.
-/
structure NativeJordanGeodesicPolygon where
  polygon : PoincarePolygon ℍ
  curve : Set ℂ
  jordan : IsComplexJordanCurve curve
  contained : curve ⊆ Metric.closedBall (0 : ℂ) 1
  interior_eq : polygon.interior = nativeJordanInside curve
  boundary_eq : polygon.boundary =
    (fun z : ℍ => (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹' curve
  sideIntervals : NativeGeodesicSideIntervals polygon

namespace NativeJordanGeodesicPolygon

/-- The bundled Jordan and side-interval data imply regular-open connected interior,
closure and frontier identities, and locally finite geodesic-side geometry. -/
def geometry (J : _root_.LowDimensionalTopology.Geometry.Polygon.NativeJordanGeodesicPolygon) :
    _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry J.polygon J.sideIntervals.vertices :=
  _root_.LowDimensionalTopology.Geometry.Polygon.nativeJordan_sideIntervals_geometry J.curve J.jordan J.contained
    J.interior_eq J.boundary_eq J.sideIntervals

/--
Labeled natural vertex cycles and opposite-side neighborhoods imply the Poincare
criterion when evaluation has uniform hyperbolic ball charts. The cycle condition
and the uniform chart condition are explicit assumptions on the side pairing.
-/
theorem corrected_natural_cycle_poincare (J :
  _root_.LowDimensionalTopology.Geometry.Polygon.NativeJordanGeodesicPolygon)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ ≃ᵢ ℍ) J.polygon)
    (hNatural : S.NaturalVertexCycleCondition J.sideIntervals.vertices)
    (hOpp : ∀ s : J.polygon.Side, ∀ x ∈ s.val, x ∉ J.sideIntervals.vertices →
      S.OppositeSideNeighborhoods s x)
    {ε : ℝ} (hε : 0 < ε) (hCharts : _root_.LowDimensionalTopology.Geometry.Hyperbolic.UniformHyperbolicBallCharts
      S.evaluation ε) :
    DiscreteTopology S.Generated ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume J.polygon.interior :=
  _root_.LowDimensionalTopology.Geometry.Polygon.nativeJordan_natural_cycles_poincare J.curve J.jordan J.contained J.interior_eq
    J.boundary_eq J.sideIntervals S hNatural hOpp hε hCharts

/--
For a polygon with compact closure, one positive integer gives its angular
multiplicity and the ratio of its area to the orbit-quotient area. The acting group
may contain reflections.
-/
theorem exists_positive_constant_angularMultiplicity_and_area_eq_multiple_quotient (J :
  _root_.LowDimensionalTopology.Geometry.Polygon.NativeJordanGeodesicPolygon)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ ≃ᵢ ℍ) J.polygon) [DiscreteTopology
      S.Generated]
    (hCompact : IsCompact J.polygon.carrier)
    (hOpp : ∀ s : J.polygon.Side, ∀ x ∈ s.val, x ∉ J.sideIntervals.vertices →
      S.OppositeSideNeighborhoods s x) :
    ∃ k : ℕ, 0 < k ∧
      (∀ z : ℍ, _root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonAngularMultiplicity S.Generated
        J.polygon.interior z = k ∧
        _root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonAngularMultiplicityRadians S.Generated J.polygon.interior z =
          2 * Real.pi * (k : ℝ)) ∧
      MeasureTheory.volume J.polygon.interior =
        (k : ℝ≥0∞) * _root_.LowDimensionalTopology.Geometry.Fuchsian.nativeHyperbolicQuotientMeasure S.Generated Set.univ :=
  _root_.LowDimensionalTopology.Geometry.Fuchsian.nativeJordan_exists_positive_constant_angularMultiplicity_and_area_eq_multiple_quotient J.curve J.jordan J.contained J.interior_eq J.boundary_eq
    J.sideIntervals S hCompact hOpp

end NativeJordanGeodesicPolygon
end LowDimensionalTopology.Geometry.Polygon
