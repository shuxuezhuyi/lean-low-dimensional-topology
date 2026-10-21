/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.ClosedBranchCover
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.CoveringFiberCardinality
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Quotient.PolygonIdentifiedCover
public import Mathlib.Topology.Maps.Proper.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
open Set Filter Topology
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false in
/-- A compact side-identified polygon maps to the group orbit space with a closed
branch-value set and a fixed covering degree on its dense complement. The
ramification set is closed and nowhere dense. -/
theorem nativeJordan_identifiedPolygon_closed_branch_cover
    {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉D.vertices →S.OppositeSideNeighborhoods s x) :
    ∃k : ℕ,0<k ∧CompactSpace S.PointQuotient ∧T2Space S.PointQuotient ∧
      CompactSpace (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated
        ℍ) ∧T2Space (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated ℍ) ∧
      Continuous S.pointToOrbit ∧IsProperMap S.pointToOrbit ∧IsOpenMap S.pointToOrbit ∧
      Function.Surjective S.pointToOrbit ∧
      (∀q : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated ℍ,(S.pointToOrbit ⁻¹'
        {q}).Finite) ∧
      ∃B:Set (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated
        ℍ),IsClosed B ∧Dense Bᶜ ∧
        IsClosed (S.pointToOrbit ⁻¹' B) ∧Dense (S.pointToOrbit ⁻¹' B)ᶜ ∧
        IsCoveringMapOn S.pointToOrbit Bᶜ ∧
        (∀q∈Bᶜ,Nat.card (S.pointToOrbit ⁻¹' {q})=k) ∧
        B=S.pointToOrbit '' {x:S.PointQuotient|
          ¬∃e:OpenPartialHomeomorph S.PointQuotient (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated ℍ),
            x∈e.source ∧S.pointToOrbit=e} ∧
        IsClosed {x:S.PointQuotient|
          ¬∃e:OpenPartialHomeomorph S.PointQuotient (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated ℍ),
            x∈e.source ∧S.pointToOrbit=e} ∧
        Dense {x:S.PointQuotient|
          ∃e:OpenPartialHomeomorph S.PointQuotient (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated ℍ),
            x∈e.source ∧S.pointToOrbit=e} := by
  obtain ⟨k,hk,hSrc,hSrcT2,hTgt,hTgtT2,hCont,hOpen,hSurj,hFib,hDense,_hCover,hDeg⟩:=
    nativeJordan_identifiedPolygon_finite_open_cover_degree C hC hbound hInside hBoundary D S hP hOpp
  let : CompactSpace S.PointQuotient:=hSrc
  let : T2Space S.PointQuotient:=hSrcT2
  let : CompactSpace (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated ℍ):=hTgt
  let : T2Space (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated ℍ):=hTgtT2
  let G:=nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D
  obtain ⟨B,hB,hdB,hpre,hdpre,_hsub,hCov,hCard,hBranch,hRawClosed,hRawRegularDense⟩:=
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.compact_finite_open_map_closed_branch_cover S.pointToOrbit hCont hOpen hFib _ hDense
      (PoincareSidePairing.pointToOrbit_localHomeomorphOn_regular G S) k hDeg
  exact ⟨k,hk,hSrc,hSrcT2,hTgt,hTgtT2,hCont,hCont.isProperMap,hOpen,hSurj,hFib,
    B,hB,hdB,hpre,hdpre,hCov,hCard,hBranch,hRawClosed,hRawRegularDense⟩

end LowDimensionalTopology.Geometry.Polygon
