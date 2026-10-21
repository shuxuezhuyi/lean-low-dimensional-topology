module
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeCompactifiedSideGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.ClosedSegmentTransport
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc Pointwise
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

def nativeClosedDiscIsometry (f : ℍ≃ᵢℍ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.ofPathIsometry (fun
    z=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (f
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIsometry_native_distance f.isometry)

theorem nativeClosedDiscIsometry_commutes (f : ℍ≃ᵢℍ) (z : ℍ) :
    (nativeClosedDiscIsometry f).closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (f z)) := by
  rw [(nativeClosedDiscIsometry f).finite_commutes]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (f (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))))=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]

/-- An actual isometry carrying one literal native side onto another carries exactly
their original compactified endpoint pairs, including every finite/ideal combination. -/
theorem nativeCompactifiedSide_endpoint_transport (f : ℍ≃ᵢℍ) (p q a b : 𝕔𝔻)
    (hpq : p≠q) (hab : a≠b)
    (hSide : f '' nativeCompactifiedSide p q=nativeCompactifiedSide a b) :
    ({(nativeClosedDiscIsometry f).closedMap p,(nativeClosedDiscIsometry f).closedMap q} : Set 𝕔𝔻)=
      {a,b} := by
  let e:=nativeClosedDiscIsometry f
  apply e.closed_segment_image_endpoints
  rw [←nativeCompactifiedSide_closedModelClosure p q hpq,e.closedMap.image_closure,image_image]
  have he : (fun z : ℍ=>e.closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)))=
      (fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) ∘f := by
    funext z
    exact nativeClosedDiscIsometry_commutes f z
  rw [he]
  change closure ((fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (f z))) '' nativeCompactifiedSide p q)=_
  have him : (fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (f z))) '' nativeCompactifiedSide p q=
      (fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) '' (f '' nativeCompactifiedSide p q) :=
    (Set.image_image (fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))
      (fun z : ℍ=>f z) (nativeCompactifiedSide p q)).symm
  rw [him,hSide,nativeCompactifiedSide_closedModelClosure a b hab]

theorem NativeGeodesicSideIntervals.pairing_endpoint_transport {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P) (s : P.Side) :
    ({(nativeClosedDiscIsometry (S.element s)).closedMap (D.startPoint s),
      (nativeClosedDiscIsometry (S.element s)).closedMap (D.endPoint s)} : Set 𝕔𝔻)=
      {D.startPoint (S.paired s),D.endPoint (S.paired s)} := by
  apply nativeCompactifiedSide_endpoint_transport _ _ _ _ _ (D.endpoint_ne s) (D.endpoint_ne (S.paired s))
  rw [←D.side_eq s,←D.side_eq (S.paired s)]
  change S.element s •s.val=(S.paired s).val
  exact S.side_image s

theorem NativeGeodesicSideIntervals.pairing_preserves_endpoints {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    (s : P.Side) (x : ℍ) (hx : x∈D.endpoints s) : S.element s x∈D.endpoints (S.paired s) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (S.element s x))∈
    ({D.startPoint (S.paired s),D.endPoint (S.paired s)} : Set 𝕔𝔻)
  rw [←D.pairing_endpoint_transport S s,←nativeClosedDiscIsometry_commutes]
  simp only [NativeGeodesicSideIntervals.endpoints,mem_preimage,mem_insert_iff,mem_singleton_iff] at hx
  exact hx.imp (congrArg _) (congrArg _)

/-- At an original vertex, every incident original side really ends there. -/
theorem NativeGeodesicSideIntervals.vertex_on_side_endpoint {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) (x : ℍ) (hx : x∈D.vertices)
    (s : P.Side) (hxs : x∈s.val) : x∈D.endpoints s := by
  obtain ⟨t,ht⟩:=mem_iUnion.mp hx
  by_cases hst : s=t
  · exact hst.symm ▸ ht
  · exact D.side_intersection s t hst x hxs (D.endpoints_subset_side t ht)

/-- Side-pairing preservation of every original native vertex is proved from the literal
original endpoint transport; no vertex-preservation or cycle hypothesis is added. -/
theorem NativeGeodesicSideIntervals.pairing_preserves_vertices {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    (x : ℍ) (hx : x∈D.vertices) (s : P.Side) (hxs : x∈s.val) : S.element s x∈D.vertices :=
  mem_iUnion.mpr ⟨S.paired s,D.pairing_preserves_endpoints S s x (D.vertex_on_side_endpoint x hx s hxs)⟩

end LowDimensionalTopology.Geometry.Polygon
