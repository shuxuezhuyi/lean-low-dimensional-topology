module
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeCompactifiedSideGeometry
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- The actual original open geodesic side, excluding both finite-or-ideal endpoints. -/
def nativeCompactifiedSideInterior (p q : 𝕔𝔻) : Set ℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate ⁻¹' openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q)

theorem nativeCompactifiedSide_iff_klein_segment (p q : 𝕔𝔻) (x : ℍ) :
    x∈nativeCompactifiedSide p q ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x∈segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q) := by
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image).symm

/-- The whole true strict Euclidean side interval occurs in the native hyperbolic plane,
including when both original endpoints are ideal. -/
theorem nativeCompactifiedSideInterior_image_klein (p q : 𝕔𝔻) (hpq : p≠q) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' nativeCompactifiedSideInterior p q=
      openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q) := by
  apply subset_antisymm
  · rintro z ⟨x,hx,rfl⟩
    exact hx
  · intro z hz
    obtain ⟨x,_hx,hxz⟩:=nativeCompactifiedSide_realizes_openSegment hpq hz
    refine ⟨x,?_,hxz⟩
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x∈openSegment ℝ _ _
    rw [hxz]
    exact hz

theorem nativeCompactifiedSideInterior_connected (p q : 𝕔𝔻) (hpq : p≠q) :
    IsConnected (nativeCompactifiedSideInterior p q) := by
  constructor
  · have hz : AffineMap.lineMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q) (1/2 : ℝ)∈
      openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q) :=
      lineMap_mem_openSegment ℝ _ _ (by norm_num)
    obtain ⟨x,_hx,hxz⟩:=nativeCompactifiedSide_realizes_openSegment hpq hz
    refine ⟨x,?_⟩
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x∈openSegment ℝ _ _
    rw [hxz]
    exact hz
  · apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.isEmbedding.isInducing.isPreconnected_image.mp
    rw [nativeCompactifiedSideInterior_image_klein p q hpq]
    exact (convex_openSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q)).isPreconnected

/-- The literal open side is dense in the whole original native side, with no global
compactness assumption and with arbitrary ideal endpoint status. -/
theorem nativeCompactifiedSideInterior_closure (p q : 𝕔𝔻) :
    closure (nativeCompactifiedSideInterior p q)=nativeCompactifiedSide p q := by
  change closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate ⁻¹' openSegment ℝ
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q))=_
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.isOpenMap.preimage_closure_eq_closure_preimage
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.continuous,closure_openSegment]
  exact Set.ext fun x=>(nativeCompactifiedSide_iff_klein_segment p q x).symm

theorem nativeCompactifiedSideInterior_no_endpoints (p q : 𝕔𝔻) (hpq : p≠q)
    {x : ℍ} (hx : x∈nativeCompactifiedSideInterior p q) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)∉({p,q} : Set 𝕔𝔻) := by
  intro he
  have hk := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hpq
  simp only [mem_insert_iff,mem_singleton_iff] at he
  rcases he with he | he
  · have hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p:=congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate he
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x∈openSegment ℝ _ _ at hx
    rw [hK] at hx
    exact hk (left_mem_openSegment_iff.mp hx)
  · have hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q:=congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate he
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x∈openSegment ℝ _ _ at hx
    rw [hK] at hx
    exact hk (right_mem_openSegment_iff.mp hx)

def NativeGeodesicSideIntervals.openSide {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) (s : P.Side) : Set ℍ :=
  nativeCompactifiedSideInterior (D.startPoint s) (D.endPoint s)

theorem NativeGeodesicSideIntervals.openSide_connected {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) (s : P.Side) : IsConnected (D.openSide s) :=
  nativeCompactifiedSideInterior_connected _ _ (D.endpoint_ne s)

theorem NativeGeodesicSideIntervals.openSide_closure {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) (s : P.Side) : closure (D.openSide s)=s.val := by
  rw [D.side_eq s]
  exact nativeCompactifiedSideInterior_closure _ _

/-- The actual original open sides are pairwise disjoint, and each incident endpoint
is approached by its genuine connected open side. -/
theorem NativeGeodesicSideIntervals.openSides_pairwise_disjoint {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) : Pairwise (fun s t=>Disjoint (D.openSide s) (D.openSide t)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hx ht
  have hxs : x∈s.val := D.openSide_closure s ▸ subset_closure hx
  have hxt : x∈t.val := D.openSide_closure t ▸ subset_closure ht
  exact nativeCompactifiedSideInterior_no_endpoints _ _ (D.endpoint_ne s) hx
    (D.side_intersection s t hst x hxs hxt)

end LowDimensionalTopology.Geometry.Polygon
