/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Germs
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.ClosedTriangleNativeCoordinates
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleReflectionGroups
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareReflectionVertices
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
open Set Topology Filter
open scoped UpperHalfPlane

def closedTrianglePoincarePolygon (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ where
  interior:=T.interior
  interior_nonempty:=T.interior_nonempty
  sides:=range T.nativeSide
  sides_nonempty:=⟨_,mem_range_self 0⟩
  side_nonempty:=by rintro s ⟨i,rfl⟩;exact T.nativeSide_nonempty i
  disjoint:=by
    rw [T.nativeSide_boundary]
    apply disjoint_left.mpr
    intro z hz hf
    exact (T.interior_isOpen.frontier_eq ▸ hf).2 hz

def closedTrianglePoincareSideEquiv (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    Fin 3≃(closedTrianglePoincarePolygon T).Side:=
  Equiv.ofBijective (fun i=>⟨T.nativeSide i,mem_range_self i⟩)
    ⟨fun i j he=>T.nativeSide_injective (congrArg Subtype.val he),
      by rintro ⟨s,i,hi⟩;exact ⟨i,Subtype.ext hi⟩⟩

theorem closedTrianglePoincareSideEquiv_symm (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (s : (closedTrianglePoincarePolygon T).Side) :
    T.nativeSide ((closedTrianglePoincareSideEquiv T).symm s)=s.val:=
  congrArg Subtype.val ((closedTrianglePoincareSideEquiv T).apply_symm_apply s)

def closedTrianglePoincareElement (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (s : (closedTrianglePoincarePolygon T).Side) : ℍ≃ᵢℍ:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (T.nativeLine ((closedTrianglePoincareSideEquiv T).symm s))

theorem closedTrianglePoincareElement_fixed (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (s : (closedTrianglePoincarePolygon T).Side) {x : ℍ} (hx : x∈s.val) :
    closedTrianglePoincareElement T s x=x := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflection_fixed_iff _ x).mpr
  have h : x∈T.nativeSide ((closedTrianglePoincareSideEquiv T).symm s):=by
    rwa [closedTrianglePoincareSideEquiv_symm]
  rw [T.nativeSide_eq_carrier_inter_line] at h
  exact h.2

/-- All finite/ideal original side slices are paired by their actual pointwise-fixing mirrors. -/
def closedTrianglePoincarePairing (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (closedTrianglePoincarePolygon T) where
  paired:=Equiv.refl _
  involutive:=fun _=>rfl
  element:=closedTrianglePoincareElement T
  element_paired:=fun s=>(_root_.LowDimensionalTopology.Geometry.Fuchsian.halfPlaneLineReflectionIsometry_inv _).symm
  side_image:=by
    intro s
    apply Set.Subset.antisymm
    · rintro x ⟨y,hy,rfl⟩
      change closedTrianglePoincareElement T s y∈s.val
      rwa [closedTrianglePoincareElement_fixed T s hy]
    · intro x hx
      exact ⟨x,hx,closedTrianglePoincareElement_fixed T s hx⟩

theorem closedTrianglePoincarePolygon_carrier (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    (closedTrianglePoincarePolygon T).carrier=closure T.interior := by
  change T.interior∪⋃₀(range T.nativeSide)=closure T.interior
  rw [T.nativeSide_boundary]
  exact (closure_eq_self_union_frontier _).symm

theorem closedTrianglePoincareSide_isClosed (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (s : (closedTrianglePoincarePolygon T).Side) : IsClosed s.val := by
  obtain ⟨i,hi⟩:=(closedTrianglePoincareSideEquiv T).surjective s
  rw [←hi]
  exact T.nativeSide_isClosed i

instance closedTrianglePoincareSideFinite (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    Finite (closedTrianglePoincarePolygon T).Side:=Finite.of_equiv (Fin 3) (closedTrianglePoincareSideEquiv T)

theorem closedTrianglePoincareSide_locallyFinite
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    LocallyFinite (fun s:(closedTrianglePoincarePolygon T).Side=>s.val):=locallyFinite_of_finite _

theorem closedTrianglePoincarePairing_range (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    range (closedTrianglePoincarePairing T).element=
      range (fun i=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (T.nativeLine i)) := by
  ext f
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨(closedTrianglePoincareSideEquiv T).symm s,rfl⟩
  · rintro ⟨i,rfl⟩
    refine ⟨closedTrianglePoincareSideEquiv T i,?_⟩
    simp only [closedTrianglePoincarePairing,closedTrianglePoincareElement,Equiv.symm_apply_apply]

/-- The genuine native group is exactly the original full three-reflection group in every ideal case. -/
theorem closedTrianglePoincarePairing_generated
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    (closedTrianglePoincarePairing T).Generated=triangleReflectionGroup T := by
  change Subgroup.closure (range (closedTrianglePoincarePairing T).element)=_
  rw [closedTrianglePoincarePairing_range]
  unfold triangleReflectionGroup triangleReflectionSides
  congr 1
  ext f
  simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.nativeLine,Fin.exists_fin_succ,eq_comm]

theorem closedTrianglePoincare_metric_assumptions
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    (closedTrianglePoincarePairing T).MetricPolygonAssumptions:=
  ⟨fun s=>(closedTrianglePoincareElement T s).isometry,T.interior_isOpen,
    ⟨T.interior_nonempty,T.interior_isPreconnected⟩⟩

/-- The source finite-corner angle is the genuine forward-ray angle in the original native plane. -/
theorem closedTriangle_finiteCorner_angle
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (x : ℍ)
    (ha : T.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel x) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure (T.finiteCornerAtA x ha).rayAB (T.finiteCornerAtA x ha).rayAC=T.alpha := by
  generalize hz:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x=z
  have hx : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z=x:=by rw [←hz,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  subst x
  have hAD : T.toDiscTriangle.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph T.a=_
    rw [ha, _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_on_interior,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  change _=T.toDiscTriangle.alpha
  rw [T.toDiscTriangle.alpha_of_finite z hAD,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure_eq_halfPlane,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.cornerRayABAtA_toHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.cornerRayACAtA_toHalfPlane]
  rfl

theorem closedTriangle_regular_open (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : interior (closure T.interior)=T.interior := by
  rw [T.closure_interior_coordinate,
    ←T.nativeCoordinate_isOpenEmbedding.isOpenMap.preimage_interior_eq_interior_preimage
      T.nativeCoordinate_isOpenEmbedding.continuous,_root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle_interior]
  rw [←T.nativeCoordinate_image_interior,T.nativeCoordinate_isOpenEmbedding.injective.preimage_image]

theorem closedTriangle_finiteCorner_closure_germ
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (x : ℍ)
    (ha : T.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel x) : ∃r : ℝ,0<r ∧ ∀z : ℍ,dist z x<r →
      (z∈(closedTrianglePoincarePolygon T).carrier ↔
        z∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior (T.finiteCornerAtA x ha).rayAB (T.finiteCornerAtA x ha).rayAC)) := by
  obtain ⟨r,hr,he⟩:=T.locally_angleAtA x ha
  have hG : ∀ᶠz in 𝓝 x,z∈T.interior ↔
      z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior (T.finiteCornerAtA x ha).rayAB (T.finiteCornerAtA x ha).rayAC := by
    filter_upwards [Metric.ball_mem_nhds x hr] with z hz
    have hm:=Set.ext_iff.mp he z
    simpa only [mem_inter_iff,hz,true_and] using hm
  have hC:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_closure_germ hG
  rw [←closedTrianglePoincarePolygon_carrier T] at hC
  exact Metric.eventually_nhds_iff_ball.mp hC

end LowDimensionalTopology.Geometry.Fuchsian
