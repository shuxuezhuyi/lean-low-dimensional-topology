/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareDevelopmentConnected
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleTypeGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleTopology
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PerpendicularBisectors
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane Pointwise
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

/-- The actual three finite-triangle sides, retaining their literal native h-segments. -/
def finiteTrianglePoincareSide
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) : Fin 3→Set ℍ:=![T.sideA,T.sideB,T.sideC]

def finiteTrianglePoincareLine (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) : Fin 3→_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine:=
  ![T.sideLineA,T.sideLineB,T.sideLineC]

theorem finiteTrianglePoincareSide_subset_line
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (i : Fin 3) :
    finiteTrianglePoincareSide T i⊆(finiteTrianglePoincareLine T i).carrier := by
  fin_cases i
  · exact T.sideLineA.closedHSegment_subset T.b_ne_c T.rayBC.start_mem_support
      (T.rayBC.subset_support T.c_mem_rayBC)
  · exact T.sideLineB.closedHSegment_subset T.c_ne_a T.rayCA.start_mem_support
      (T.rayCA.subset_support T.a_mem_rayCA)
  · exact T.sideLineC.closedHSegment_subset T.a_ne_b T.rayAB.start_mem_support
      (T.rayAB.subset_support T.b_mem_rayAB)

theorem finiteTrianglePoincareSide_nonempty
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (i : Fin 3) :
    (finiteTrianglePoincareSide T i).Nonempty := by
  fin_cases i
  · exact ⟨T.b,_root_.LowDimensionalTopology.Geometry.Hyperbolic.mem_closedHSegment_of_dist_triangle_eq T.b_ne_c (by simp)⟩
  · exact ⟨T.c,_root_.LowDimensionalTopology.Geometry.Hyperbolic.mem_closedHSegment_of_dist_triangle_eq T.c_ne_a (by simp)⟩
  · exact ⟨T.a,_root_.LowDimensionalTopology.Geometry.Hyperbolic.mem_closedHSegment_of_dist_triangle_eq T.a_ne_b (by simp)⟩

theorem finiteTrianglePoincareSide_injective (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    Function.Injective (finiteTrianglePoincareSide T) := by
  have hAB : T.sideA≠T.sideB := by
    intro he
    have hb : T.b∈T.sideA:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.mem_closedHSegment_of_dist_triangle_eq T.b_ne_c (by simp)
    rw [he] at hb
    exact T.b_not_mem_sideLineB (finiteTrianglePoincareSide_subset_line T 1 hb)
  have hAC : T.sideA≠T.sideC := by
    intro he
    have hc : T.c∈T.sideA:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.mem_closedHSegment_of_dist_triangle_eq T.b_ne_c (by simp)
    rw [he] at hc
    exact T.c_not_mem_sideLineC (finiteTrianglePoincareSide_subset_line T 2 hc)
  have hBC : T.sideB≠T.sideC := by
    intro he
    have hc : T.c∈T.sideB:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.mem_closedHSegment_of_dist_triangle_eq T.c_ne_a (by simp)
    rw [he] at hc
    exact T.c_not_mem_sideLineC (finiteTrianglePoincareSide_subset_line T 2 hc)
  intro i j he
  fin_cases i <;> fin_cases j <;> simp_all [finiteTrianglePoincareSide]

/-- The actual full native triangle boundary is exactly the union of these three genuine sides. -/
theorem finiteTrianglePoincareSide_boundary (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    ⋃₀(range (finiteTrianglePoincareSide T))=frontier T.interior := by
  rw [T.frontier_eq_sides,sUnion_range]
  ext z
  simp [finiteTrianglePoincareSide,Fin.exists_fin_succ,or_assoc]

/-- Genuine triangle data for the original Poincare polygon definition. -/
def finiteTrianglePoincarePolygon (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ where
  interior:=T.interior
  interior_nonempty:=T.interior_nonempty
  sides:=range (finiteTrianglePoincareSide T)
  sides_nonempty:=⟨_,mem_range_self 0⟩
  side_nonempty:=by rintro s ⟨i,rfl⟩;exact finiteTrianglePoincareSide_nonempty T i
  disjoint:=by
    rw [finiteTrianglePoincareSide_boundary]
    apply disjoint_left.mpr
    intro z hz hf
    exact (T.interior_isOpen.frontier_eq ▸ hf).2 hz

/-- The actual side set of the triangle has exactly its original three distinct members. -/
def finiteTrianglePoincareSideEquiv
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) : Fin 3≃(finiteTrianglePoincarePolygon T).Side :=
  Equiv.ofBijective (fun i=>⟨finiteTrianglePoincareSide T i,mem_range_self i⟩)
    ⟨fun i j he=>finiteTrianglePoincareSide_injective T (congrArg Subtype.val he),
      by rintro ⟨s,i,hi⟩;exact ⟨i,Subtype.ext hi⟩⟩

theorem finiteTrianglePoincareSideEquiv_symm (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (s : (finiteTrianglePoincarePolygon T).Side) :
    finiteTrianglePoincareSide T ((finiteTrianglePoincareSideEquiv T).symm s)=s.val :=
  congrArg Subtype.val ((finiteTrianglePoincareSideEquiv T).apply_symm_apply s)

/-- The literal side reflection attached to the actual side, with no assumed discreteness. -/
def finiteTrianglePoincareElement (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (s : (finiteTrianglePoincarePolygon T).Side) : ℍ≃ᵢℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry
    (finiteTrianglePoincareLine T ((finiteTrianglePoincareSideEquiv T).symm s))

theorem finiteTrianglePoincareElement_fixed (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (s : (finiteTrianglePoincarePolygon T).Side) {x : ℍ} (hx : x∈s.val) :
    finiteTrianglePoincareElement T s x=x := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflection_fixed_iff _ x).mpr
  apply finiteTrianglePoincareSide_subset_line T ((finiteTrianglePoincareSideEquiv T).symm s)
  rwa [finiteTrianglePoincareSideEquiv_symm]

/-- Reflection in each true side gives its actual self-paired Poincare pairing. -/
def finiteTrianglePoincarePairing (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (finiteTrianglePoincarePolygon T) where
  paired:=Equiv.refl _
  involutive:=fun _=>rfl
  element:=finiteTrianglePoincareElement T
  element_paired:=fun s=>(halfPlaneLineReflectionIsometry_inv _).symm
  side_image:=by
    intro s
    apply Set.Subset.antisymm
    · rintro x ⟨y,hy,rfl⟩
      change finiteTrianglePoincareElement T s y∈s.val
      rwa [finiteTrianglePoincareElement_fixed T s hy]
    · intro x hx
      exact ⟨x,hx,finiteTrianglePoincareElement_fixed T s hx⟩

/-- The actual full carrier is exactly the compact closure of the original triangle interior. -/
theorem finiteTrianglePoincarePolygon_carrier (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    (finiteTrianglePoincarePolygon T).carrier=closure T.interior := by
  change T.interior∪⋃₀(range (finiteTrianglePoincareSide T))=closure T.interior
  rw [finiteTrianglePoincareSide_boundary]
  exact (closure_eq_self_union_frontier _).symm

/-- Compactness here is proved for the original actual polygon, rather than assumed. -/
theorem finiteTrianglePoincarePolygon_isCompact (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    IsCompact (finiteTrianglePoincarePolygon T).carrier := by
  rw [finiteTrianglePoincarePolygon_carrier]
  exact T.closure_isCompact

/-- The actual abstract development of the side-reflection triangle is connected,
without a connectedness or tessellation hypothesis on that quotient. -/
theorem finiteTrianglePoincareDevelopment_connected (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    ConnectedSpace (finiteTrianglePoincarePairing T).Development := by
  apply _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.development_connectedSpace_of_interior
  · exact ⟨T.interior_nonempty,T.interior_isPreconnected⟩
  · rw [finiteTrianglePoincarePolygon_carrier]
    exact subset_rfl

/-- The pairing elements are exactly the original three side reflections. -/
theorem finiteTrianglePoincarePairing_range (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    range (finiteTrianglePoincarePairing T).element=
      range (fun i=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (finiteTrianglePoincareLine T i)) := by
  ext f
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨(finiteTrianglePoincareSideEquiv T).symm s,rfl⟩
  · rintro ⟨i,rfl⟩
    refine ⟨finiteTrianglePoincareSideEquiv T i,?_⟩
    simp only [finiteTrianglePoincarePairing,finiteTrianglePoincareElement,Equiv.symm_apply_apply]

/-- The development's actual generated subgroup is exactly the pre-existing genuine
triangle-reflection group, rather than an abstract replacement group. -/
theorem finiteTrianglePoincarePairing_generated (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    (finiteTrianglePoincarePairing T).Generated=triangleReflectionGroup T.toClosedHTriangle := by
  change Subgroup.closure (range (finiteTrianglePoincarePairing T).element)=_
  rw [finiteTrianglePoincarePairing_range,triangleReflectionGroup,triangleReflectionSides,
    finite_closedTriangle_sideA,finite_closedTriangle_sideB,finite_closedTriangle_sideC]
  congr 1
  ext f
  simp [finiteTrianglePoincareLine,Fin.exists_fin_succ,eq_comm]

end LowDimensionalTopology.Geometry.Fuchsian
