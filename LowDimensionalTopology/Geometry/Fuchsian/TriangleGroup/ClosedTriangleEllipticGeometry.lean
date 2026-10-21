/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleCornerOrders
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleIdealLabels
public import Mathlib.GroupTheory.IndexNormal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The original conformal triangle subgroup is invariant under the entire actual reflection group. -/
theorem closedTriangle_conformal_conjugate_mem (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (k:ℍ≃ᵢℍ) (hk:k∈triangleReflectionGroup T)
    (f:ℍ≃ᵢℍ) (hf:f∈triangleConformalGroup T) :
    k*f*k⁻¹∈triangleConformalGroup T := by
  let K:=triangleConformalKernel T
  let kH:triangleReflectionGroup T:=⟨k,hk⟩
  let fH:triangleReflectionGroup T:=⟨f,hf.1⟩
  have hN:K.Normal:=Subgroup.normal_of_index_eq_two (triangleConformalKernel_index_two T)
  have hConf:kH*fH*kH⁻¹∈K:=hN.conj_mem fH hf.2 kH
  exact ⟨(triangleReflectionGroup T).mul_mem ((triangleReflectionGroup T).mul_mem hk hf.1)
    ((triangleReflectionGroup T).inv_mem hk),hConf⟩

/-- A genuine mirror through the target changes an odd transporter into an actual conformal one. -/
theorem closedTriangle_even_transporter (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (z:ℍ) (x:(closedTrianglePoincarePolygon T).Point) (j:Fin 3)
    (hx:x.val∈T.nativeSide j) (k:ℍ≃ᵢℍ) (hk:k∈triangleReflectionGroup T)
    (hkx:k z=x.val) : ∃g:triangleConformalGroup T,g • z=x.val := by
  by_cases hConf:k∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup
  · exact ⟨⟨k,hk,hConf⟩,hkx⟩
  · let s:=(closedTrianglePoincarePairing T).generator (closedTrianglePoincareSideEquiv T j)
    have hs:s.val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (T.nativeLine j):=by
      change closedTrianglePoincareElement T (closedTrianglePoincareSideEquiv T j)=_
      simp only [closedTrianglePoincareElement,Equiv.symm_apply_apply]
    have hsH:s.val∈triangleReflectionGroup T:=by
      rw [←closedTrianglePoincarePairing_generated]
      exact s.property
    let sH:triangleReflectionGroup T:=⟨s.val,hsH⟩
    let kH:triangleReflectionGroup T:=⟨k,hk⟩
    have hsOdd:sH∉triangleConformalKernel T:=by
      change s.val∉_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup
      rw [hs]
      exact halfPlaneLineReflectionIsometry_not_conformal _
    have hkOdd:kH∉triangleConformalKernel T:=hConf
    have hEven:sH*kH∈triangleConformalKernel T:=
      (Subgroup.mul_mem_iff_of_index_two (triangleConformalKernel_index_two T)).mpr
        (iff_of_false hsOdd hkOdd)
    refine ⟨⟨s.val*k,(triangleReflectionGroup T).mul_mem hsH hk,hEven⟩,?_⟩
    change s.val (k z)=x.val
    rw [hkx]
    exact closedTrianglePoincareElement_fixed T (closedTrianglePoincareSideEquiv T j) hx

/-- Every actual nontrivial conformal fixed point lies in the conformal orbit of an original finite vertex. -/
theorem closedTriangle_conformal_fixed_point_vertex_orbit
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (z:ℍ) (f:ℍ≃ᵢℍ)
    (hf:f∈triangleConformalGroup T) (hfn:f≠1) (hfix:f z=z) :
    ∃i:Fin 3,∃x:(closedTrianglePoincarePolygon T).Point,
      closedTriangleVertex T i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel x.val ∧
        ∃g:triangleConformalGroup T,g • z=x.val := by
  obtain ⟨k,y,hy,hky⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.closure_covering (triangleReflectionGroup T) ℍ
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.fundamentalDomain_of_integral_angles T ha hb hc) z
  let x:(closedTrianglePoincarePolygon T).Point:=⟨y,(closedTrianglePoincarePolygon_carrier T).symm ▸ hy⟩
  have hkz:k.val⁻¹ z=x.val:=by
    change k.val⁻¹ z=y
    rw [←hky]
    exact k.val.symm_apply_apply y
  have hFix:(k.val⁻¹*f*k.val) x.val=x.val:=by
    change k.val⁻¹ (f (k.val x.val))=x.val
    rw [show k.val x.val=z from hky,hfix,hkz]
  have hMem:k.val⁻¹*f*k.val∈triangleConformalGroup T:=by
    simpa only [inv_inv] using closedTriangle_conformal_conjugate_mem T k.val⁻¹
      ((triangleReflectionGroup T).inv_mem k.property) f hf
  have hNe:k.val⁻¹*f*k.val≠1:=by
    intro he
    apply hfn
    calc
      f=k.val*(k.val⁻¹*f*k.val)*k.val⁻¹:=by group
      _=1:=by rw [he];group
  obtain ⟨i,hi⟩:=closedTriangle_conformal_fixed_point_is_vertex T ha hb hc x _ hMem hNe hFix
  have hxj:x.val∈T.nativeSide (closedTriangleAdjacentSides i 0):=
    (closedTriangle_vertex_side_iff T i _ x hi).mpr
      ((closedTriangleAdjacentSides_iff i _).mpr (Or.inl rfl))
  exact ⟨i,x,hi,closedTriangle_even_transporter T z x _ hxj k.val⁻¹
    ((triangleReflectionGroup T).inv_mem k.property) hkz⟩



/-- Positive original corner angles are exactly the original physical finite vertices. -/
theorem closedTrianglePhysicalVertex_finite_iff
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i:Fin 3) :
    ‖(closedTrianglePhysicalVertex T i).val‖<1 ↔0<closedTriangleCornerAngle T i := by
  fin_cases i
  · exact T.toDiscTriangle.alpha_pos_iff_finite.symm
  · exact T.toDiscTriangle.cycle.alpha_pos_iff_finite.symm
  · exact T.toDiscTriangle.cycle.cycle.alpha_pos_iff_finite.symm

/-- The actual native point of each original positive-angle vertex. -/
def closedTriangleFiniteVertexPoint (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i:{i:Fin 3|0<closedTriangleCornerAngle T i}) : (closedTrianglePoincarePolygon T).Point :=
  (closedTrianglePhysicalRegionHomeomorph T).symm
    ⟨closedTrianglePhysicalVertex T i.val,(closedTrianglePhysicalVertex_finite_iff T i.val).mpr i.property⟩

theorem closedTriangleFiniteVertexPoint_vertex (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i:{i:Fin 3|0<closedTriangleCornerAngle T i}) :
    closedTriangleVertex T i.val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (closedTriangleFiniteVertexPoint T i).val := by
  have h:=congrArg (fun p:closedTrianglePhysicalOpenRegion T=>p.val.val)
    ((closedTrianglePhysicalRegionHomeomorph T).apply_symm_apply
      ⟨closedTrianglePhysicalVertex T i.val,(closedTrianglePhysicalVertex_finite_iff T i.val).mpr i.property⟩)
  change closedTrianglePhysicalCayley (closedTriangleFiniteVertexPoint T i).val=
    (closedTrianglePhysicalVertex T i.val).val at h
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.injective
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_on_interior]
  apply Complex.UnitClosedDisc.coe_injective
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph (closedTriangleVertex T i.val):ℂ)=
    closedTrianglePhysicalCayley (closedTriangleFiniteVertexPoint T i).val
  rw [h]
  have he:∀j:Fin 3,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph (closedTriangleVertex T j):ℂ)=
      (closedTrianglePhysicalVertex T j).val:=by intro j;fin_cases j <;> rfl
  exact he i.val

/-- Distinct original finite vertices never represent the same actual conformal orbit. -/
theorem closedTriangle_finite_vertex_orbits_distinct
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma)
    (i j:{i:Fin 3|0<closedTriangleCornerAngle T i}) (g:triangleConformalGroup T)
    (hxy:g • (closedTriangleFiniteVertexPoint T i).val=(closedTriangleFiniteVertexPoint T j).val) : i=j := by
  have hpoint:=closedTriangle_closed_chamber_orbit_unique T ha hb hc
    (closedTriangleFiniteVertexPoint T i) (closedTriangleFiniteVertexPoint T j) g.val g.property.1 hxy
  have hvi:=closedTriangleFiniteVertexPoint_vertex T i
  have hvj:=closedTriangleFiniteVertexPoint_vertex T j
  have hi:closedTrianglePhysicalVertex T i.val=closedTrianglePhysicalVertex T j.val:=by
    apply Subtype.ext
    have he:∀k:Fin 3,(closedTrianglePhysicalVertex T k).val=
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph (closedTriangleVertex T k):ℂ):=by intro k;fin_cases k <;> rfl
    rw [he i.val,he j.val,hvi,hvj,hpoint]
  exact Subtype.ext (closedTrianglePhysicalVertex_injective T hi)



theorem closedTriangle_finite_vertex_angle_pos (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (x:(closedTrianglePoincarePolygon T).Point) (i:Fin 3)
    (hv:closedTriangleVertex T i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel x.val) :
    0<closedTriangleCornerAngle T i := by
  let U:=closedTriangleCornerCycle T i
  have hUa:U.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel x.val:=(closedTriangleCornerCycle_vertex T i).trans hv
  let C:=U.finiteCornerAtA x.val hUa
  rw [←closedTriangleCornerCycle_angle T i,←closedTriangle_finiteCorner_angle U x.val hUa]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_pos C.rayAB C.rayAC C.proper

/-- Each genuine original finite corner has a nonidentity stabilizer in the whole conformal group. -/
theorem closedTriangle_finite_vertex_nontrivial_stabilizer
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (i:{i:Fin 3|0<closedTriangleCornerAngle T i}) :
    ∃g:triangleConformalGroup T,g≠1 ∧g • (closedTriangleFiniteVertexPoint T i).val=
      (closedTriangleFiniteVertexPoint T i).val := by
  have hI:IsIntegralTriangleAngle (closedTriangleCornerAngle T i.val):=by
    rcases i with ⟨i,hi⟩
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  rcases hI with hz|⟨n,hn,hθ⟩
  · have hp:0<closedTriangleCornerAngle T i.val:=i.property
    rw [hz] at hp
    exact False.elim (lt_irrefl 0 hp)
  · let x:=closedTriangleFiniteVertexPoint T i
    have hv:=closedTriangleFiniteVertexPoint_vertex T i
    let r:=closedTriangleCornerRotation T i.val
    have ho:orderOf r=n:=closedTriangle_corner_rotation_order T x i.val hv n hn hθ
    have hne:r≠1:=by intro he;rw [he,orderOf_one] at ho;omega
    have hr:r∈triangleConformalGroup T ⊓ MulAction.stabilizer (ℍ≃ᵢℍ) x.val:=by
      rw [closedTriangle_vertex_conformal_stabilizer T ha hb hc x i.val hv]
      exact Subgroup.mem_zpowers r
    exact ⟨⟨r,hr.1⟩,fun he=>hne (congrArg Subtype.val he),hr.2⟩

end LowDimensionalTopology.Geometry.Fuchsian
