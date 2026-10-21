/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.HorocyclicTrianglePartition
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.IdealPolygonVertexBounds
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TwoIdealTriangles
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.ParabolicFordFundamentalDomains
@[expose] public section
noncomputable section
open Set Filter Topology MeasureTheory InnerProductGeometry
open scoped UpperHalfPlane OnePoint MatrixGroups Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The genuine one-ideal-vertex fan triangle over two ordered native points. -/
def horocyclicFanHTriangle (z w : ℍ) (hx :
  z.re<w.re) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle where
  a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel z
  b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel w
  c:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint
  noncollinear:=by
    rintro ⟨L,hz,hw,hi⟩
    have hZ:=(L.closedCarrier_mem_interior_iff z).mp hz
    have hW:=(L.closedCarrier_mem_interior_iff w).mp hw
    have hI:=(L.closedCarrier_mem_ideal_iff _
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint_ideal).mp hi
    obtain ⟨a,rfl⟩:=L.eq_vertical_of_infty_ideal hI
    have hz' : z.re=a:=hZ
    have hw' : w.re=a:=hW
    exact hx.ne (hz'.trans hw'.symm)

def horocyclicFanTriangle (z w : ℍ) (hx :
  z.re<w.re) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle:=
  (horocyclicFanHTriangle z w hx).toDiscTriangle

theorem horocyclicFanTriangle_a (z w : ℍ) (hx : z.re<w.re) :
    (horocyclicFanTriangle z w hx).a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z):=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_on_interior z

theorem horocyclicFanTriangle_b (z w : ℍ) (hx : z.re<w.re) :
    (horocyclicFanTriangle z w hx).b=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w):=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_on_interior w

theorem horocyclicFanTriangle_c (z w : ℍ) (hx : z.re<w.re) :
    (horocyclicFanTriangle z w hx).c=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint:=rfl

theorem horocyclicFanTriangle_c_ideal (z w : ℍ) (hx : z.re<w.re) :
    ‖((horocyclicFanTriangle z w hx).c:ℂ)‖=1:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_ideal_norm _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint_ideal

/-- Its actual finite vertex angle is the native upward-ray angle already
 used in the exact one-period cotangent projection. -/
theorem horocyclicFanTriangle_alpha (z w : ℍ) (hx : z.re<w.re) :
    (horocyclicFanTriangle z w hx).alpha=
      horocyclicForwardAngle z w (fun he=>hx.ne (congrArg UpperHalfPlane.re he)) := by
  let T:=horocyclicFanTriangle z w hx
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w
  have ha : T.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel a:=horocyclicFanTriangle_a z w hx
  have hb : T.b=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel b:=horocyclicFanTriangle_b z w hx
  have hc : ‖(T.c:ℂ)‖=1:=horocyclicFanTriangle_c_ideal z w hx
  have hab : a≠b:=by
    intro he
    exact hx.ne (congrArg UpperHalfPlane.re
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective he))
  have hAB : T.cornerRayABAtA a ha=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRayThrough a b hab:=by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRayThrough_eq hab _ ?_).symm
    apply T.cornerAtA_sideC_finite_subset a ha
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel b∈T.sideC
    rw [←hb,T.mem_sideC_iff_coordinate,T.coordinate_b]
    norm_num
  have hAC : (T.cornerRayACAtA a ha).toHalfPlane=horocyclicUpwardRay (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane a):=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.idealEndpoint_injective
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.toHalfPlane_idealEndpoint,T.cornerRayACAtA_idealEndpoint a ha hc,
      horocyclicUpwardRay_endpoint]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint))=∞
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_toExtended,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm_apply_apply]
    rfl
  have hα : T.alpha=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure (horocyclicUpwardRay
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane a))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm.injective.ne hab)):=by
    rw [T.alpha_of_finite a ha,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure_eq_halfPlane,hAB,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRayThrough_toHalfPlane,hAC]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm _ _
  change T.alpha=horocyclicForwardAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
    a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane b) _ at hα
  simpa only [a,b,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using hα

/-- Reversing the two equal-height finite endpoints preserves the true
 native finite angle, without introducing prescribed triangle data. -/
theorem horocyclicForwardAngle_reverse (z w : ℍ) (hne : z≠w) (hy : w.im=z.im) :
    horocyclicForwardAngle z w hne=horocyclicForwardAngle w z hne.symm := by
  have hc1:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.upwardRay_angle_coordinates hne (horocyclicUpwardRay z)
    (horocyclicUpwardRay_endpoint z)).2
  have hc2:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.upwardRay_angle_coordinates hne.symm (horocyclicUpwardRay
    w) (horocyclicUpwardRay_endpoint w)).2
  have hL : 0<2*z.im*w.im*Real.sinh (dist z w):=by
    exact mul_pos (mul_pos (mul_pos (by norm_num) z.im_pos) w.im_pos)
      (Real.sinh_pos_iff.mpr (dist_pos.mpr hne))
  rw [dist_comm w z] at hc2
  rw [hy] at hc1 hc2 hL
  have hcos : Real.cos (horocyclicForwardAngle z w hne)=
      Real.cos (horocyclicForwardAngle w z hne.symm):=by
    dsimp only [horocyclicForwardAngle]
    nlinarith only [hc1,hc2,hL]
  exact Real.strictAntiOn_cos.injOn ⟨angle_nonneg _ _,angle_le_pi _ _⟩
    ⟨angle_nonneg _ _,angle_le_pi _ _⟩ hcos

/-- The other actual base angle is the same upward-ray construction at
 the neighboring original point, with the real geodesic pointing back. -/
theorem horocyclicFanTriangle_beta (z w : ℍ) (hx : z.re<w.re) :
    (horocyclicFanTriangle z w hx).beta=
      horocyclicForwardAngle w z (fun he=>hx.ne (congrArg UpperHalfPlane.re he.symm)) := by
  let T:=horocyclicFanTriangle z w hx
  let U:=T.cycle
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w
  have ha : T.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel a:=horocyclicFanTriangle_a z w hx
  have hb : U.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel b:=horocyclicFanTriangle_b z w hx
  have hc : ‖(U.b:ℂ)‖=1:=horocyclicFanTriangle_c_ideal z w hx
  have hab : a≠b:=by
    intro he
    exact hx.ne (congrArg UpperHalfPlane.re
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective he))
  have hBA : U.cornerRayACAtA b hb=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRayThrough b a hab.symm:=by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRayThrough_eq hab.symm _ ?_).symm
    apply U.cornerAtA_sideB_finite_subset b hb
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel a∈U.sideB
    rw [show _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel a=U.c from
      ha.symm,U.mem_sideB_iff_coordinate,U.coordinate_c]
    norm_num
  have hAB : (U.cornerRayABAtA b hb).toHalfPlane=horocyclicUpwardRay (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane b):=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.idealEndpoint_injective
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.toHalfPlane_idealEndpoint,U.cornerRayABAtA_idealEndpoint b hb hc,
      horocyclicUpwardRay_endpoint]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint))=∞
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_toExtended,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm_apply_apply]
    rfl
  have hβ : U.alpha=horocyclicForwardAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
    b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane a)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm.injective.ne hab.symm):=by
    unfold horocyclicForwardAngle
    rw [U.alpha_of_finite b hb,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure_eq_halfPlane,hBA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRayThrough_toHalfPlane,hAB]
  change U.alpha=_
  simpa only [a,b,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using hβ

/-- A genuine equal-height one-ideal fan triangle is isosceles at its
 two actual finite vertices; equality is derived from the real metric angles. -/
theorem horocyclicFanTriangle_alpha_eq_beta (z w : ℍ) (hx : z.re<w.re) (hy : w.im=z.im) :
    (horocyclicFanTriangle z w hx).alpha=(horocyclicFanTriangle z w hx).beta := by
  rw [horocyclicFanTriangle_alpha,horocyclicFanTriangle_beta]
  exact horocyclicForwardAngle_reverse z w _ hy

/-- The actual upward ray stays above its original starting height. -/
theorem horocyclicUpwardRay_im_ge (z u : ℍ) (hu : u∈(horocyclicUpwardRay z).val) :
    z.im≤u.im := by
  let R:=horocyclicUpwardRay z
  have hL : R.supportLine=.vertical z.re:=
    R.supportLine_of_idealEndpoint_infty (horocyclicUpwardRay_endpoint z)
  have hdir : R.longitudinal z<R.longitudinal R.directionPoint:=by
    by_contra hn
    have ht:=R.tangentVector_of_idealEndpoint_infty (horocyclicUpwardRay_endpoint z)
    have him:=congrArg Complex.im ht
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.tangentVector,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.tangentSign,hn,hL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.tangentAt] at him
    norm_num at him
  have hm:=(R.mem_iff_longitudinal (R.subset_support hu)).mp hu
  rw [ite_eq_left hdir] at hm
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.longitudinal,hL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.longitudinal,Complex.imCLM_apply,
    UpperHalfPlane.coe_im] using hm

/-- A genuine upward ray in a set supplies its genuine compactified infinity. -/
theorem horocyclic_infty_mem_closedModelClosure (z : ℍ) (S : Set ℍ)
    (hsub : (horocyclicUpwardRay z).val⊆S) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneClosedModelClosure S := by
  have hEnd : (∞:OnePoint ℂ)∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' (horocyclicUpwardRay z).val):=by
    have hh : (horocyclicUpwardRay z).idealEndpoint∈
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTraceIdealEndpoints (horocyclicUpwardRay z).val:=by
      rw [(horocyclicUpwardRay z).trace_idealEndpoint]
      exact mem_singleton _
    rw [horocyclicUpwardRay_endpoint] at hh
    exact hh.1
  have hh:=closure_mono (image_mono hsub) hEnd
  change (∞:OnePoint ℂ)∈closure ((fun u:ℍ=>((u:ℂ):OnePoint ℂ)) '' S) at hh
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneClosedModelClosure_ambient] at hh
  obtain ⟨p,hp,he⟩:=hh
  have hep : p=_root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint:=Subtype.ext he
  exact hep ▸ hp

/-- The actual one-ideal-vertex triangle lies inside every original closed
convex set containing its finite endpoints and its ideal limit point. -/
theorem horocyclicFanTriangle_finiteCarrier_subset (z w : ℍ) (hx : z.re<w.re)
    (S : Set ℍ) (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S) (hclosed : IsClosed S) (hz : z∈S) (hw
      : w∈S)
    (hi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneClosedModelClosure S) :
    (horocyclicFanTriangle z w hx).finiteCarrier⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S := by
  have hconv := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex S).mp hS
  have hza : (horocyclicFanTriangle z w hx).a∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S):=by
    rw [horocyclicFanTriangle_a]
    exact subset_closure (mem_image_of_mem _ (mem_image_of_mem _ hz))
  have hwb : (horocyclicFanTriangle z w hx).b∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S):=by
    rw [horocyclicFanTriangle_b]
    exact subset_closure (mem_image_of_mem _ (mem_image_of_mem _ hw))
  have hic : (horocyclicFanTriangle z w hx).c∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S):=by
    rw [horocyclicFanTriangle_c,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_image_closure]
    exact mem_image_of_mem _ hi
  have h:=closedTriangle_finiteCarrier_subset_closure _ _ hconv hza hwb hic
  have hs : IsClosed (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ''
    S):=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isClosedMap S hclosed
  rwa [hs.closure_eq] at h

/-- A one-ideal fan triangle is between its two actual vertical boundary lines. -/
theorem horocyclicFanTriangle_finiteCarrier_re_bounds (z w : ℍ) (hx : z.re<w.re)
    (u : Complex.UnitDisc) (hu : u∈(horocyclicFanTriangle z w hx).finiteCarrier) :
    z.re≤(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane u).re ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane u).re≤w.re := by
  let S : Set ℍ:={v | z.re≤v.re ∧ v.re≤w.re}
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S:=by
    intro v hv y hy u hu
    exact ⟨parabolicFord_hConvex_re_ge z.re v hv.1 y hy.1 hu,
      parabolicFord_hConvex_re_le w.re v hv.2 y hy.2 hu⟩
  have hs : IsClosed S:=
    (isClosed_le continuous_const UpperHalfPlane.continuous_re).inter
      (isClosed_le UpperHalfPlane.continuous_re continuous_const)
  have hz : z∈S:=⟨le_rfl,hx.le⟩
  have hw : w∈S:=⟨hx.le,le_rfl⟩
  have hi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneClosedModelClosure S:=by
    apply horocyclic_infty_mem_closedModelClosure z S
    intro v hv
    have hR:=(horocyclicUpwardRay z).subset_support hv
    rw [(horocyclicUpwardRay z).supportLine_of_idealEndpoint_infty
      (horocyclicUpwardRay_endpoint z)] at hR
    change v.re=z.re at hR
    exact ⟨hR.ge,hR.trans_le hx.le⟩
  obtain ⟨v,hv,he⟩:=horocyclicFanTriangle_finiteCarrier_subset z w hx S hc hs hz hw hi hu
  change z.re≤v.re ∧ v.re≤w.re at hv
  simpa only [←he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using hv

/-- Its genuine open interior stays strictly between the original vertical
boundary lines; no prescribed angular data is involved. -/
theorem horocyclicFanTriangle_interior_re_bounds (z w : ℍ) (hx : z.re<w.re)
    (u : Complex.UnitDisc) (hu : u∈(horocyclicFanTriangle z w hx).interior) :
    z.re<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane u).re ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane u).re<w.re := by
  let T:=horocyclicFanTriangle z w hx
  let f : Complex.UnitDisc→ℝ:=fun u=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane u).re
  have ho : IsOpen (f '' T.interior):=
    (UpperHalfPlane.isOpenMap_re.comp
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm.isOpenMap) _ T.interior_isOpen
  have hsub : f '' T.interior⊆Icc z.re w.re:=by
    rintro _ ⟨v,hv,rfl⟩
    exact horocyclicFanTriangle_finiteCarrier_re_bounds z w hx v
      (T.finiteCarrier_eq_closure ▸ subset_closure hv)
  have hm:=interior_maximal hsub ho (mem_image_of_mem f hu)
  rwa [interior_Icc] at hm

/-- Neighboring actual one-ideal fan triangles have disjoint genuine interiors. -/
theorem horocyclicFanTriangle_adjacent_disjoint (v z w : ℍ)
    (hv : v.re<z.re) (hw : z.re<w.re) :
    Disjoint (horocyclicFanTriangle v z hv).interior
      (horocyclicFanTriangle z w hw).interior := by
  apply Set.disjoint_left.mpr
  intro u hu hvu
  have hleft:=horocyclicFanTriangle_interior_re_bounds v z hv u hu
  have hright:=horocyclicFanTriangle_interior_re_bounds z w hw u hvu
  exact (not_lt_of_ge hright.1.le) hleft.2

/-- The true two adjacent base angles fit into the actual containing convex
sector at their common original finite point. -/
theorem horocyclicFanTriangle_adjacent_angle_le (v z w : ℍ)
    (hv : v.re<z.re) (hw : z.re<w.re) (S : Set ℍ) (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S)
    (hclosed : IsClosed S) (hvS : v∈S) (hzS : z∈S) (hwS : w∈S)
    (hi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneClosedModelClosure S) :
    (horocyclicFanTriangle v z hv).beta+(horocyclicFanTriangle z w hw).alpha≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) := by
  let T:=horocyclicFanTriangle v z hv
  let U:=horocyclicFanTriangle z w hw
  have hT : T.cycle.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z):=horocyclicFanTriangle_b v z hv
  have hU : U.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z):=horocyclicFanTriangle_a z w hw
  have hdis : Disjoint T.cycle.interior U.interior:=by
    rw [T.cycle_interior]
    exact horocyclicFanTriangle_adjacent_disjoint v z w hv hw
  have hsub : T.cycle.finiteCarrier⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S:=by
    rw [T.cycle.finiteCarrier_eq_closure,T.cycle_interior,←T.finiteCarrier_eq_closure]
    exact horocyclicFanTriangle_finiteCarrier_subset v z hv S hS hclosed hvS hzS hi
  exact cycle_two_triangle_angles_le T.cycle U _ _ hT hU hdis hsub
    (horocyclicFanTriangle_finiteCarrier_subset z w hw S hS hclosed hzS hwS hi)

/-- The actual Ford strip has infinity as a true compactified limit point,
 witnessed by its genuine high vertical ray. -/
theorem parabolicFordClosedStrip_infty_mem_closedModelClosure
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hd :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneClosedModelClosure (parabolicFordClosedStrip H) := by
  let z : ℍ:=⟨(1/2:ℂ)+2*Complex.I,by norm_num⟩
  have hzre : z.re=1/2:=by norm_num [z,UpperHalfPlane.re]
  have hzim : z.im=2:=by norm_num [z,UpperHalfPlane.im]
  apply horocyclic_infty_mem_closedModelClosure z
  intro u hu
  have hre:=(horocyclicUpwardRay z).subset_support hu
  rw [(horocyclicUpwardRay z).supportLine_of_idealEndpoint_infty
    (horocyclicUpwardRay_endpoint z)] at hre
  change u.re=z.re at hre
  have him:=horocyclicUpwardRay_im_ge z u hu
  rw [hzim] at him
  refine ⟨?_,?_,parabolicFord_high_im_exterior H hd hT u (by linarith only [him])⟩
  · rw [hre,hzre];norm_num
  · rw [hre,hzre];norm_num

/-- Genuine fan triangles in the original Ford strip stay inside the actual
closed original Ford polygon. -/
theorem parabolicFord_horocyclicFanTriangle_subset
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hd :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) (z w : ℍ) (hx : z.re<w.re)
    (hz : z∈parabolicFordClosedStrip H) (hw : w∈parabolicFordClosedStrip H) :
    (horocyclicFanTriangle z w hx).finiteCarrier⊆
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' closure (parabolicFordDomain H) := by
  rw [closure_parabolicFordDomain H hd hT]
  exact horocyclicFanTriangle_finiteCarrier_subset z w hx _
    (parabolicFordClosedStrip_hConvex H hd hT) (parabolicFordClosedStrip_isClosed H) hz hw
    (parabolicFordClosedStrip_infty_mem_closedModelClosure H hd hT)

/-- The actual adjacent Ford triangle angles have the genuine original
polygon-sector budget, derived from the true Ford domain geometry. -/
theorem parabolicFord_horocyclicFanTriangle_adjacent_angle_le
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hd :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) (v z w : ℍ) (hv : v.re<z.re) (hw
      : z.re<w.re)
    (hvS : v∈parabolicFordClosedStrip H) (hzS : z∈parabolicFordClosedStrip H)
    (hwS : w∈parabolicFordClosedStrip H) :
    (horocyclicFanTriangle v z hv).beta+(horocyclicFanTriangle z w hw).alpha≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' closure (parabolicFordDomain H)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) := by
  rw [closure_parabolicFordDomain H hd hT]
  exact horocyclicFanTriangle_adjacent_angle_le v z w hv hw _
    (parabolicFordClosedStrip_hConvex H hd hT) (parabolicFordClosedStrip_isClosed H) hvS hzS hwS
    (parabolicFordClosedStrip_infty_mem_closedModelClosure H hd hT)

end LowDimensionalTopology.Geometry.Fuchsian
