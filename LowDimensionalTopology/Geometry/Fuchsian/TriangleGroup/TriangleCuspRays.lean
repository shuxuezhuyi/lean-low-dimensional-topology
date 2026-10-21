/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleIdealLabels
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.ClosedSegmentTransport
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  Set
  Filter
  Topology
open scoped UpperHalfPlane Complex.UnitDisc OnePoint

/-- Every noninitial point of the actual vertex-to-interior closed geodesic segment is inside the original triangle. -/
theorem closedDiscTriangle_vertex_segment_inside
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle)
    (p q:𝔻)
    (hp:p∈T.interior) (hq:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q≠T.a)
    (hs:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment T.a (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel p)) : q∈T.interior := by
  have hpH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane p∈T.halfPlaneInterior:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane p)∈T.interior
    rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  have hpF:T.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel p)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.standardOpenTriangle:=by
    have h:=(T.mem_halfPlaneInterior_iff (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane p)).mp hpH
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.halfPlaneCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.discCoordinate,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.standardOpenTriangle,mem_ofPred_eq] using h
  rw [T.mem_closedSegment_iff_coordinate,T.coordinate_a] at hs
  obtain ⟨a,b,ha,hb,hab,he⟩:=hs
  have hbpos:0<b:=lt_of_le_of_ne hb (by
    intro hz
    apply hq
    apply T.coordinate_injective
    rw [T.coordinate_a,←he,←hz]
    simp)
  have hqF:T.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.standardOpenTriangle:=by
    rw [←he]
    have hp1:=hpF.1
    have hp2:=hpF.2.1
    have hpsum:=hpF.2.2
    change 0<(a•(0,0)+b•T.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel p)).1 ∧
      0<(a•(0,0)+b•T.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel p)).2 ∧
      (a•(0,0)+b•T.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel p)).1+
        (a•(0,0)+b•T.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel p)).2<1
    dsimp only [Prod.smul_fst,Prod.smul_snd,Prod.fst_add,Prod.snd_add,smul_eq_mul]
    simp only [mul_zero,zero_add]
    exact ⟨mul_pos hbpos hp1,mul_pos hbpos hp2,by nlinarith [mul_pos hbpos (sub_pos.mpr hpsum)]⟩
  have hqH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane q∈T.halfPlaneInterior:=by
    rw [T.mem_halfPlaneInterior_iff]
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.halfPlaneCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.discCoordinate,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.standardOpenTriangle,mem_ofPred_eq] using hqF
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane q)∈T.interior at hqH
  rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane] at hqH

/-- An actual vertical tail has its genuine Klein convex-combination parameter towards its ideal endpoint. -/
theorem halfPlaneKlein_vertical_tail (p q:ℍ) (hRe:q.re=p.re) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate q=(1-(p.re^2+p.im^2+1)/(q.re^2+q.im^2+1))•(1:ℂ)+
      ((p.re^2+p.im^2+1)/(q.re^2+q.im^2+1))•_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate p := by
  have hD:q.re^2+q.im^2+1≠0:=by positivity
  have hDp:p.re^2+p.im^2+1≠0:=by positivity
  apply Complex.ext
  all_goals simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_explicit,Complex.add_re,Complex.add_im,
    Complex.real_smul,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.one_re,Complex.one_im,zero_mul,mul_zero,sub_zero,
    add_zero,zero_add]
  all_goals rw [hRe]; field_simp
  all_goals ring


/-- Every genuine vertical height tail lies in the compactified geodesic from its base to infinity. -/
theorem halfPlane_vertical_tail_closed_segment (p q:ℍ) (hRe:q.re=p.re) (hIm:p.im≤q.im) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc q)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (1:𝕔𝔻)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc p)) := by
  let e:ℝ:=(p.re^2+p.im^2+1)/(q.re^2+q.im^2+1)
  have he:0<e:=by dsimp [e];positivity
  have he1:e≤1:=by
    apply (div_le_one (by positivity :0<q.re^2+q.im^2+1)).mpr
    rw [hRe]
    nlinarith [p.im_pos,q.im_pos]
  have h1:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (1:𝕔𝔻)=1:=by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein (1:𝕔𝔻):ℂ)=1
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed _ (by simp)]
    rfl
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
  refine ⟨1-e,e,by linarith,he.le,by ring,?_⟩
  rw [h1]
  exact (halfPlaneKlein_vertical_tail p q hRe).symm

/-- Height tending to infinity has the actual ideal limit in the original one-point sphere topology. -/
theorem halfPlane_height_tendsto_infty {ι:Type*} {l:Filter ι} (f:ι→ℍ)
    (hf:Tendsto (fun i=>(f i).im) l atTop) :
    Tendsto (fun i=>_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (f i)) l (𝓝 (∞:Mobius.ExtendedComplex)) := by
  have hn:Tendsto (fun i=>‖(f i:ℂ)‖) l atTop:=
    tendsto_atTop_mono (fun i=>(le_abs_self (f i).im).trans (Complex.abs_im_le_norm _)) hf
  have hc:Tendsto (fun i=>(f i:ℂ)) l (cocompact ℂ):=
    (tendsto_norm_atTop_iff_cobounded.mp hn).mono_right Metric.cobounded_le_cocompact
  exact OnePoint.tendsto_coe_infty.comp (hc.mono_right cocompact_le_coclosedCompact)


theorem realSLMobius_image_closed_model (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHalfPlaneSet := by
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closure_openHalfPlaneSet]
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) '' closure _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=closure _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
  rw [(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)).image_closure]
  exact congrArg closure (realSLMobius_image_openHalfPlane A)

def realSLCuspClosedModel (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel≃ₜ_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel :=
  (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)).subtype (fun p=>by
    conv_rhs=>rw [←realSLMobius_image_closed_model A]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val.injective.mem_set_image.symm)

theorem realSLCuspClosedModel_finite (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (z:ℍ) :
    realSLCuspClosedModel A (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel z)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (A•z) :=
  Subtype.ext (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A z)

def realSLCuspDiscIsometry
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry where
  finiteMap z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (A•_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)
  distance_eq:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIsometry_native_distance (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A).isometry
  closedMap:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm.trans ((realSLCuspClosedModel A).trans _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph)
  finite_commutes z:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph (realSLCuspClosedModel A
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)))=_
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_inverse_finite,
      realSLCuspClosedModel_finite, _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_on_interior]

theorem realSLCuspDiscIsometry_finite (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (z:ℍ) :
    (realSLCuspDiscIsometry A).closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (A•z)) := by
  rw [(realSLCuspDiscIsometry A).finite_commutes]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (A•_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)))=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]

theorem realSLCuspDiscIsometry_ideal_vertex
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val T.a.val=∞) : (realSLCuspDiscIsometry A).closedMap T.toDiscTriangle.a=1 := by
  have he: (realSLCuspDiscIsometry A).closedMap T.toDiscTriangle.a=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph (realSLCuspClosedModel A T.a):=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph (realSLCuspClosedModel A
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph T.a)))=_
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm_apply_apply]
  rw [he]
  apply Complex.UnitClosedDisc.coe_injective
  apply OnePoint.coe_injective
  have hc:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_toExtended (realSLCuspClosedModel A T.a)
  change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph (realSLCuspClosedModel A T.a):ℂ):Mobius.ExtendedComplex)=_
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph (realSLCuspClosedModel A T.a))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (1:𝕔𝔻)
  rw [hc]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val T.a.val)=_
  rw [hA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_infty]
  rfl

theorem closedTriangle_native_cusp_ray_inside
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hα:T.alpha=0)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val T.a.val=∞)
    (p q:ℍ) (hp:p∈T.interior) (hRe:(A•q:ℍ).re=(A•p:ℍ).re)
    (hIm:(A•p:ℍ).im≤(A•q:ℍ).im) : q∈T.interior := by
  let E:=realSLCuspDiscIsometry A
  have hs:=halfPlane_vertical_tail_closed_segment (A•p) (A•q) hRe hIm
  rw [←realSLCuspDiscIsometry_ideal_vertex T A hA,
    ←realSLCuspDiscIsometry_finite A p,←realSLCuspDiscIsometry_finite A q,
    ←E.image_closedModelDiscHSegment] at hs
  have hs':_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc q)∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment T.toDiscTriangle.a (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc p)):=
    E.closedMap.injective.mem_set_image.mp hs
  have hI:‖(T.toDiscTriangle.a:ℂ)‖=1:=T.toDiscTriangle.alpha_eq_zero_iff_ideal.mp hα
  have hq:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc q)≠T.toDiscTriangle.a:=by
    intro he
    have hn:=congrArg (fun x:𝕔𝔻=>‖(x:ℂ)‖) he
    have hpq:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc q).norm_lt_one
    change ‖(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc q:ℂ)‖=‖(T.toDiscTriangle.a:ℂ)‖ at hn
    rw [hn,hI] at hpq
    exact lt_irrefl _ hpq
  exact closedDiscTriangle_vertex_segment_inside T.toDiscTriangle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc q)
    hp hq hs'

end LowDimensionalTopology.Geometry.Fuchsian
