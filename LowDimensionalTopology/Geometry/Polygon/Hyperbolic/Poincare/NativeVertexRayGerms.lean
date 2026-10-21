/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Quotient.PolygonVertexAngularMultiplicity
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.ClosedSegmentTransport
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeSideArms
public import LowDimensionalTopology.Geometry.Polygon.Topology.Jordan.JordanEndpointExclusion
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- At a nondegenerate endpoint, the actual Euclidean closed segment has the
germ of its literal forward ray. -/
theorem complex_segment_zero_ray_germ {v : ℂ} (hv : v≠0) :
    ∀ᶠz in 𝓝 (0 : ℂ),z∈segment ℝ 0 v ↔
      ∃t : ℝ,0≤t ∧z=(t : ℂ)*v := by
  have hn : 0<‖v‖:=norm_pos_iff.mpr hv
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hn] with z hz
  have hzN : ‖z‖<‖v‖:=by simpa only [Metric.mem_ball,dist_zero_right] using hz
  rw [segment_eq_image]
  constructor
  · rintro ⟨t,ht,he⟩
    refine ⟨t,ht.1,?_⟩
    simpa only [smul_zero,zero_add,Complex.real_smul] using he.symm
  · rintro ⟨t,ht,rfl⟩
    have ht1 : t<1:=by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht] at hzN
      nlinarith
    refine ⟨t,⟨ht,ht1.le⟩,?_⟩
    simp only [smul_zero,zero_add,Complex.real_smul]

/-- Positive radial scalar factors preserve the actual forward-ray relation. -/
theorem complex_positive_rescaling_ray_iff (z v : ℂ) (c d : ℝ)
    (hc : 0<c) (hd : 0<d) :
    (∃t : ℝ,0≤t ∧(c : ℂ)*z=(t : ℂ)*((d : ℂ)*v)) ↔
      ∃t : ℝ,0≤t ∧z=(t : ℂ)*v := by
  constructor
  · rintro ⟨t,ht,he⟩
    refine ⟨t*d/c,div_nonneg (mul_nonneg ht hd.le) hc.le,?_⟩
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne')
    rw [he]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hc.ne']
  · rintro ⟨t,ht,rfl⟩
    refine ⟨c*t/d,div_nonneg (mul_nonneg hc.le ht) hd.le,?_⟩
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hd.ne']

/-- A genuine compactified native h-segment issuing from the disc origin has
its actual Euclidean radial-ray germ, for both finite and ideal other endpoints. -/
theorem closedModelDiscHSegment_zero_ray_germ (p : 𝕔𝔻) (hp : (p : ℂ)≠0) :
    ∀ᶠz in 𝓝 (0 : 𝔻),_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel 0) p ↔
      ∃t : ℝ,0≤t ∧(z : ℂ)=(t : ℂ)*(p : ℂ) := by
  let K : 𝔻→ℂ:=fun z=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
  have hK : Continuous K:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_kleinCoordinate
  have hK0 : K 0=0:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (0 : ℂ)=0
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,mul_zero]
  have hpK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p≠0:=by
    change ((2/(1+‖(p : ℂ)‖^2) : ℝ) : ℂ)*(p : ℂ)≠0
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) hp
  have hT : Tendsto K (𝓝 (0 : 𝔻)) (𝓝 (0 : ℂ)):=hK0 ▸ hK.continuousAt
  filter_upwards [hT.eventually (complex_segment_zero_ray_germ hpK)] with z hz
  have hMem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel 0) p ↔
      K z∈segment ℝ 0 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) := by
    have hImage:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel 0) p
    have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel 0)=0:=hK0
    rw [he] at hImage
    rw [←hImage]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.symm
  rw [hMem,hz]
  exact complex_positive_rescaling_ray_iff z p (2/(1+‖(z : ℂ)‖^2))
    (2/(1+‖(p : ℂ)‖^2)) (by positivity) (by positivity)

/-- The genuine native origin normalizer extends to the actual closed disc. -/
def nativeOriginClosedDiscIsometry (p : ℍ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.ofPathIsometry
    (fun z=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry p.toSL2R⁻¹
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIsometry_native_distance
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry p.toSL2R⁻¹).isometry)

theorem nativeOriginClosedDiscIsometry_finite (p x : ℍ) :
    (nativeOriginClosedDiscIsometry p).finiteMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)=
      nativeAngularOriginChart p x := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry p.toSL2R⁻¹ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)))=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  rfl

/-- The true finite/ideal original side is mapped to its exact compactified
h-segment by the actual native isometric coordinate at any chosen center. -/
theorem NativeGeodesicSideIntervals.origin_chart_side
    {P : PoincarePolygon ℍ} (D : NativeGeodesicSideIntervals P) (p : ℍ) (s : P.Side) :
    nativeAngularOriginChart p '' s.val=
      {z : 𝔻 | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment
        ((nativeOriginClosedDiscIsometry p).closedMap (D.startPoint s))
        ((nativeOriginClosedDiscIsometry p).closedMap (D.endPoint s))} := by
  let E:=nativeOriginClosedDiscIsometry p
  have himg:=E.image_closedModelDiscHSegment (D.startPoint s) (D.endPoint s)
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (nativeAngularOriginChart p
      x)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment
      (E.closedMap (D.startPoint s)) (E.closedMap (D.endPoint s))
    rw [←himg]
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x),?_,?_⟩
    · change x∈nativeCompactifiedSide (D.startPoint s) (D.endPoint s)
      rwa [←D.side_eq s]
    · rw [E.finite_commutes,nativeOriginClosedDiscIsometry_finite]
  · intro hz
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment
      (E.closedMap (D.startPoint s)) (E.closedMap (D.endPoint s)) at hz
    rw [←himg] at hz
    obtain ⟨q,hq,he⟩:=hz
    let x:=(nativeAngularOriginChart p).symm z
    have hxz : nativeAngularOriginChart p x=z:=(nativeAngularOriginChart p).apply_symm_apply z
    have hEx : E.closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := by
      rw [E.finite_commutes,nativeOriginClosedDiscIsometry_finite,hxz]
    have hqEq : q=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x):=E.closedMap.injective (he.trans hEx.symm)
    refine ⟨x,?_,hxz⟩
    rw [D.side_eq s]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (D.startPoint s) (D.endPoint s)
    rwa [hqEq] at hq

/-- At either actual native endpoint, the side normalizes to a nondegenerate
closed h-segment with one endpoint at the actual disc origin. -/
theorem NativeGeodesicSideIntervals.origin_endpoint_segment
    {P : PoincarePolygon ℍ} (D : NativeGeodesicSideIntervals P) (p : ℍ) (s : P.Side)
    (hp : p∈D.endpoints s) :
    ∃q : 𝕔𝔻,(q : ℂ)≠0 ∧nativeAngularOriginChart p '' s.val=
      {z : 𝔻 | _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel 0) q} := by
  let E:=nativeOriginClosedDiscIsometry p
  have hZero : E.closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc p))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel 0 := by
    rw [E.finite_commutes,nativeOriginClosedDiscIsometry_finite,nativeAngularOriginChart_apply_self]
  have hNz {q r : 𝕔𝔻} (hne : q≠r) (hr : r=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel 0) : (q : ℂ)≠0 := by
    intro hz
    apply hne
    rw [hr]
    apply Subtype.ext
    exact hz
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc p)∈({D.startPoint s,D.endPoint s}:Set 𝕔𝔻) at hp
  rcases hp with hp|hp
  · have hs : E.closedMap (D.startPoint s)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel 0:=by
      rw [←hp]
      exact hZero
    refine ⟨E.closedMap (D.endPoint s),hNz (E.closedMap.injective.ne (D.endpoint_ne s).symm) hs,?_⟩
    rw [D.origin_chart_side p s,hs]
  · have hs : E.closedMap (D.endPoint s)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel 0:=by
      rw [←hp]
      exact hZero
    refine ⟨E.closedMap (D.startPoint s),hNz (E.closedMap.injective.ne (D.endpoint_ne s)) hs,?_⟩
    have hComm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (E.closedMap (D.startPoint
      s)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel 0)=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel 0) (E.closedMap (D.startPoint s)) := by
      apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.image_injective
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment,segment_symm]
    rw [D.origin_chart_side p s,hs,hComm]

/-- Every actual native endpoint side has the germ of one true unit-direction
ray in the genuine isometric coordinate at that endpoint. -/
theorem NativeGeodesicSideIntervals.origin_endpoint_ray_germ
    {P : PoincarePolygon ℍ} (D : NativeGeodesicSideIntervals P) (p : ℍ) (s : P.Side)
    (hp : p∈D.endpoints s) :
    ∃u : Circle,∀ᶠz in 𝓝 (0 : 𝔻),z∈nativeAngularOriginChart p '' s.val ↔
      ∃t : ℝ,0≤t ∧(z : ℂ)=(t : ℂ)*(u : ℂ) := by
  obtain ⟨q,hq,hImage⟩:=D.origin_endpoint_segment p s hp
  let u:=Circle.exp (Complex.arg (q : ℂ))
  have hu : (‖(q : ℂ)‖ : ℂ)*(u : ℂ)=(q : ℂ):=by
    simpa only [u,Circle.coe_exp] using Complex.norm_mul_exp_arg_mul_I (q : ℂ)
  refine ⟨u,?_⟩
  filter_upwards [closedModelDiscHSegment_zero_ray_germ q hq] with z hz
  rw [hImage]
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel 0) q) ↔_
  rw [hz,←hu]
  simpa only [Complex.ofReal_one,one_mul] using
    complex_positive_rescaling_ray_iff (z : ℂ) (u : ℂ) 1 ‖(q : ℂ)‖ (by norm_num) (norm_pos_iff.mpr hq)

/-- Two distinct original sides cannot give the same true ray germ at an
actual original vertex: their literal common points are isolated original endpoints. -/
theorem NativeGeodesicSideIntervals.origin_incident_ray_germs_distinct
    {P : PoincarePolygon ℍ} (D : NativeGeodesicSideIntervals P) (p : ℍ)
    (hp : p∈D.vertices) (s t : P.Side) (hst : s≠t) (u v : Circle)
    (hu : ∀ᶠz in 𝓝 (0 : 𝔻),z∈nativeAngularOriginChart p '' s.val ↔
      ∃r : ℝ,0≤r ∧(z : ℂ)=(r : ℂ)*(u : ℂ))
    (hv : ∀ᶠz in 𝓝 (0 : 𝔻),z∈nativeAngularOriginChart p '' t.val ↔
      ∃r : ℝ,0≤r ∧(z : ℂ)=(r : ℂ)*(v : ℂ)) : u≠v := by
  intro he
  subst v
  let F:=nativeAngularOriginChart p
  have hF0 : F p=0:=nativeAngularOriginChart_apply_self p
  have hSymm0 : F.symm 0=p:=by
    apply F.injective
    rw [F.apply_symm_apply,hF0]
  have hIso : ∀ᶠx in 𝓝 p,x∈D.vertices →x=p := by
    have hS : ({p}:Set ℍ)∈𝓝[D.vertices] p:=by
      rw [D.vertices_discrete.nhdsWithin p hp]
      simp only [mem_pure,mem_singleton_iff]
    change {x : ℍ | x∈D.vertices →x=p}∈𝓝 p
    simpa only [mem_singleton_iff] using Filter.mem_inf_principal.mp hS
  have hT : Tendsto F.symm (𝓝 (0 : 𝔻)) (𝓝 p):=hSymm0 ▸F.symm.continuous.continuousAt
  have hNear : ∀ᶠz in 𝓝 (0 : 𝔻),
      (z∈F '' s.val ↔∃r : ℝ,0≤r ∧(z : ℂ)=(r : ℂ)*(u : ℂ)) ∧
      (z∈F '' t.val ↔∃r : ℝ,0≤r ∧(z : ℂ)=(r : ℂ)*(u : ℂ)) ∧
      (F.symm z∈D.vertices →F.symm z=p) := by
    filter_upwards [hu,hv,hT.eventually hIso] with z hs ht hi
    exact ⟨hs,ht,hi⟩
  obtain ⟨n,hs,ht,hi⟩:=((_root_.LowDimensionalTopology.Geometry.Hyperbolic.tendsto_discRadialTestPoint u).eventually
    hNear).exists
  let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialTestRadius n) u
  have hRay : ∃r : ℝ,0≤r ∧(z : ℂ)=(r : ℂ)*(u : ℂ):=
    ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialTestRadius
      n).val,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialTestRadius n).property.1.le,rfl⟩
  have hPre {A : Set ℍ} (h : z∈F '' A) : F.symm z∈A := by
    obtain ⟨x,hx,he⟩:=h
    rw [←he,F.symm_apply_apply]
    exact hx
  have hxs:=hPre (hs.mpr hRay)
  have hxt:=hPre (ht.mpr hRay)
  have hxV : F.symm z∈D.vertices:=
    mem_iUnion.mpr ⟨s,D.side_intersection s t hst _ hxs hxt⟩
  have hz0 : z=0:=by
    have h:=congrArg F (hi hxV)
    simpa only [F.apply_symm_apply,hF0] using h
  have hn:=congrArg (fun w : 𝔻=>‖(w : ℂ)‖) hz0
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint_norm] at hn
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialTestRadius n).property.1.ne' (by simpa only [Complex.UnitDisc.coe_zero,norm_zero] using hn)

/-- The actual native boundary at every original Jordan vertex is, in its
genuine isometric origin chart, precisely two distinct actual forward-ray germs. -/
theorem NativeGeodesicSideIntervals.vertex_origin_boundary_two_rays
    {P : PoincarePolygon ℍ} (D : NativeGeodesicSideIntervals P)
    (C : Set ℂ) (hC : IsComplexJordanCurve C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (p : ℍ) (hp : p∈D.vertices) :
    ∃u v : Circle,u≠v ∧∀ᶠz in 𝓝 (0 : 𝔻),
      z∈nativeAngularOriginChart p '' P.boundary ↔
        (∃r : ℝ,0≤r ∧(z : ℂ)=(r : ℂ)*(u : ℂ)) ∨
        (∃r : ℝ,0≤r ∧(z : ℂ)=(r : ℂ)*(v : ℂ)) := by
  let F:=nativeAngularOriginChart p
  obtain ⟨s,t,hst,hps,hpt,hEx⟩:=D.vertex_exactly_two_incident_sides C hC hBoundary p hp
  obtain ⟨u,hu⟩:=D.origin_endpoint_ray_germ p s (D.vertex_on_side_endpoint p hp s hps)
  obtain ⟨v,hv⟩:=D.origin_endpoint_ray_germ p t (D.vertex_on_side_endpoint p hp t hpt)
  refine ⟨u,v,D.origin_incident_ray_germs_distinct p hp s t hst u v hu hv,?_⟩
  let pP : P.Point:=⟨p,P.side_subset_carrier s hps⟩
  obtain ⟨r,hr,hAvoid⟩:=PoincareSidePairing.exists_ball_incident_sides
    D.locallyFinite D.side_geometry.side_closed pP
  have hF0 : F p=0:=nativeAngularOriginChart_apply_self p
  have hSymm0 : F.symm 0=p:=by
    apply F.injective
    rw [F.apply_symm_apply,hF0]
  have hT : Tendsto F.symm (𝓝 (0 : 𝔻)) (𝓝 p):=hSymm0 ▸F.symm.continuous.continuousAt
  filter_upwards [hu,hv,hT.eventually (Metric.ball_mem_nhds p hr)] with z hsu htv hz
  constructor
  · rintro ⟨q,hq,rfl⟩
    have hqNear : q∈Metric.ball p r:=by
      change F.symm (F q)∈Metric.ball p r at hz
      simpa only [F.symm_apply_apply] using hz
    obtain ⟨w,hw,hqw⟩:=mem_sUnion.mp hq
    let w' : P.Side:=⟨w,hw⟩
    have hpw : p∈w'.val:=hAvoid q hqNear w' hqw
    rcases hEx w' hpw with hws|hwt
    · apply Or.inl
      apply hsu.mp
      exact ⟨q,hws ▸hqw,rfl⟩
    · apply Or.inr
      apply htv.mp
      exact ⟨q,hwt ▸hqw,rfl⟩
  · intro h
    rcases h with hu|hv
    · exact image_mono (P.side_subset_boundary s) (hsu.mpr hu)
    · exact image_mono (P.side_subset_boundary t) (htv.mpr hv)

/-- The actual original inside and actual exterior remain two open regions
with their true common original boundary in the native isometric origin chart. -/
theorem NativeGeodesicPolygonGeometry.origin_corner_regions
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (p : ℍ) (hp : p∈P.boundary) :
    let F:=nativeAngularOriginChart p
    IsOpen (F '' P.interior) ∧IsOpen (F '' P.carrierᶜ) ∧
      Disjoint (F '' P.interior) (F '' P.carrierᶜ) ∧
      (F '' P.interior)∪(F '' P.carrierᶜ)=(F '' P.boundary)ᶜ ∧
      (0 : 𝔻)∈frontier (F '' P.interior) ∧(0 : 𝔻)∈frontier (F '' P.carrierᶜ) := by
  let F:=nativeAngularOriginChart p
  have hClosed : IsClosed P.carrier:=by rw [G.carrier_closure];exact isClosed_closure
  have hF0 : F p=0:=nativeAngularOriginChart_apply_self p
  have hOFront : frontier (P.carrierᶜ)=P.boundary := by
    rw [frontier_compl,G.carrier_closure,frontier,closure_closure,G.regular_open]
    simpa only [frontier,G.interior_open.interior_eq] using G.frontier_boundary
  refine ⟨F.isOpenMap _ G.interior_open,F.isOpenMap _ hClosed.isOpen_compl,?_,?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,he⟩ ⟨y,hy,he'⟩
    have hxy : x=y:=F.injective (he.trans he'.symm)
    exact hy (hxy ▸P.interior_subset_carrier hx)
  · ext z
    obtain ⟨x,rfl⟩:=F.surjective z
    change ((F x∈F '' P.interior) ∨(F x∈F '' P.carrierᶜ)) ↔F x∉F '' P.boundary
    rw [F.injective.mem_set_image,F.injective.mem_set_image,F.injective.mem_set_image]
    change (x∈P.interior ∨x∉P.carrier) ↔x∉P.boundary
    have hdis:=P.disjoint
    change Disjoint P.interior P.boundary at hdis
    constructor
    · rintro (hx|hx)
      · exact fun hb=>Set.disjoint_left.mp hdis hx hb
      · exact fun hb=>hx (Or.inr hb)
    · intro hb
      by_cases hx : x∈P.interior
      · exact Or.inl hx
      · apply Or.inr
        intro hc
        rcases hc with hi|hxb
        · exact hx hi
        · exact hb hxb
  · rw [←F.image_frontier,G.frontier_boundary]
    exact ⟨p,hp,hF0⟩
  · rw [←F.image_frontier,hOFront]
    exact ⟨p,hp,hF0⟩
end LowDimensionalTopology.Geometry.Polygon
