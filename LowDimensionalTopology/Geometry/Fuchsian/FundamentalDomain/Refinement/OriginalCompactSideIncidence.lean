/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Refinement.OriginalSideEndpoints
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletGeometry
public import Mathlib.Analysis.Convex.StrictConvexSpace
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Genuine native isometries preserve strict betweenness in actual Klein coordinates. -/
theorem original_normalizedKlein_between {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (x a b:P.domain.carrier) (hab:a≠b)
    (hx:P.kleinCoordinate x∈openSegment ℝ (P.kleinCoordinate a) (P.kleinCoordinate b)) :
    normalizedPolygonKleinCoordinate P x x∈openSegment ℝ
      (normalizedPolygonKleinCoordinate P x a) (normalizedPolygonKleinCoordinate P x b) := by
  let :=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  have hxa : x≠a:=by
    intro he; subst x
    exact hab (P.kleinCoordinate_isOpenEmbedding.injective (left_mem_openSegment_iff.mp hx))
  have hxb : x≠b:=by
    intro he; subst x
    exact hab (P.kleinCoordinate_isOpenEmbedding.injective (right_mem_openSegment_iff.mp hx))
  have hxseg : P.finiteCoordinate x∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHSegment (P.finiteCoordinate a) (P.finiteCoordinate b):=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective.mem_set_image.mp
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.klein_image_closedDiscHSegment]
    exact openSegment_subset_segment ℝ _ _ hx
  let f:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate x)
  have hf:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry (P.finiteCoordinate x)
  have hxmap : f (P.finiteCoordinate x)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHSegment
      (f (P.finiteCoordinate a)) (f (P.finiteCoordinate b)):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_isometry_image_closedHSegment hf
      (P.finiteCoordinate.injective.ne hab)]
    exact mem_image_of_mem f hxseg
  have hxnorm : normalizedPolygonKleinCoordinate P x x∈segment ℝ
      (normalizedPolygonKleinCoordinate P x a) (normalizedPolygonKleinCoordinate P x b):=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (f (P.finiteCoordinate x))∈segment ℝ
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (f (P.finiteCoordinate
        a))) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (f (P.finiteCoordinate b)))
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.klein_image_closedDiscHSegment]
    exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate hxmap
  exact mem_openSegment_of_ne_left_right
    ((normalizedPolygonKleinCoordinate_isOpenEmbedding P x).injective.ne hxa.symm)
    ((normalizedPolygonKleinCoordinate_isOpenEmbedding P x).injective.ne hxb.symm) hxnorm


/-- The literal open-disc points of the original compact Klein side remain the original side points. -/
theorem original_side_klein_closure_mem {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (s:FuchsianPolygonSides P D) (x:P.domain.carrier)
    (hx:P.kleinCoordinate x∈closure (P.kleinCoordinate '' s.val)) : x∈s.val := by
  have hm : x∈closure s.val:=by
    rw [P.kleinCoordinate_isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image]
    exact hx
  rwa [(fuchsian_polygon_side_isClosed s).closure_eq] at hm

/-- A strict point of an actual compactified side segment cannot be an original finite vertex. The two nearby genuine finite side points are constructed, not supplied. -/
theorem original_side_vertex_eq_closed_endpoint {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (s:FuchsianPolygonSides P D)
    (p q:𝕔𝔻) (hpq:p≠q) (hs:fuchsianSideClosedModel
      s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q)
    (x:P.domain.carrier) (hx:x∈s.val) (hv:IsFuchsianPolygonVertex P D x) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)=p∨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)=q := by
  by_contra hnot
  push Not at hnot
  have hkpq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hpq
  have hxseg : P.kleinCoordinate x∈segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment,←hs]
    exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ((mem_fuchsianSideClosedModel_finite s x).mpr hx)
  have hxp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p≠P.kleinCoordinate x:=by
    intro he
    apply hnot.1
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective he.symm
  have hxq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q≠P.kleinCoordinate x:=by
    intro he
    apply hnot.2
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective he.symm
  have hxopen:=mem_openSegment_of_ne_left_right hxp hxq hxseg
  let f:ℂ→ᵃ[ℝ] ℂ:=AffineMap.homothety (P.kleinCoordinate x) (1/2:ℝ)
  have hfself : f (P.kleinCoordinate x)=P.kleinCoordinate x:=AffineMap.homothety_apply_same _ _
  have hfform (y:ℂ) : f y=(1/2:ℝ) • y+(1/2:ℝ) • P.kleinCoordinate x:=by
    simp only [f,AffineMap.homothety_apply,vsub_eq_sub,vadd_eq_add,smul_sub]
    module
  have hfx (y:ℂ) (hy:‖y‖≤1) : f y∈Metric.ball (0:ℂ) 1:=by
    have hxB : P.kleinCoordinate x∈Metric.ball (0:ℂ) 1:=P.kleinCoordinate_range ▸ mem_range_self x
    have hxnorm : ‖P.kleinCoordinate x‖<1:=mem_ball_zero_iff.mp hxB
    have hbound:=norm_add_le ((1/2:ℝ) • y) ((1/2:ℝ) • P.kleinCoordinate x)
    rw [norm_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)] at hbound
    rw [mem_ball_zero_iff,hfform]
    linarith
  obtain ⟨a,ha⟩:=(P.kleinCoordinate_range ▸ hfx (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein p).norm_le_one)
  obtain ⟨b,hb⟩:=(P.kleinCoordinate_range ▸ hfx (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    q) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein q).norm_le_one)
  have hopen : P.kleinCoordinate x∈openSegment ℝ (P.kleinCoordinate a) (P.kleinCoordinate b):=by
    rw [ha,hb,←image_openSegment]
    exact ⟨P.kleinCoordinate x,hxopen,hfself⟩
  have hab : a≠b:=by
    intro he
    have hfi : Function.Injective f:=AffineMap.homothety_injective (P.kleinCoordinate x) (by norm_num : (1/2:ℝ)≠0)
    exact hkpq (hfi (ha.symm.trans ((congrArg P.kleinCoordinate he).trans hb)))
  have haf : P.kleinCoordinate a∈segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q):=by
    rw [ha,hfform]
    exact (convex_segment (𝕜:=ℝ) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q)) (left_mem_segment ℝ _ _) hxseg
      (by norm_num) (by norm_num) (by norm_num)
  have hbf : P.kleinCoordinate b∈segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q):=by
    rw [hb,hfform]
    exact (convex_segment (𝕜:=ℝ) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q)) (right_mem_segment ℝ _ _) hxseg
      (by norm_num) (by norm_num) (by norm_num)
  have he : closure (P.kleinCoordinate '' s.val)=segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q):=by
    rw [←fuchsianSideClosedModel_klein_image,hs,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
  have haS:=original_side_klein_closure_mem s a (he ▸ haf)
  have hbS:=original_side_klein_closure_mem s b (he ▸ hbf)
  exact (hD.vertex_side_endpoint hv s.property hx).2
    ⟨a,haS,b,hbS,hab,original_normalizedKlein_between P x a b hab hopen⟩


/-- A genuine ideal point on a nondegenerate closed hyperbolic segment is one of its actual endpoints. -/
theorem original_segment_ideal_eq_endpoint (p q z:𝕔𝔻) (hpq:p≠q)
    (hz:z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q) (hn:‖(z:ℂ)‖=1) : z=p∨z=q := by
  by_contra hnot
  push Not at hnot
  have hseg : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate z∈segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate hz
  have hopen:=mem_openSegment_of_ne_left_right
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hnot.1.symm)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hnot.2.symm) hseg
  have hball:=openSegment_subset_ball_of_ne
    (mem_closedBall_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein
      p).norm_le_one)
    (mem_closedBall_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein
      q).norm_le_one)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hpq) hopen
  have hlt : ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate z‖<1:=mem_ball_zero_iff.mp hball
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate z=(z:ℂ):=
    congrArg (fun a:𝕔𝔻=>(a:ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed z
      hn)
  rw [he,hn] at hlt
  exact (lt_irrefl _ hlt)

/-- Distinct unchanged original compactified sides meet only at their genuine common endpoints, including at infinity. -/
theorem original_closed_sides_meet_endpoints {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (s t:FuchsianPolygonSides P D) (hst:s≠t)
    (p q a b:𝕔𝔻) (hpq:p≠q) (hab:a≠b)
    (hs:fuchsianSideClosedModel s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q)
    (ht:fuchsianSideClosedModel t=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a b) :
    fuchsianSideClosedModel s∩fuchsianSideClosedModel t⊆{p,q}∩{a,b} := by
  intro z hz
  rcases _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDisc_interior_or_ideal z with ⟨w,rfl⟩ | hn
  · let x:=P.finiteCoordinate.symm w
    have hw:P.finiteCoordinate x=w:=P.finiteCoordinate.apply_symm_apply w
    have hxS : x∈s.val:=by
      apply (mem_fuchsianSideClosedModel_finite s x).mp
      rw [hw]
      exact hz.1
    have hxT : x∈t.val:=by
      apply (mem_fuchsianSideClosedModel_finite t x).mp
      rw [hw]
      exact hz.2
    have hv:=hD.distinct_sides_meet_vertex s.property t.property
      (fun he=>hst (Subtype.ext he)) ⟨hxS,hxT⟩
    have hsp:=original_side_vertex_eq_closed_endpoint hD s p q hpq hs x hxS hv
    have htp:=original_side_vertex_eq_closed_endpoint hD t a b hab ht x hxT hv
    rw [hw] at hsp htp
    exact ⟨by simpa only [mem_insert_iff,mem_singleton_iff] using hsp,
      by simpa only [mem_insert_iff,mem_singleton_iff] using htp⟩
  · exact ⟨by simpa only [mem_insert_iff,mem_singleton_iff] using
      original_segment_ideal_eq_endpoint p q z hpq (hs ▸ hz.1) hn,
      by simpa only [mem_insert_iff,mem_singleton_iff] using
      original_segment_ideal_eq_endpoint a b z hab (ht ▸ hz.2) hn⟩

end LowDimensionalTopology.Geometry.Fuchsian
