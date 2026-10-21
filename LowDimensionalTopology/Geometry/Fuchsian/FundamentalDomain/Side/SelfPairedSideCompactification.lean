/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CompactifiedPolygonSides
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSelfPairedSides
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianFiniteGroups
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonBoundaryConvexity
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped OnePoint Complex.UnitDisc Pointwise
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
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Every fixed point of an original elliptic in the actual closed disc is strictly finite interior. -/
theorem UnitDiscFuchsianGroup.compactifiedAction_fixed_norm_lt_one
    {H : Subgroup Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H) (g:H)
    (he:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val)
    (p:𝕔𝔻)
    (hp:(P.compactifiedAction g).closedMap p=p) :
    ‖(p:ℂ)‖<1 := by
  have hfix : g.val.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p:=by
    have hh:=congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended hp
    rwa [P.compactifiedAction_sphere] at hh
  have hne : ‖(p:ℂ)‖≠1:=by
    intro hn
    have hb : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=by
      rw [_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle]
      exact (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe 0 (p:ℂ) 1).mpr (by simpa only [sub_zero] using hn)
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_fixed_not_mem_disc_frontier g.val he _root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc
      (P.image_eq g) hfix hb
  exact lt_of_le_of_ne p.norm_le_one hne

/-- An original elliptic has at most one actual closed-disc fixed point. -/
theorem UnitDiscFuchsianGroup.compactifiedAction_elliptic_fixed_subsingleton
    {H : Subgroup Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H) (g:H)
    (he:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val) :
    {p:𝕔𝔻 | (P.compactifiedAction g).closedMap p=p}.Subsingleton := by
  intro p hp q hq
  have hpn:=P.compactifiedAction_fixed_norm_lt_one g he p hp
  have hqn:=P.compactifiedAction_fixed_norm_lt_one g he q hq
  let a:_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedUnitDisc (p:ℂ)).mpr hpn⟩
  let b:_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended q,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedUnitDisc (q:ℂ)).mpr hqn⟩
  obtain ⟨u,_hu,huniq⟩:=elliptic_unitDisc_existsUnique_fixed g.val he (P.image_eq g)
  have hfa : g.val.val a.val=a.val:=by
    have hh:=congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended hp
    rwa [P.compactifiedAction_sphere] at hh
  have hfb : g.val.val b.val=b.val:=by
    have hh:=congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended hq
    rwa [P.compactifiedAction_sphere] at hh
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_closedDiscToExtended.injective
  exact congrArg Subtype.val ((huniq a hfa).trans (huniq b hfb).symm)

/-- A literal self-paired original side exchanges its two derived finite-or-ideal endpoints. -/
theorem fuchsian_selfPaired_compactified_endpoints_swap
    {H : Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (s:FuchsianPolygonSides P D)
    (hself:fuchsianPairedSide hD s=s) (p q:𝕔𝔻) (hpq:p≠q)
    (hs:fuchsianSideClosedModel s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q) :
    (P.compactifiedAction (fuchsianSideElement hD s)).closedMap p=q∧
      (P.compactifiedAction (fuchsianSideElement hD s)).closedMap q=p := by
  let g:=fuchsianSideElement hD s
  let e:=P.compactifiedAction g
  have hinv : g⁻¹=g:=by
    have hh:=fuchsianSideElement_paired hD s
    rw [hself] at hh
    exact hh.symm
  have hpairs : ({e.closedMap p,e.closedMap q}:Set 𝕔𝔻)={p,q}:=by
    have hh:=fuchsianSideClosedModel_pairing_endpoints hD s p q p q hs (hself.symm ▸ hs)
    rwa [hinv] at hh
  have hpmem : e.closedMap p∈({p,q}:Set 𝕔𝔻):=by rw [←hpairs];simp only [mem_insert_iff,true_or]
  have hqmem : e.closedMap q∈({p,q}:Set 𝕔𝔻):=by rw [←hpairs];simp only [mem_insert_iff,mem_singleton_iff,or_true]
  have he:= (fuchsianPairedSide_self_geometric hD s hself).2.1
  have hsub:=P.compactifiedAction_elliptic_fixed_subsingleton g he
  have hnot : e.closedMap p≠p:=by
    intro hfix
    have hqq : e.closedMap q=q:=by
      rcases hqmem with hqp|hqq
      · exact False.elim (hpq (e.closedMap.injective (hfix.trans hqp.symm)))
      · exact hqq
    exact hpq (hsub hfix hqq)
  have heqp : e.closedMap p=q:=hpmem.resolve_left hnot
  refine ⟨heqp,?_⟩
  rcases hqmem with hqp|hqq
  · exact hqp
  · exact False.elim (hpq (e.closedMap.injective (heqp.trans hqq.symm)))

/-- The fixed point used to subdivide a self-paired side lies in its genuine open finite-or-ideal segment. -/
theorem fuchsian_selfPaired_fixedPoint_between_endpoints
    {H : Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (s:FuchsianPolygonSides P D)
    (hself:fuchsianPairedSide hD s=s) (p q:𝕔𝔻) (hpq:p≠q)
    (hs:fuchsianSideClosedModel s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q)
    (x:P.domain.carrier) (hx:x∈s.val) (hfix:fuchsianSideElement hD s•x=x) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x))∈
      openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q) := by
  let m:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)
  let e:=P.compactifiedAction (fuchsianSideElement hD s)
  have hem : e.closedMap m=m:=by rw [P.compactifiedAction_finite,hfix]
  obtain ⟨hep,heq⟩:=fuchsian_selfPaired_compactified_endpoints_swap hD s hself p q hpq hs
  have hmp : m≠p:=by intro he;rw [he] at hem;exact hpq (hem.symm.trans hep)
  have hmq : m≠q:=by intro he;rw [he] at hem;exact hpq (heq.symm.trans hem)
  have hm : m∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q:=by
    rw [←hs]
    exact (mem_fuchsianSideClosedModel_finite s x).mpr hx
  have hk:=mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate hm
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment] at hk
  exact mem_openSegment_of_ne_left_right
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hmp.symm) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hmq.symm) hk

/-- Subdivision at the genuine original order-two fixed point pairs the two actual half-sides. -/
theorem fuchsian_selfPaired_halfSide_image
    {H : Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (s:FuchsianPolygonSides P D)
    (hself:fuchsianPairedSide hD s=s) (p q:𝕔𝔻) (hpq:p≠q)
    (hs:fuchsianSideClosedModel s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q)
    (x:P.domain.carrier) (hfix:fuchsianSideElement hD s•x=x) :
    (P.compactifiedAction (fuchsianSideElement hD s)).closedMap ''
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment q (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)) := by
  rw [(P.compactifiedAction (fuchsianSideElement hD s)).image_closedModelDiscHSegment,
    (fuchsian_selfPaired_compactified_endpoints_swap hD s hself p q hpq hs).1,
    P.compactifiedAction_finite,hfix]

/-- Subdividing a genuine compactified segment at one of its own points gives two halves with exactly that common endpoint. -/
theorem compactified_polygon_segment_split (p m q:𝕔𝔻)
    (hm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate m∈segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p m∪_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment m q=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p m∩_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment m q={m} := by
  constructor
  · apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.image_injective
    rw [image_union,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.polygon_segment_split hm
  · apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.image_injective
    rw [image_inter _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment,image_singleton]
    ext z
    constructor
    · rintro ⟨hz1,hz2⟩
      have hzfull: z∈segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q):=
        (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) hm hz1
      have h1:=dist_add_dist_of_mem_segment hz1
      have h2:=dist_add_dist_of_mem_segment hz2
      have h3:=dist_add_dist_of_mem_segment hm
      have h4:=dist_add_dist_of_mem_segment hzfull
      rw [dist_comm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate m) z] at h2
      exact dist_eq_zero.mp (by linarith)
    · rintro rfl
      exact ⟨right_mem_segment ℝ _ _,left_mem_segment ℝ _ _⟩

/-- Every self-paired original side admits its required actual two-sided subdivision at the derived original order-two elliptic fixed point, retaining both finite-or-ideal endpoints and the true pairing of the two halves. -/
theorem exists_selfPaired_original_side_subdivision
    {H : Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (s:FuchsianPolygonSides P D)
    (hself:fuchsianPairedSide hD s=s) :
    ∃p q:𝕔𝔻,∃x:P.domain.carrier,p≠q∧
      fuchsianSideClosedModel s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q∧x∈s.val∧
      fuchsianSideElement hD s•x=x∧fuchsianPointOrder P x=2∧fuchsianPolygonCycle P D x={x}∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x))∈
        openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q)∧
      (P.compactifiedAction (fuchsianSideElement hD s)).closedMap ''
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x))=
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)) q∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x))∪
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)) q=fuchsianSideClosedModel s∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x))∩
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)) q=
          {_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)} := by
  obtain ⟨p,q,hpq,hs⟩:=fuchsianSideClosedModel_eq_segment s
  obtain ⟨_horder,_he,x,hx,hfix,_hi,hpoint,hcycle,_hstab⟩:=fuchsianPairedSide_self_geometric hD s hself
  have hbetween:=fuchsian_selfPaired_fixedPoint_between_endpoints hD s hself p q hpq hs x hx hfix
  obtain ⟨hunion,hinter⟩:=compactified_polygon_segment_split p (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)) q
    (openSegment_subset_segment ℝ _ _ hbetween)
  refine ⟨p,q,x,hpq,hs,hx,hfix,hpoint,hcycle,hbetween,?_,hunion.trans hs.symm,hinter⟩
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_comm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)) q]
  exact fuchsian_selfPaired_halfSide_image hD s hself p q hpq hs x hfix

end LowDimensionalTopology.Geometry.Fuchsian
