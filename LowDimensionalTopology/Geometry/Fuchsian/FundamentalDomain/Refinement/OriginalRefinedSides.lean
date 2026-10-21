/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.SelfPairedSideCompactification
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaPolygonSides
@[expose] public section
noncomputable section
set_option autoImplicit false
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

/-- Each unchanged non-self-paired original side occurs once; each actual self-paired side occurs twice after its genuine elliptic-center subdivision. -/
def OriginalRefinedSide {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) :=
  {v:FuchsianPolygonSides P D×Bool // v.2=true→fuchsianPairedSide hD v.1=v.1}

/-- Literal original partner, with the two genuine self-paired halves exchanged. -/
def OriginalRefinedSide.pair {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (v:OriginalRefinedSide hD) :
    OriginalRefinedSide hD := by
  classical
  refine ⟨(fuchsianPairedSide hD v.val.1,
    if fuchsianPairedSide hD v.val.1=v.val.1 then !v.val.2 else v.val.2),?_⟩
  intro ht
  by_cases hs:fuchsianPairedSide hD v.val.1=v.val.1
  · simp only [hs]
  · simp only [hs,ite_false] at ht
    exact False.elim (hs (v.property ht))

@[simp] theorem OriginalRefinedSide.pair_original {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) : v.pair.val.1=fuchsianPairedSide hD v.val.1 := rfl

/-- The refined original side pairing is an actual involution. -/
theorem OriginalRefinedSide.pair_involutive {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) :
    Function.Involutive (_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.pair (hD:=hD)) := by
  classical
  intro v
  apply Subtype.ext
  apply Prod.ext
  · exact fuchsianPairedSide_involutive hD v.val.1
  · change (if fuchsianPairedSide hD (fuchsianPairedSide hD v.val.1)=fuchsianPairedSide hD v.val.1
      then !(if fuchsianPairedSide hD v.val.1=v.val.1 then !v.val.2 else v.val.2)
      else (if fuchsianPairedSide hD v.val.1=v.val.1 then !v.val.2 else v.val.2))=v.val.2
    rw [fuchsianPairedSide_involutive hD]
    by_cases hs:fuchsianPairedSide hD v.val.1=v.val.1
    · simp only [hs,ite_true,Bool.not_not]
    · simp only [hs,show ¬v.val.1=fuchsianPairedSide hD v.val.1 from fun he=>hs he.symm,ite_false]

/-- No refined original side is paired with itself. This is derived from the actual original involution rather than assumed as polygon data. -/
theorem OriginalRefinedSide.pair_ne_self {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) : v.pair≠v := by
  classical
  intro he
  have hs:fuchsianPairedSide hD v.val.1=v.val.1:=congrArg (fun a:OriginalRefinedSide hD=>a.val.1) he
  have hb:=congrArg (fun a:OriginalRefinedSide hD=>a.val.2) he
  change (if fuchsianPairedSide hD v.val.1=v.val.1 then !v.val.2 else v.val.2)=v.val.2 at hb
  rw [ite_eq_left hs] at hb
  exact Bool.not_ne_self _ hb

/-- Refinement keeps the exact original side-pairing transformation. -/
theorem OriginalRefinedSide.pair_element {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) :
    fuchsianSideElement hD v.pair.val.1=(fuchsianSideElement hD v.val.1)⁻¹ :=
  fuchsianSideElement_paired hD v.val.1

/-- The actual refined partner permutation. -/
def OriginalRefinedSide.pairingEquiv {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) :
    Equiv.Perm (OriginalRefinedSide
      hD):=(_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.pair_involutive hD).toPerm

/-- Genuine finite area supplies a finite refined original side set, with no finite-sided assumption. -/
theorem originalRefinedSide_finite {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤) : Finite (OriginalRefinedSide hD) := by
  let :Finite (FuchsianPolygonSides P D):=finite_area_polygon_finite_sides hD ha
  unfold OriginalRefinedSide
  exact inferInstance


/-- Genuine geometric data for subdividing one unchanged original self-paired side. -/
structure OriginalSelfSideSplit {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (s:FuchsianPolygonSides P D) where
  left:𝕔𝔻
  right:𝕔𝔻
  center:P.domain.carrier
  endpoints_ne:left≠right
  side_eq:fuchsianSideClosedModel s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment left right
  center_mem:center∈s.val
  center_fixed:fuchsianSideElement hD s•center=center
  center_between:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate center))∈
    openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      left) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate right)

/-- The geometric subdivision data are constructed from the original actual self-pairing. -/
def originalSelfSideSplit {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (s:FuchsianPolygonSides P D)
    (hself:fuchsianPairedSide hD s=s) : OriginalSelfSideSplit hD s := by
  have hn:Nonempty (OriginalSelfSideSplit hD s):=by
    obtain ⟨p,q,x,hpq,hs,hx,hfix,_ho,_hc,hbetween,_hm,_hu,_hi⟩:=
      exists_selfPaired_original_side_subdivision hD s hself
    exact ⟨⟨p,q,x,hpq,hs,hx,hfix,hbetween⟩⟩
  exact Classical.choice hn

/-- The actual first compactified half of a subdivided original side. -/
def OriginalSelfSideSplit.first {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} {s:FuchsianPolygonSides P D}
    (A:OriginalSelfSideSplit hD s) : Set 𝕔𝔻:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment A.left (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center))

/-- The actual second compactified half of a subdivided original side. -/
def OriginalSelfSideSplit.second {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} {s:FuchsianPolygonSides P D}
    (A:OriginalSelfSideSplit hD s) : Set 𝕔𝔻:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center)) A.right

/-- Genuine original self-pairing maps the first half exactly to the second half. -/
theorem OriginalSelfSideSplit.map_first {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    {s:FuchsianPolygonSides P D} (A:OriginalSelfSideSplit hD s) (hs:fuchsianPairedSide hD s=s) :
    (P.compactifiedAction (fuchsianSideElement hD s)).closedMap '' A.first=A.second := by
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalSelfSideSplit.first,_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalSelfSideSplit.second,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_comm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center)) A.right]
  exact fuchsian_selfPaired_halfSide_image hD s hs A.left A.right A.endpoints_ne A.side_eq A.center A.center_fixed

/-- Genuine original self-pairing also maps the second half exactly to the first half. -/
theorem OriginalSelfSideSplit.map_second {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    {s:FuchsianPolygonSides P D} (A:OriginalSelfSideSplit hD s) (hs:fuchsianPairedSide hD s=s) :
    (P.compactifiedAction (fuchsianSideElement hD s)).closedMap '' A.second=A.first := by
  let g:=fuchsianSideElement hD s
  let f:=(P.compactifiedAction g).closedMap
  obtain ⟨hp,hq⟩:=fuchsian_selfPaired_compactified_endpoints_swap hD s hs A.left A.right A.endpoints_ne A.side_eq
  have hfm:f (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center):=by
    rw [P.compactifiedAction_finite,A.center_fixed]
  change f '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center)) A.right=_
  rw [(P.compactifiedAction g).image_closedModelDiscHSegment,hfm,hq,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_comm]
  rfl

/-- Actual original halves cover the unchanged entire original compactified side and meet exactly at its genuine finite fixed point. -/
theorem OriginalSelfSideSplit.union_inter {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    {s:FuchsianPolygonSides P D} (A:OriginalSelfSideSplit hD s) :
    A.first∪A.second=fuchsianSideClosedModel s ∧
      A.first∩A.second={_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center)} := by
  obtain ⟨hu,hi⟩:=compactified_polygon_segment_split A.left (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center)) A.right
    (openSegment_subset_segment ℝ _ _ A.center_between)
  exact ⟨hu.trans A.side_eq.symm,hi⟩

/-- Literal geometric OriginalRefinedSide.carrier of each refined original side. Only original self-paired sides are subdivided. -/
def OriginalRefinedSide.carrier {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (v:OriginalRefinedSide hD) : Set 𝕔𝔻 := by
  classical
  exact if hs:fuchsianPairedSide hD v.val.1=v.val.1 then
    if v.val.2 then (originalSelfSideSplit hD v.val.1 hs).second else (originalSelfSideSplit hD v.val.1 hs).first
    else fuchsianSideClosedModel v.val.1


/-- Each actual refined side stays in its unchanged original side closure. -/
theorem OriginalRefinedSide.carrier_subset_original {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) : v.carrier⊆fuchsianSideClosedModel v.val.1 := by
  classical
  by_cases hs:fuchsianPairedSide hD v.val.1=v.val.1
  · let A:=originalSelfSideSplit hD v.val.1 hs
    have he:=A.union_inter.1
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,dite_eq_left hs]
    cases hb:v.val.2
    · simp only [Bool.false_eq_true,ite_false]
      exact he ▸ subset_union_left
    · simp only [ite_true]
      exact he ▸ subset_union_right
  · simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,hs,dite_false]
    exact subset_refl _

/-- Every refined original side is a genuine nondegenerate finite-or-ideal geodesic segment. -/
theorem OriginalRefinedSide.carrier_eq_segment {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) : ∃p q:𝕔𝔻,p≠q∧v.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q := by
  classical
  by_cases hs:fuchsianPairedSide hD v.val.1=v.val.1
  · let A:=originalSelfSideSplit hD v.val.1 hs
    have hpl:A.left≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center):=by
      intro he
      have hm:=A.center_between
      rw [←he] at hm
      exact A.endpoints_ne (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective
        (left_mem_openSegment_iff.mp hm))
    have hpr:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center)≠A.right:=by
      intro he
      have hm:=A.center_between
      rw [he] at hm
      exact A.endpoints_ne (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective
        (right_mem_openSegment_iff.mp hm))
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,dite_eq_left hs]
    cases hb:v.val.2
    · exact ⟨A.left,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center),hpl,by simp only [Bool.false_eq_true,ite_false];rfl⟩
    · exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center),A.right,hpr,by simp only [ite_true];rfl⟩
  · rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,dite_eq_right hs]
    exact fuchsianSideClosedModel_eq_segment v.val.1

/-- The finite refinement covers exactly the union of the unchanged original compactified sides. -/
theorem originalRefinedSide_iUnion_carrier {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) :
    (⋃v:OriginalRefinedSide hD,v.carrier)=⋃s:FuchsianPolygonSides P D,fuchsianSideClosedModel s := by
  classical
  apply subset_antisymm
  · intro p hp
    obtain ⟨v,hv⟩:=mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨v.val.1,v.carrier_subset_original hv⟩
  · intro p hp
    obtain ⟨s,hs⟩:=mem_iUnion.mp hp
    let v:OriginalRefinedSide hD:=⟨(s,false),by simp only [Bool.false_eq_true,false_implies]⟩
    by_cases hself:fuchsianPairedSide hD s=s
    · let w:OriginalRefinedSide hD:=⟨(s,true),fun _=>hself⟩
      let A:=originalSelfSideSplit hD s hself
      have hv:v.carrier=A.first:=by simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,v,hself,dite_true,Bool.false_eq_true,ite_false];rfl
      have hw:w.carrier=A.second:=by simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,w,hself,dite_true,ite_true];rfl
      rw [←A.union_inter.1] at hs
      rcases hs with hs|hs
      · exact mem_iUnion.mpr ⟨v,hv.symm ▸ hs⟩
      · exact mem_iUnion.mpr ⟨w,hw.symm ▸ hs⟩
    · refine mem_iUnion.mpr ⟨v,?_⟩
      simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,v,hself,dite_false] using hs

/-- Every literal refined pairing is the restriction of the unchanged original group transformation. -/
theorem OriginalRefinedSide.pair_carrier {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) :
    (P.compactifiedAction (fuchsianSideElement hD v.val.1)⁻¹).closedMap '' v.carrier=v.pair.carrier := by
  classical
  let s:=v.val.1
  by_cases hs:fuchsianPairedSide hD s=s
  · let A:=originalSelfSideSplit hD s hs
    have hi:(fuchsianSideElement hD s)⁻¹=fuchsianSideElement hD s:=by
      have he:=fuchsianSideElement_paired hD s
      rw [hs] at he
      exact he.symm
    have hp:v.pair=⟨(v.val.1,!v.val.2),fun _=>hs⟩:=by
      apply Subtype.ext
      simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.pair,show fuchsianPairedSide hD
        v.val.1=v.val.1 from hs,ite_true]
    rw [hi,hp]
    have hself:fuchsianPairedSide hD v.val.1=v.val.1:=hs
    simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,dite_eq_left hself]
    cases hb:v.val.2
    · simpa only [hb,Bool.false_eq_true,ite_false,Bool.not_false,ite_true] using A.map_first hs
    · simpa only [hb,ite_true,Bool.not_true,Bool.false_eq_true,ite_false] using A.map_second hs
  · have hmate:fuchsianPairedSide hD (fuchsianPairedSide hD s)≠fuchsianPairedSide hD s:=by
      rw [fuchsianPairedSide_involutive hD]
      exact fun he=>hs he.symm
    have hv:v.carrier=fuchsianSideClosedModel s:=by simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,s,hs,dite_false]
    have hw:v.pair.carrier=fuchsianSideClosedModel (fuchsianPairedSide hD s):=by
      simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.pair_original,s,hmate,dite_false]
    rw [hv,hw]
    exact fuchsianSideClosedModel_paired_image hD s

end LowDimensionalTopology.Geometry.Fuchsian
