/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Refinement.OriginalCompactSideIncidence
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Refinement.OriginalRefinedSides
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- An original extreme endpoint in a genuine subsegment remains one of that subsegment's endpoints. -/
theorem original_closed_subsegment_endpoint (a b p q x:𝕔𝔻) (hpq:p≠q)
    (hsub:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a
      b⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q)
    (hx:x∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a b) (he:x=p∨x=q) : x=a∨x=b := by
  have hKsub:segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate b)⊆
      segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact image_mono hsub
  have hKx:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate x∈segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate b):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact mem_image_of_mem _ hx
  have hext:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate x∈
      (segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q)).extremePoints ℝ:=by
    rcases he with rfl|rfl
    · exact original_segment_left_extreme _ _ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hpq)
    · rw [segment_symm]
      exact original_segment_left_extreme _ _ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hpq.symm)
  by_contra hn
  push Not at hn
  have hopen:=mem_openSegment_of_ne_left_right (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hn.1.symm)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hn.2.symm) hKx
  have ha:=hext.2 (hKsub (left_mem_segment ℝ _ _)) (hKsub (right_mem_segment ℝ _ _)) hopen
  exact hn.1 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective ha.symm)

/-- Refined pieces coming from different unchanged original sides meet only in their own genuine endpoint pairs. -/
theorem OriginalRefinedSide.inter_subset_endpoints_of_original_ne
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H} {D:Set
      P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D} (v w:OriginalRefinedSide hD)
    (hvw:v.val.1≠w.val.1) (a b p q:𝕔𝔻)
    (hv:v.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a
      b) (hw:w.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q) :
    v.carrier∩w.carrier⊆{a,b}∩{p,q} := by
  obtain ⟨a',b',hab,hs⟩:=fuchsianSideClosedModel_eq_segment v.val.1
  obtain ⟨p',q',hpq,ht⟩:=fuchsianSideClosedModel_eq_segment w.val.1
  have hint:=original_closed_sides_meet_endpoints hD v.val.1 w.val.1 hvw a' b' p' q' hab hpq hs ht
  have hsubv:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a b⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a' b':=by
    rw [←hv,←hs]
    exact v.carrier_subset_original
  have hsubw:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p' q':=by
    rw [←hw,←ht]
    exact w.carrier_subset_original
  rintro x ⟨hxv,hxw⟩
  obtain ⟨hsv,hsw⟩:=hint ⟨v.carrier_subset_original hxv,w.carrier_subset_original hxw⟩
  have hev:x=a'∨x=b':=by simpa only [mem_insert_iff,mem_singleton_iff] using hsv
  have hew:x=p'∨x=q':=by simpa only [mem_insert_iff,mem_singleton_iff] using hsw
  exact ⟨by simpa only [mem_insert_iff,mem_singleton_iff] using
    original_closed_subsegment_endpoint a b a' b' x hab hsubv (hv ▸ hxv) hev,
    by simpa only [mem_insert_iff,mem_singleton_iff] using
    original_closed_subsegment_endpoint p q p' q' x hpq hsubw (hw ▸ hxw) hew⟩

/-- The original fixed center is strictly away from the first actual side endpoint. -/
theorem OriginalSelfSideSplit.left_ne_center {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    {s:FuchsianPolygonSides P D} (A:OriginalSelfSideSplit hD s) :
    A.left≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center) := by
  intro he
  have hm:=A.center_between
  rw [←he] at hm
  exact A.endpoints_ne (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective
    (left_mem_openSegment_iff.mp hm))

/-- The original fixed center is strictly away from the second actual side endpoint. -/
theorem OriginalSelfSideSplit.center_ne_right {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    {s:FuchsianPolygonSides P D} (A:OriginalSelfSideSplit hD s) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center)≠A.right := by
  intro he
  have hm:=A.center_between
  rw [he] at hm
  exact A.endpoints_ne (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective
    (right_mem_openSegment_iff.mp hm))

/-- Two actual halves of one original self-paired side meet only at their own genuine endpoints, regardless of the chosen endpoint order. -/
theorem OriginalSelfSideSplit.inter_subset_endpoints {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    {s:FuchsianPolygonSides P D} (A:OriginalSelfSideSplit hD s) (a b p q:𝕔𝔻)
    (ha:A.first=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a
      b) (hb:A.second=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q) :
    A.first∩A.second⊆{a,b}∩{p,q} := by
  rintro x hx
  have he:x=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center):=by
    exact mem_singleton_iff.mp (A.union_inter.2 ▸ hx)
  have hsuba:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a b⊆
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment A.left (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center)):=by
    rw [←ha]
    exact subset_refl _
  have hsubb:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q⊆
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center)) A.right:=by
    rw [←hb]
    exact subset_refl _
  exact ⟨by simpa only [mem_insert_iff,mem_singleton_iff] using
    original_closed_subsegment_endpoint a b A.left _ x A.left_ne_center hsuba (ha ▸ hx.1) (Or.inr he),
    by simpa only [mem_insert_iff,mem_singleton_iff] using
    original_closed_subsegment_endpoint p q _ A.right x A.center_ne_right hsubb (hb ▸ hx.2) (Or.inl he)⟩

/-- Any two distinct genuine refined sides intersect only in their actual endpoint pairs. Both original sides and their genuine elliptic-center halves are included. -/
theorem OriginalRefinedSide.inter_subset_endpoints
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H} {D:Set
      P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D} (v w:OriginalRefinedSide hD) (hne:v≠w)
    (a b p q:𝕔𝔻) (hv:v.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a b)
    (hw:w.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q) : v.carrier∩w.carrier⊆{a,b}∩{p,q} := by
  by_cases hsrc:v.val.1=w.val.1
  · rcases v with ⟨⟨s,bv⟩,vprop⟩
    rcases w with ⟨⟨t,bw⟩,wprop⟩
    change s=t at hsrc
    subst t
    cases bv <;> cases bw
    · exact False.elim (hne (Subtype.ext rfl))
    · have hs:=wprop rfl
      let A:=originalSelfSideSplit hD s hs
      have hfirst:_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier ⟨(s,false),vprop⟩=A.first:=by
        simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,hs,dite_true,Bool.false_eq_true,ite_false]
        rfl
      have hsecond:_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier ⟨(s,true),wprop⟩=A.second:=by
        simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,hs,dite_true,ite_true]
        rfl
      rw [hfirst,hsecond]
      exact A.inter_subset_endpoints a b p q (hfirst.symm.trans hv) (hsecond.symm.trans hw)
    · have hs:=vprop rfl
      let A:=originalSelfSideSplit hD s hs
      have hsecond:_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier ⟨(s,true),vprop⟩=A.second:=by
        simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,hs,dite_true,ite_true]
        rfl
      have hfirst:_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier ⟨(s,false),wprop⟩=A.first:=by
        simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,hs,dite_true,Bool.false_eq_true,ite_false]
        rfl
      rw [hsecond,hfirst,inter_comm A.second A.first,inter_comm ({a,b}:Set 𝕔𝔻)]
      exact A.inter_subset_endpoints p q a b (hfirst.symm.trans hw) (hsecond.symm.trans hv)
    · exact False.elim (hne (Subtype.ext rfl))
  · exact v.inter_subset_endpoints_of_original_ne w hsrc a b p q hv hw

/-- Choose the two genuine endpoints of a refined original side. Their order is arbitrary here and supplies no orientation assumption. -/
def OriginalRefinedSide.endpointPair {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) :
    {p:𝕔𝔻×𝕔𝔻 // p.1≠p.2∧v.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p.1 p.2} := by
  let p:=Classical.choose v.carrier_eq_segment
  let q:=Classical.choose (Classical.choose_spec v.carrier_eq_segment)
  exact ⟨(p,q),Classical.choose_spec (Classical.choose_spec v.carrier_eq_segment)⟩

def OriginalRefinedSide.leftEndpoint {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) : 𝕔𝔻:=v.endpointPair.val.1

def OriginalRefinedSide.rightEndpoint {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) : 𝕔𝔻:=v.endpointPair.val.2

theorem OriginalRefinedSide.endpoints_ne {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) : v.leftEndpoint≠v.rightEndpoint:=v.endpointPair.property.1

theorem OriginalRefinedSide.carrier_eq_endpoints {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) :
    v.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment v.leftEndpoint v.rightEndpoint:=v.endpointPair.property.2

/-- The exact genuine endpoint set of all the original geometric refined pieces. -/
def originalRefinedEndpointSet {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) : Set 𝕔𝔻:=
  range (_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.leftEndpoint
    (hD:=hD))∪range (_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.rightEndpoint (hD:=hD))

theorem originalRefinedEndpointSet_finite {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ha:P.area D≠⊤) : (originalRefinedEndpointSet hD).Finite := by
  let :Finite (OriginalRefinedSide hD):=originalRefinedSide_finite hD ha
  exact (finite_range _).union (finite_range _)

theorem OriginalRefinedSide.endpoints_mem_carrier {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) : v.leftEndpoint∈v.carrier∧v.rightEndpoint∈v.carrier := by
  rw [v.carrier_eq_endpoints]
  constructor
  · apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact left_mem_segment ℝ _ _
  · apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact right_mem_segment ℝ _ _

/-- Genuine original pairing transformations carry the exact unordered endpoint pair to that of the actual refined partner. -/
theorem OriginalRefinedSide.pair_endpoint_pair {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) :
    ({(P.compactifiedAction (fuchsianSideElement hD v.val.1)⁻¹).closedMap v.leftEndpoint,
      (P.compactifiedAction (fuchsianSideElement hD v.val.1)⁻¹).closedMap v.rightEndpoint}:Set 𝕔𝔻)=
      {v.pair.leftEndpoint,v.pair.rightEndpoint} := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.closed_segment_image_endpoints
  rw [←v.carrier_eq_endpoints,←v.pair.carrier_eq_endpoints]
  exact v.pair_carrier

/-- Distinct genuine refined pieces have no intersections except at the finite exact endpoint set. -/
theorem OriginalRefinedSide.inter_subset_endpointSet {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v w:OriginalRefinedSide hD) (hne:v≠w) : v.carrier∩w.carrier⊆originalRefinedEndpointSet hD := by
  intro x hx
  have he: x=v.leftEndpoint∨x=v.rightEndpoint:=by
    have hh:=(v.inter_subset_endpoints w hne v.leftEndpoint v.rightEndpoint w.leftEndpoint w.rightEndpoint
      v.carrier_eq_endpoints w.carrier_eq_endpoints hx).1
    simpa only [mem_insert_iff,mem_singleton_iff] using hh
  rcases he with rfl|rfl
  · exact Or.inl (mem_range_self v)
  · exact Or.inr (mem_range_self v)

/-- The exact marked endpoint set has no extra points in the interior of any genuine refined side. -/
theorem OriginalRefinedSide.endpointSet_inter_carrier {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (v:OriginalRefinedSide hD) : originalRefinedEndpointSet hD∩v.carrier⊆{v.leftEndpoint,v.rightEndpoint} := by
  rintro x ⟨hx,hxv⟩
  have hendpoint (w:OriginalRefinedSide hD) (hxw:x∈w.carrier) : x=v.leftEndpoint∨x=v.rightEndpoint:=by
    by_cases hw:w=v
    · rw [hw] at hxw
      rcases hx with ⟨a,ha⟩|⟨a,ha⟩
      · by_cases hav:a=v
        · exact Or.inl (by simpa only [hav] using ha.symm)
        · have hh:=(v.inter_subset_endpoints a (Ne.symm hav) _ _ _ _ v.carrier_eq_endpoints a.carrier_eq_endpoints
            ⟨hxv,ha ▸ a.endpoints_mem_carrier.1⟩).1
          simpa only [mem_insert_iff,mem_singleton_iff] using hh
      · by_cases hav:a=v
        · exact Or.inr (by simpa only [hav] using ha.symm)
        · have hh:=(v.inter_subset_endpoints a (Ne.symm hav) _ _ _ _ v.carrier_eq_endpoints a.carrier_eq_endpoints
            ⟨hxv,ha ▸ a.endpoints_mem_carrier.2⟩).1
          simpa only [mem_insert_iff,mem_singleton_iff] using hh
    · have hh:=(v.inter_subset_endpoints w (Ne.symm hw) _ _ _ _ v.carrier_eq_endpoints w.carrier_eq_endpoints
        ⟨hxv,hxw⟩).1
      simpa only [mem_insert_iff,mem_singleton_iff] using hh
  rcases hx with ⟨w,hw⟩|⟨w,hw⟩
  · simpa only [mem_insert_iff,mem_singleton_iff] using hendpoint w (hw ▸ w.endpoints_mem_carrier.1)
  · simpa only [mem_insert_iff,mem_singleton_iff] using hendpoint w (hw ▸ w.endpoints_mem_carrier.2)
end LowDimensionalTopology.Geometry.Fuchsian
