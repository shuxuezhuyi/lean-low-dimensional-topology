/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Area.OriginalRawWeightedEuler
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonVertexConventions
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.FinitePolygonEllipticClasses
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.FuchsianSignatureOrders
/-!
# Elliptic raw corner classes

Refined endpoints retain finite vertices and self-pairing centers. Their
nonaccidental raw corner classes correspond to maximal elliptic cyclic
conjugacy classes, preserving stabilizer orders and reciprocal weights.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical

/-- The actual subdivision center of every self-paired original side is a genuine marked endpoint. -/
theorem originalSelfSideSplit_center_endpoint
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (s : FuchsianPolygonSides P D) (hself : fuchsianPairedSide hD s=s) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate (originalSelfSideSplit hD s
      hself).center)∈
      originalRefinedEndpointSet hD := by
  let A:=originalSelfSideSplit hD s hself
  let v : OriginalRefinedSide hD:=⟨(s,false),by simp only [Bool.false_eq_true,false_implies]⟩
  have hv : v.carrier=A.first:=by
    simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,v,hself,dite_true,Bool.false_eq_true,ite_false]
    rfl
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center)∈v.carrier:=by
    rw [hv,_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalSelfSideSplit.first]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_right_mem _ _
  have hsub : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment v.leftEndpoint v.rightEndpoint⊆
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment A.left (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center)):=by
    rw [←v.carrier_eq_endpoints,hv]
    rfl
  have he:=original_closed_subsegment_endpoint v.leftEndpoint v.rightEndpoint A.left _ _
    A.left_ne_center hsub (v.carrier_eq_endpoints ▸ hc) (Or.inr rfl)
  rcases he with he|he
  · exact Or.inl ⟨v,he.symm⟩
  · exact Or.inr ⟨v,he.symm⟩

/-- Every original finite vertex remains a genuine marked endpoint after the actual self-side subdivision. -/
theorem originalFiniteVertex_mem_refinedEndpointSet
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) (hx : IsFuchsianPolygonVertex P D x) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈originalRefinedEndpointSet hD := by
  obtain ⟨S,T,hS,hT,hST,hxS,hxT⟩:=hD.vertex_exists_two_sides hx
  let s : FuchsianPolygonSides P D:=⟨S,hS⟩
  let t : FuchsianPolygonSides P D:=⟨T,hT⟩
  obtain ⟨v,hv,hxv⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.exists_over_side hD s _
    ((mem_fuchsianSideClosedModel_finite s x).mpr hxS)
  obtain ⟨w,hw,hxw⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.exists_over_side hD t _
    ((mem_fuchsianSideClosedModel_finite t x).mpr hxT)
  apply v.inter_subset_endpointSet w _ ⟨hxv,hxw⟩
  intro he
  exact hST (congrArg Subtype.val (hv.symm.trans ((congrArg (fun a : OriginalRefinedSide hD=>a.val.1) he).trans hw)))

/-- Every actual elliptic fixed point in the original polygon closure is retained among the genuine marked corners, including the self-side centers. -/
theorem originalEllipticPoint_mem_refinedEndpointSet
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) (hx : x∈closure D) (he : ¬IsAccidentalFuchsianPoint P x) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈originalRefinedEndpointSet hD := by
  by_cases hv : IsFuchsianPolygonVertex P D x
  · exact originalFiniteVertex_mem_refinedEndpointSet hD x hv
  obtain ⟨s,hxs,hself,_hi,hfix,_ho,_hc⟩:=hD.nonvertex_elliptic_self_paired hx hv he
  let A:=originalSelfSideSplit hD s hself
  let f:=fuchsianSideElement hD s
  have hne : f≠1:=(fuchsianSideElement_spec hD s).1
  have hE : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f.val:=P.fixing_nonidentity_elliptic x f hfix hne
  obtain ⟨z,hz,hzu⟩:=elliptic_disc_existsUnique_fixed f.val hE P.asFuchsianDisc.isDisc (P.image_eq f)
  have hA : A.center=x:=(hzu A.center (congrArg Subtype.val A.center_fixed)).trans
    (hzu x (congrArg Subtype.val hfix)).symm
  rw [←hA]
  exact originalSelfSideSplit_center_endpoint hD s hself

/-- The genuine elliptic marked classes inside the actual raw endpoint quotient. -/
def originalRawEllipticClass {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (J : PolygonalCircle)
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD)
    (q : Quotient (originalRawCornerSetoid J e)) : Prop :=
    ∃i : ZMod J.n,∃x : P.domain.carrier,
      Quotient.mk (originalRawCornerSetoid J e) i=q ∧
      originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x) ∧
      ¬IsAccidentalFuchsianPoint P x

/-- A selected genuine representative retains its actual cyclic index and original finite point. -/
def originalRawEllipticRepresentative {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (J : PolygonalCircle)
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD)
    (q : {q : Quotient (originalRawCornerSetoid J e) // originalRawEllipticClass hD J hv e q}) :
    Σi : ZMod J.n,{x : P.domain.carrier //
      Quotient.mk (originalRawCornerSetoid J e) i=q.val ∧
      originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x) ∧
      ¬IsAccidentalFuchsianPoint P x} := by
  apply Classical.choice
  obtain ⟨i,x,hi,hx,he⟩:=q.property
  exact ⟨⟨i,⟨x,hi,hx,he⟩⟩⟩

/-- The selected representative is an actual elliptic fixed point of the original whole group. -/
def originalRawEllipticPoint {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (J : PolygonalCircle)
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD)
    (q : {q : Quotient (originalRawCornerSetoid J e) // originalRawEllipticClass hD J hv e q}) :
    fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic := by
  let r:=originalRawEllipticRepresentative hD J hv e q
  refine ⟨r.2.val.val,fun _=>r.2.val.property,?_⟩
  obtain ⟨f,hf,hfix⟩:=not_not.mp r.2.property.2.2
  exact ⟨f.val,f.property,hf,congrArg Subtype.val hfix⟩

/-- The actual maximal cyclic conjugacy class of a genuine elliptic raw marked class. -/
def originalRawEllipticClassMap {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (J : PolygonalCircle)
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) :
    {q : Quotient (originalRawCornerSetoid J e) // originalRawEllipticClass hD J hv e q} →
      FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic :=
    fun q=>(fuchsianCyclicConjugacyClassesEquiv P.asFuchsianDisc .elliptic).symm
      (Quotient.mk _ (originalRawEllipticPoint hD J hv e q))

theorem originalRawEllipticClassMap_injective {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier) :
    Function.Injective (originalRawEllipticClassMap hD J hv e) := by
  intro q r hqr
  have hquot : Quotient.mk (MulAction.orbitRel H (fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic))
      (originalRawEllipticPoint hD J hv e q)=
      Quotient.mk _ (originalRawEllipticPoint hD J hv e r):=
    (fuchsianCyclicConjugacyClassesEquiv P.asFuchsianDisc .elliptic).symm.injective hqr
  have horb:=Quotient.exact hquot.symm
  change originalRawEllipticPoint hD J hv e r∈MulAction.orbit H (originalRawEllipticPoint hD J hv e q) at horb
  obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp horb
  let a:=originalRawEllipticRepresentative hD J hv e q
  let b:=originalRawEllipticRepresentative hD J hv e r
  have hcoord :=congrArg (fun p : fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic=>p.val) hg
  have hab : g•a.2.val=b.2.val:=Subtype.ext hcoord
  have hraw:Relation.EqvGen (originalRawCornerStep J e) a.1 b.1:=
    (originalFiniteCorner_orbit_iff_rawCornerChain hD ha J hc hv e hs a.1 b.1 a.2.val b.2.val
      a.2.property.2.1 b.2.property.2.1).mpr ⟨g,hab⟩
  apply Subtype.ext
  exact a.2.property.1.symm.trans ((Quotient.sound hraw).trans b.2.property.1)

/-- The interior coordinate of an actual original elliptic fixed point. -/
def originalEllipticPointCoordinate {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (p : fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic) :
    P.domain.carrier:=⟨p.val,p.property.1 rfl⟩

theorem originalEllipticPointCoordinate_not_accidental {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (p : fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic) :
    ¬IsAccidentalFuchsianPoint P (originalEllipticPointCoordinate P p) := by
  intro ha
  obtain ⟨f,hfH,hf,hfix⟩:=p.property.2
  exact ha ⟨⟨f,hfH⟩,hf,Subtype.ext hfix⟩

theorem originalRawEllipticClassMap_surjective {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier) :
    Function.Surjective (originalRawEllipticClassMap hD J hv e) := by
  let E:=fuchsianCyclicConjugacyClassesEquiv P.asFuchsianDisc .elliptic
  have hrep (p : fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic) :
      ∃q,Quotient.mk (MulAction.orbitRel H (fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic))
        (originalRawEllipticPoint hD J hv e q)=Quotient.mk _ p := by
    let x:=originalEllipticPointCoordinate P p
    obtain ⟨y,hy,hyo⟩:=hD.locallyFinite.fundamental.cycle_nonempty x
    obtain ⟨g,hgy⟩:=MulAction.mem_orbit_iff.mp hyo
    have hcoord : originalEllipticPointCoordinate P (g•p)=y:=hgy
    have he : ¬IsAccidentalFuchsianPoint P y:=hcoord ▸ originalEllipticPointCoordinate_not_accidental P (g•p)
    have hmark:=originalEllipticPoint_mem_refinedEndpointSet hD y hy he
    rw [←range_originalCyclicVertex hD J hv] at hmark
    obtain ⟨i,hi⟩:=hmark
    let q : {q : Quotient (originalRawCornerSetoid J e) // originalRawEllipticClass hD J hv e q}:=
      ⟨Quotient.mk _ i,⟨i,y,rfl,hi,he⟩⟩
    let a:=originalRawEllipticRepresentative hD J hv e q
    have hai : Relation.EqvGen (originalRawCornerStep J e) a.1 i:=
      Quotient.exact a.2.property.1
    obtain ⟨k,hk⟩:=(originalFiniteCorner_orbit_iff_rawCornerChain hD ha J hc hv e hs a.1 i a.2.val y
      a.2.property.2.1 hi).mp hai
    have hpoint : k•originalRawEllipticPoint hD J hv e q=g•p:=by
      apply Subtype.ext
      change k.val.val a.2.val.val=g.val.val p.val
      exact (congrArg Subtype.val hk).trans (congrArg Subtype.val hgy).symm
    refine ⟨q,Quotient.sound ?_⟩
    change originalRawEllipticPoint hD J hv e q∈MulAction.orbit H p
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨k⁻¹*g,?_⟩
    rw [mul_smul,←hpoint,inv_smul_smul]
  intro c
  obtain ⟨p,hp⟩:=Quotient.exists_rep (E c)
  obtain ⟨q,hq⟩:=hrep p
  refine ⟨q,E.injective ?_⟩
  change E (E.symm _) = _
  rw [E.apply_symm_apply,hq,hp]

/-- Actual elliptic raw corner classes are precisely all original maximal elliptic cyclic conjugacy classes. -/
def originalRawEllipticClassesEquiv {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier) :
    {q : Quotient (originalRawCornerSetoid J e) // originalRawEllipticClass hD J hv e q} ≃
      FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic :=
    Equiv.ofBijective (originalRawEllipticClassMap hD J hv e)
      ⟨originalRawEllipticClassMap_injective hD ha J hc hv e hs,
        originalRawEllipticClassMap_surjective hD ha J hc hv e hs⟩

/-- The actual maximal cyclic class order equals the genuine original point stabilizer order. -/
theorem originalRawEllipticClassMap_order {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (J : PolygonalCircle)
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD)
    (q : {q : Quotient (originalRawCornerSetoid J e) // originalRawEllipticClass hD J hv e q}) :
    fuchsianEllipticClassOrder P.asFuchsianDisc (originalRawEllipticClassMap hD J hv e q)=
      fuchsianPointOrder P (originalRawEllipticRepresentative hD J hv e q).2.val := by
  let r:=originalRawEllipticRepresentative hD J hv e q
  change Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H
    r.2.val.val)=Nat.card (MulAction.stabilizer H r.2.val)
  exact Nat.card_congr (P.stabilizerEquivBoundary r.2.val).symm.toEquiv

/-- The geometric raw weight is the reciprocal order of its actual original elliptic conjugacy class. -/
theorem originalRawEllipticClass_weight {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier)
    (q : {q : Quotient (originalRawCornerSetoid J e) // originalRawEllipticClass hD J hv e q}) :
    originalRawCornerClassWeight hD ha J hc hv e hs q.val=
      1/(fuchsianEllipticClassOrder P.asFuchsianDisc (originalRawEllipticClassMap hD J hv e q) : ℝ) := by
  let r:=originalRawEllipticRepresentative hD J hv e q
  rw [←r.2.property.1,originalRawCornerClassWeight_finite hD ha J hc hv e hs r.1 r.2.val r.2.property.2.1,
    originalRawEllipticClassMap_order]

/-- The genuine elliptic-class count is the actual number of nontrivial finite raw endpoint classes. -/
theorem originalRawEllipticClasses_card {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier) :
    Nat.card {q : Quotient (originalRawCornerSetoid J e) // originalRawEllipticClass hD J hv e q}=
      Nat.card (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic) :=
    Nat.card_congr (originalRawEllipticClassesEquiv hD ha J hc hv e hs)

end LowDimensionalTopology.Geometry.Fuchsian
