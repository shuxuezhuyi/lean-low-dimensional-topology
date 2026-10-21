/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.TrianglePolygonCounts
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.ClosedSegmentTransport
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.GenericDirichletAccidental
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.GenericDirichletHorocycles
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
open Set Topology MeasureTheory Filter
open scoped OnePoint Pointwise Complex.UnitDisc Classical
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LeanEval.Topology.ClassificationOfSurfaces.Moise
local instance originalSideBoundsSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance originalSideBoundsSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

/--
Literal original corners and actual Euler characteristic give all three
bounds; the zero-special-class case retains a nonempty
accidental class and yields the stronger lower bound four times genus.
-/
theorem cofinitePolygon_cyclic_bounds
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (hNo:∀s:FuchsianPolygonSides P D,fuchsianPairedSide hD s≠s)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (g m:ℕ) (hχ:_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic
      (originalCyclicPresentation J e).presentation=2-2*(g:ℤ))
    (hspecial:Nat.card {q:Quotient (originalRawCornerSetoid J e) //
      originalRawCornerClassWeight hD ha J hc hv e hs q≠1}=m) :
    J.n+6≤12*g+4*m ∧ (m=0→4*g≤J.n) ∧ (0<m→4*g+2*m≤J.n+2) := by
  classical
  let Q:=Quotient (originalRawCornerSetoid J e)
  let w:Q→ℝ:=originalRawCornerClassWeight hD ha J hc hv e hs
  let A:=Fintype.card {q:Q // w q=1}
  let V:=Fintype.card Q
  have hpart:A+m=V:=by
    have hcard:=Fintype.card_subtype_compl (fun q:Q=>w q=1)
    have hle:Fintype.card {q:Q // w q=1}≤Fintype.card Q:=Fintype.card_subtype_le _
    rw [Nat.card_eq_fintype_card] at hspecial
    change Fintype.card {q:Q // ¬w q=1}=m at hspecial
    omega
  let N:Q→ℕ:=fun q=>Fintype.card {i:ZMod J.n // Quotient.mk (originalRawCornerSetoid J e) i=q}
  have hsum:(∑q:Q,N q)=J.n:=by
    have he:=Fintype.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk (originalRawCornerSetoid J e)))
    simpa only [Fintype.card_sigma,ZMod.card] using he
  have hN (q:Q):1+(if w q=1 then 2 else 0)≤N q:=by
    by_cases hq:w q=1
    · simp only [hq,ite_true]
      simpa only [Nat.card_eq_fintype_card] using
        trianglePolygon_weight_one_class_three hD ha hNo J hc hv e hs q hq
    · simp only [hq,ite_false,add_zero]
      apply Fintype.card_pos_iff.mpr
      exact ⟨q.out,Quotient.out_eq q⟩
  have hweights:(∑q:Q,if w q=1 then 2 else 0)=2*A:=by
    simp [Finset.sum_ite,A,Fintype.card_subtype,mul_comm]
  have hineq:V+2*A≤J.n:=by
    have hh:=Finset.sum_le_sum (fun q (_:q∈(Finset.univ:Finset Q))=>hN q)
    rw [hsum] at hh
    simpa only [V,Nat.cast_id,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,mul_one,hweights] using hh
  have heuler:=originalCyclicPresentation_euler_count J e
  have hvertices:=originalCyclicVertex_card_rawCorners J e
  rw [hχ,hvertices,Nat.card_eq_fintype_card] at heuler
  have heven:=originalCyclicPresentation_edgeCount_twice J e
  change (2:ℤ)-2*(g:ℤ)=(V:ℤ)-(J.n/2:ℕ)+1 at heuler
  have hvpos:0<V:=by
    let : Nonempty Q:=⟨Quotient.mk (originalRawCornerSetoid J e) 0⟩
    exact Fintype.card_pos
  omega


theorem cofinitePolygon_ideal_parabolic
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup
      H) (hFG:H.FG) (hfirst:P.asFuchsianDisc.IsFirstKind)
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (u:Circle) (hu:(u:ℂ)∈fuchsianPolygonIdealBoundary P D) :
    ∃f:H,f≠1 ∧_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val ∧f.val.val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  have hf:((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈fuchsianLimitSet H:=by
    rw [hfirst]
    change ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle,_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe,sub_zero]
    exact Circle.norm_coe u
  rcases finitelyGenerated_split_limitSet P hFG (u:ℂ) hf with hpar|hApprox
  · obtain ⟨f,hf,hfix⟩:=hpar
    exact ⟨f,fun he=>hf.1 (congrArg Subtype.val he),hf,hfix⟩
  · exact False.elim (fuchsian_pointOfApproximation_not_polygon_closure P hD (u:ℂ)
      hApprox ((mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D (u:ℂ)).mp hu).2)


/-- Universal bounds for the actual original whole-disc polygon, derived from its genuine given signature. -/
theorem cofinitePolygon_geometric_bounds
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D₀:FuchsianDisc
      H) (hFG:H.FG) (hfirst:D₀.IsFirstKind)
    (g:ℕ) (orders:List ℕ) (cusps:ℕ) (hSig:HasCofiniteFuchsianSignature D₀ g orders cusps)
    {L:Set (geometricDiscData D₀).domain.carrier}
    (hL:IsConvexFuchsianPolygon (geometricDiscData D₀) L)
    (hNo:∀s:FuchsianPolygonSides (geometricDiscData D₀) L,fuchsianPairedSide hL s≠s) :
    let N:=Nat.card (FuchsianPolygonSides (geometricDiscData D₀) L)
    let m:=orders.length+cusps
    N+6≤12*g+4*m ∧ (m=0→4*g≤N) ∧ (0<m→4*g+2*m≤N+2) := by
  classical
  let P:=geometricDiscData D₀
  let q:=geometricDiscNormalizer D₀
  let E:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  have hNE:=D₀.firstKind_nonElementary hfirst
  have hNE':_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (geometricDiscGroup
    D₀):=hNE.conjugation q
  let : Group.FG H:=(Group.fg_iff_subgroup_fg H).mpr hFG
  let : Group.FG (geometricDiscGroup D₀):=Group.fg_of_surjective (f:=E.toMonoidHom) E.surjective
  have hFG':(geometricDiscGroup D₀).FG:=(Group.fg_iff_subgroup_fg _).mp inferInstance
  have hfirst':P.asFuchsianDisc.IsFirstKind:=by
    change (geometricDiscData D₀).asFuchsianDisc.IsFirstKind
    rw [geometricDiscData_asFuchsianDisc]
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.IsFirstKind,fuchsianLimitSet_eq_nonElementary _
      hNE',
      ←nielsen_mobiusLimitSet_conjugation H q,←fuchsianLimitSet_eq_nonElementary H hNE,hfirst,
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.nielsenConjugate_carrier]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).image_frontier D₀.carrier
  have ha:P.area L≠⊤:=firstKind_finitelyGenerated_area_ne_top P hfirst' hFG' hL.locallyFinite.fundamental
  obtain ⟨J,e,hc,hv,hs⟩:=finite_area_original_cyclic_side_model hL ha
  obtain ⟨n,S,hr,_hint⟩:=finite_area_polygon_actual_cyclic_model hL ha
  have hpar:=cofinitePolygon_ideal_parabolic P hFG' hfirst' hL
  obtain ⟨g',hg,hχ⟩:=originalCyclicCompletion_genus_euler D₀ hL ha J hc hv e hs S hr hpar
  have hgg:g'=g:=_root_.LowDimensionalTopology.Geometry.Surfaces.hasTopologicalGenus_unique hg hSig.topologicalGenus
  have hχg:_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic (originalCyclicPresentation J e).presentation=2-2*(g:ℤ):=by
    simpa only [hgg] using hχ
  have hcusp:=Nat.card_congr (originalRawIdealCuspEquiv D₀ hL ha J hc hv e hs S hr hpar)
  have hell:=originalRawEllipticClasses_card hL ha J hc hv e hs
  rw [geometricDiscData_asFuchsianDisc,fuchsianCyclicClassConjugacyEquiv_natCard] at hell
  have hthree:Nat.card {q:Quotient (originalRawCornerSetoid J e)//
      originalRawCornerClassWeight hL ha J hc hv e hs q≠1}=orders.length+cusps:=by
    rw [Nat.card_congr (trianglePolygon_specialRawEquiv hL ha J hc hv e hs),Nat.card_sum,hcusp,hell]
    rw [←hSig.cuspCount,←hSig.orders_length]
    omega
  have hcount:=cofinitePolygon_cyclic_bounds hL ha hNo J hc hv e hs g (orders.length+cusps) hχg hthree
  have hnum:=originalCyclic_sideCount hL ha J e
  have hself:Nat.card {s:FuchsianPolygonSides P L // fuchsianPairedSide hL s=s}=0:=by
    let : IsEmpty {s:FuchsianPolygonSides P L // fuchsianPairedSide hL s=s}:=⟨fun s=>hNo s.val s.property⟩
    exact Nat.card_of_isEmpty
  rw [hself,add_zero] at hnum
  rwa [hnum] at hcount


/-- The three original inequalities for every actual original polygon. Attainability is proved separately. -/
theorem convexPolygon_sideCard_bounds_of_cofinite_signature
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup
      H) (hFG:H.FG) (hfirst:P.asFuchsianDisc.IsFirstKind)
    (g:ℕ) (orders:List ℕ) (cusps:ℕ) (hSig:HasCofiniteFuchsianSignature P.asFuchsianDisc g orders cusps)
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNo:∀s:FuchsianPolygonSides P D,fuchsianPairedSide hD s≠s) :
    let N:=Nat.card (FuchsianPolygonSides P D)
    let m:=orders.length+cusps
    N≤12*g+4*m-6 ∧ (m=0→4*g≤N) ∧ (0<m→4*g+2*m-2≤N) := by
  let D₀:=P.asFuchsianDisc
  let q:=geometricDiscNormalizer D₀
  have hq:q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=geometricDiscNormalizer_image D₀
  let Q:=P.conjugateData q hq
  let f:=P.conjugateCoordinate q hq
  obtain ⟨hQ,hcard,hNo'⟩:=trianglePolygon_equivariant_side_count P Q
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
      H) f (P.conjugateCoordinate_equivariant q hq)
    (P.conjugateCoordinate_area_map q hq) (P.conjugateCoordinate_isometry q hq) hD hNo
  have hgeom:IsConvexFuchsianPolygon (geometricDiscData D₀) (f '' D):=hQ
  have hNgeom:∀s:FuchsianPolygonSides (geometricDiscData D₀) (f '' D),fuchsianPairedSide hgeom s≠s:=hNo'
  have hh:=cofinitePolygon_geometric_bounds D₀ hFG hfirst g orders cusps hSig hgeom hNgeom
  rw [←hcard] at hh
  dsimp only
  omega

/-- A marked accidental finite corner is an actual original vertex even
when genuine self-paired sides have been subdivided at their fixed center. -/
theorem originalRefined_accidental_corner_vertex
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (i:ZMod J.n) (x:P.domain.carrier)
    (hi:originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (P.finiteCoordinate x))
    (hAcc:IsAccidentalFuchsianPoint P x) : IsFuchsianPolygonVertex P D x := by
  classical
  let X:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)
  have hpair (a b c d:𝕔𝔻)
      (he:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a
        b=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment c d) :
      ({a,b}:Set 𝕔𝔻)={c,d}:=by
    have hk:=congrArg (fun S:Set 𝕔𝔻=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' S) he
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment] at hk
    have hp:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.complex_segment_endpoints_eq _ _ _ _ hk
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.image_injective
    simpa only [image_insert_eq,image_singleton] using hp
  have hmark:X∈originalRefinedEndpointSet hD:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate
      x)∈originalRefinedEndpointSet hD
    rw [←hi]
    exact originalCyclicVertex_mem_endpointSet hD J hv i
  have hex:∃v:OriginalRefinedSide hD,X=v.leftEndpoint∨X=v.rightEndpoint:=by
    rcases hmark with ⟨v,hv⟩|⟨v,hv⟩
    · exact ⟨v,Or.inl hv.symm⟩
    · exact ⟨v,Or.inr hv.symm⟩
  obtain ⟨v,hv⟩:=hex
  have hext (a b:𝕔𝔻) (he:v.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a b):X=a∨X=b:=by
    have hp:=hpair _ _ _ _ (v.carrier_eq_endpoints.symm.trans he)
    have hm:X∈({v.leftEndpoint,v.rightEndpoint}:Set 𝕔𝔻):=by
      simpa only [mem_insert_iff,mem_singleton_iff] using hv
    rw [hp] at hm
    exact hm
  by_cases hself:fuchsianPairedSide hD v.val.1=v.val.1
  · let A:=originalSelfSideSplit hD v.val.1 hself
    have hne:X≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate A.center):=by
      intro he
      have hx:x=A.center:=P.finiteCoordinate.injective (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective he)
      have hfree:=(isAccidentalFuchsianPoint_iff_no_stabilizer P x).mp hAcc
      exact (fuchsianSideElement_spec hD v.val.1).1
        (hfree _ (hx.symm ▸ A.center_fixed))
    by_cases hb:v.val.2=true
    · have he:v.carrier=A.second:=by
        simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,hself,dite_true,hb,ite_true]
        rfl
      have hx:X=A.right:=(hext _ _ he).resolve_left hne
      exact (original_finite_side_endpoint_vertices hD v.val.1 _ _ A.endpoints_ne A.side_eq).2 x hx
    · have hf:v.val.2=false:=Bool.eq_false_iff.mpr hb
      have he:v.carrier=A.first:=by
        simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,hself,dite_true,hf,Bool.false_eq_true,ite_false]
        rfl
      have hx:X=A.left:=(hext _ _ he).resolve_right hne
      exact original_finite_side_endpoint_vertex hD v.val.1 _ _ A.endpoints_ne A.side_eq x hx
  · have hs:fuchsianSideClosedModel v.val.1=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment v.leftEndpoint v.rightEndpoint:=by
      simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,dite_eq_right
        hself] using v.carrier_eq_endpoints
    rcases hv with hv|hv
    · exact original_finite_side_endpoint_vertex hD v.val.1 _ _ v.endpoints_ne hs x hv
    · exact (original_finite_side_endpoint_vertices hD v.val.1 _ _ v.endpoints_ne hs).2 x hv

/-- A genuine refined accidental class still contains at least three original marked corners; inserted self-side centers are elliptic. -/
theorem originalRefined_weight_one_class_three
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (q:Quotient (originalRawCornerSetoid J e))
    (hw:originalRawCornerClassWeight hD ha J hc hv e hs q=1) :
    3≤Nat.card {i:ZMod J.n // Quotient.mk (originalRawCornerSetoid J e) i=q} := by
  classical
  have ho:originalRawCornerClassOrder hD J hv e q=1:=by
    rw [originalRawCornerClassWeight_order] at hw
    have hc':(originalRawCornerClassOrder hD J hv e q:ℝ)=1:=by
      simpa only [one_div,inv_eq_one] using hw
    exact_mod_cast hc'
  have hn:‖(originalCyclicVertex hD J hv q.out:ℂ)‖<1:=
    (originalRawCornerClassOrder_pos_iff hD J hv e q).mp (by omega)
  let x:=P.finiteCoordinate.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint
    (originalCyclicVertex hD J hv q.out) hn)
  have hx:originalCyclicVertex hD J hv q.out=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x):=by
    rw [P.finiteCoordinate.apply_symm_apply]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ hn).symm
  have hpoint:fuchsianPointOrder P x=1:=by
    have hh:=originalRawCornerClassOrder_finite hD ha J hc hv e hs q.out x hx
    rw [Quotient.out_eq,ho] at hh
    exact hh.symm
  have hthree:=trianglePolygon_accidental_vertex_cycle_three hD x
    (originalRefined_accidental_corner_vertex hD J hv q.out x hx
      ((isAccidentalFuchsianPoint_iff_pointOrder_one P x).mpr hpoint))
    ((isAccidentalFuchsianPoint_iff_pointOrder_one P x).mpr hpoint)
  have hcard:=originalRawFiniteCornerClass_card hD ha J hc hv e hs q.out x hx
  have heq:{i:ZMod J.n // Quotient.mk (originalRawCornerSetoid J e) i=q}≃
      {i:ZMod J.n // Relation.EqvGen (originalRawCornerStep J e) q.out i}:=
    Equiv.subtypeEquivRight (fun i=>by
      constructor
      · intro hi
        exact Relation.EqvGen.symm _ _ (Quotient.exact (hi.trans (Quotient.out_eq q).symm))
      · intro hi
        exact (Quotient.sound (Relation.EqvGen.symm _ _ hi)).trans (Quotient.out_eq q))
  rwa [←hcard,←Nat.card_congr heq] at hthree


/-- A raw finite fiber has exactly the original whole-orbit cycle's size. -/
theorem originalRefined_fiber_card_finite
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (i:ZMod J.n) (x:P.domain.carrier)
    (hi:originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (P.finiteCoordinate x)) :
    Nat.card {j:ZMod J.n // Quotient.mk (originalRawCornerSetoid J e) j=Quotient.mk _ i}=
      fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x) := by
  let E:{j:ZMod J.n // Quotient.mk (originalRawCornerSetoid J e) j=Quotient.mk _ i}≃
      {j:ZMod J.n // Relation.EqvGen (originalRawCornerStep J e) i j}:=
    Equiv.subtypeEquivRight (fun j=>⟨fun h=>Relation.EqvGen.symm _ _ (Quotient.exact h),
      fun h=>Quotient.sound (Relation.EqvGen.symm _ _ h)⟩)
  rw [Nat.card_congr E,originalRawFiniteCornerClass_card hD ha J hc hv e hs i x hi]
  rfl

/-- An ideal marked corner lies on the literal ideal boundary of the original polygon. -/
theorem originalRefined_ideal_corner_boundary
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (i:ZMod J.n) (hn:‖(originalCyclicVertex hD J hv i:ℂ)‖=1) :
    (originalCyclicVertex hD J hv i:ℂ)∈fuchsianPolygonIdealBoundary P D := by
  let p:=originalCyclicVertex hD J hv i
  have hp:p∈(e i).carrier:=(originalCyclicVertex_mem_side_iff hD J hv e hs i i).mpr (Or.inl rfl)
  have hK:=fuchsianSideClosedModel_klein_subset_polygon (e i).val.1
    (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ((e
      i).carrier_subset_original hp))
  have he:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p=(p:ℂ):=congrArg (fun
    z:𝕔𝔻=>(z:ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed p hn)
  rw [he] at hK
  exact (compactKlein_ideal_mem_iff P D (p:ℂ) hn).mp hK

/-- A singleton genuine ideal cycle has only one literal raw corner in its
class. This uses the true sphere action, rather than an ideal-label assumption. -/
theorem originalRefined_ideal_fiber_one
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (i:ZMod J.n) (hn:‖(originalCyclicVertex hD J hv i:ℂ)‖=1)
    (hcycle:fuchsianPolygonIdealCycle P D ((originalCyclicVertex hD J hv
      i:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
      {((originalCyclicVertex hD J hv i:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)}) :
    Nat.card {j:ZMod J.n // Quotient.mk (originalRawCornerSetoid J e) j=Quotient.mk _ i}=1 := by
  classical
  let F:={j:ZMod J.n // Quotient.mk (originalRawCornerSetoid J e) j=Quotient.mk _ i}
  have hi:F:=⟨i,rfl⟩
  have heq (j:F):j.val=i:=by
    have hji:=Quotient.exact j.property
    have hij:=Relation.EqvGen.symm _ _ hji
    have hnj:‖(originalCyclicVertex hD J hv j.val:ℂ)‖=1:=by
      have hf:=(originalRawCorner_finite_iff_rawChain hD ha J hc hv e hs hij)
      have hnot:¬‖(originalCyclicVertex hD J hv i:ℂ)‖<1:=by rw [hn];exact lt_irrefl 1
      exact le_antisymm (originalCyclicVertex hD J hv j.val).norm_le_one (le_of_not_gt (mt hf.mpr hnot))
    obtain ⟨g,hg⟩:=originalRawCornerChain_sphereOrbit hD ha J hc hv e hs hij
    have hb:=originalRefined_ideal_corner_boundary hD J hv e hs j.val hnj
    have hm:((originalCyclicVertex hD J hv j.val:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈
        fuchsianPolygonIdealCycle P D ((originalCyclicVertex hD J hv i:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
      refine ⟨mem_image_of_mem _ hb,MulAction.mem_orbit_iff.mpr ⟨g,?_⟩⟩
      exact hg
    rw [hcycle,mem_singleton_iff] at hm
    exact originalCyclicVertex_injective hD J hv
      (Subtype.ext (OnePoint.coe_injective hm))
  let : Nonempty F:=⟨hi⟩
  let : Subsingleton F:=⟨fun a b=>Subtype.ext ((heq a).trans (heq b).symm)⟩
  exact Nat.card_unique

/-- For almost every genuine center, the original Dirichlet polygon with
its actual self-side center subdivisions has exactly the source upper
number of sides. No generic cycle-size assumptions are added. -/
theorem cofinitePolygon_geometric_dirichlet_upper_ae
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D₀:FuchsianDisc
      H) (hFG:H.FG) (hfirst:D₀.IsFirstKind)
    (g:ℕ) (orders:List ℕ) (cusps:ℕ) (hSig:HasCofiniteFuchsianSignature D₀ g orders cusps) :
    ∀ᵐw ∂(geometricDiscData D₀).area,
      ∃hD:IsConvexFuchsianPolygon (geometricDiscData D₀) (dirichletDomain (geometricDiscData D₀) w),
        Nat.card (OriginalRefinedSide hD)=12*g+4*(orders.length+cusps)-6 := by
  classical
  let P:=geometricDiscData D₀
  let q:=geometricDiscNormalizer D₀
  let E:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  have hNE:=D₀.firstKind_nonElementary hfirst
  have hNE':_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (geometricDiscGroup
    D₀):=hNE.conjugation q
  let : Group.FG H:=(Group.fg_iff_subgroup_fg H).mpr hFG
  let : Group.FG (geometricDiscGroup D₀):=Group.fg_of_surjective (f:=E.toMonoidHom) E.surjective
  have hFG':(geometricDiscGroup D₀).FG:=(Group.fg_iff_subgroup_fg _).mp inferInstance
  have hfirst':P.asFuchsianDisc.IsFirstKind:=by
    change (geometricDiscData D₀).asFuchsianDisc.IsFirstKind
    rw [geometricDiscData_asFuchsianDisc]
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.IsFirstKind,fuchsianLimitSet_eq_nonElementary _
      hNE',
      ←nielsen_mobiusLimitSet_conjugation H q,←fuchsianLimitSet_eq_nonElementary H hNE,hfirst,
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.nielsenConjugate_carrier]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).image_frontier D₀.carrier
  filter_upwards [ae_dirichlet_elliptic_cycleLength_eq_one P,ae_dirichlet_accidental_vertex_cycleLength_eq_three P,
    ae_dirichlet_proper_ideal_vertex_parabolic_fixer_and_singleton_cycle P] with w hEll hAcc hIde
  let L:=dirichletDomain P w
  let hD:IsConvexFuchsianPolygon P L:=dirichletDomain_isConvexFuchsianPolygon P w hEll.1
  have ha:P.area L≠⊤:=firstKind_finitelyGenerated_area_ne_top P hfirst' hFG' hD.locallyFinite.fundamental
  obtain ⟨J,e,hc,hv,hs⟩:=finite_area_original_cyclic_side_model hD ha
  obtain ⟨n,S,hr,_hint⟩:=finite_area_polygon_actual_cyclic_model hD ha
  have hpar:=cofinitePolygon_ideal_parabolic P hFG' hfirst' hD
  obtain ⟨g',hg,hχ⟩:=originalCyclicCompletion_genus_euler D₀ hD ha J hc hv e hs S hr hpar
  have hgg:g'=g:=_root_.LowDimensionalTopology.Geometry.Surfaces.hasTopologicalGenus_unique hg hSig.topologicalGenus
  rw [hgg] at hχ
  have hcusp:=Nat.card_congr (originalRawIdealCuspEquiv D₀ hD ha J hc hv e hs S hr hpar)
  have hell:=originalRawEllipticClasses_card hD ha J hc hv e hs
  rw [geometricDiscData_asFuchsianDisc,fuchsianCyclicClassConjugacyEquiv_natCard] at hell
  let Q:=Quotient (originalRawCornerSetoid J e)
  let ω:Q→ℝ:=originalRawCornerClassWeight hD ha J hc hv e hs
  let A:=Fintype.card {q:Q // ω q=1}
  let V:=Fintype.card Q
  let m:=orders.length+cusps
  have hspecial:Nat.card {q:Q // ω q≠1}=m:=by
    rw [Nat.card_congr (trianglePolygon_specialRawEquiv hD ha J hc hv e hs),Nat.card_sum,hcusp,hell]
    rw [←hSig.cuspCount,←hSig.orders_length]
    omega
  have hpart:A+m=V:=by
    have hcard:=Fintype.card_subtype_compl (fun q:Q=>ω q=1)
    have hle:Fintype.card {q:Q // ω q=1}≤Fintype.card Q:=Fintype.card_subtype_le _
    rw [Nat.card_eq_fintype_card] at hspecial
    change Fintype.card {q:Q // ¬ω q=1}=m at hspecial
    omega
  let N:Q→ℕ:=fun q=>Fintype.card {i:ZMod J.n // Quotient.mk (originalRawCornerSetoid J e) i=q}
  have hN (q:Q):N q=if ω q=1 then 3 else 1:=by
    by_cases hz:ω q=0
    · have hni:= (originalRawCornerClassWeight_zero_iff_ideal hD ha J hc hv e hs q).mp hz
      let u:Circle:=⟨(originalCyclicVertex hD J hv q.out:ℂ),mem_sphere_zero_iff_norm.mpr hni⟩
      have hp:originalCyclicVertex hD J hv q.out∈(e q.out).carrier:=
        (originalCyclicVertex_mem_side_iff hD J hv e hs q.out q.out).mpr (Or.inl rfl)
      have hu:IsProperFuchsianInfiniteVertex P L u:=original_ideal_side_point_isProper hD ha
        (e q.out).val.1 _ ((e q.out).carrier_subset_original hp) hni
      obtain ⟨_k,_hk,_hpar,_hfix,hcycle⟩:=hIde.2 u hu
      have hf:=originalRefined_ideal_fiber_one hD ha J hc hv e hs q.out hni hcycle
      rw [Quotient.out_eq] at hf
      simpa only [hz,zero_ne_one,ite_false,Nat.card_eq_fintype_card] using hf
    · have hn:‖(originalCyclicVertex hD J hv q.out:ℂ)‖<1:=lt_of_le_of_ne
        (originalCyclicVertex hD J hv q.out).norm_le_one
        (fun hn=>hz ((originalRawCornerClassWeight_zero_iff_ideal hD ha J hc hv e hs q).mpr hn))
      let x:=P.finiteCoordinate.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint
        (originalCyclicVertex hD J hv q.out) hn)
      have hx:originalCyclicVertex hD J hv q.out=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x):=by
        rw [P.finiteCoordinate.apply_symm_apply]
        exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ hn).symm
      have hw:=originalRawCornerClassWeight_finite hD ha J hc hv e hs q.out x hx
      rw [Quotient.out_eq] at hw
      have hf:=originalRefined_fiber_card_finite hD ha J hc hv e hs q.out x hx
      rw [Quotient.out_eq] at hf
      by_cases ho:ω q=1
      · have hpoint:fuchsianPointOrder P x=1:=by
          have hh:(fuchsianPointOrder P x:ℝ)=1:=by
            simpa only [one_div,inv_eq_one] using hw.symm.trans ho
          exact_mod_cast hh
        have hacc:IsAccidentalFuchsianPoint P x:=(isAccidentalFuchsianPoint_iff_pointOrder_one P x).mpr hpoint
        have hxv:=originalRefined_accidental_corner_vertex hD J hv q.out x hx hacc
        have hc3:=hAcc.2 x hxv hacc
        rw [hc3] at hf
        simpa only [ho,ite_true,Nat.card_eq_fintype_card] using hf
      · have hne:¬IsAccidentalFuchsianPoint P x:=by
          intro he
          apply ho
          change originalRawCornerClassWeight hD ha J hc hv e hs q=1
          rw [hw,(isAccidentalFuchsianPoint_iff_pointOrder_one P x).mp he]
          norm_num
        have hxell:x∈fuchsianEllipticPoints P:=by
          intro hfree
          exact hne ((isAccidentalFuchsianPoint_iff_no_stabilizer P x).mpr hfree)
        rw [hEll.2 x hxell] at hf
        simpa only [ho,ite_false,Nat.card_eq_fintype_card] using hf
  have hsum:(∑q:Q,N q)=J.n:=by
    have he:=Fintype.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk (originalRawCornerSetoid J e)))
    simpa only [Fintype.card_sigma,ZMod.card] using he
  have hn:J.n=3*A+m:=by
    rw [←hsum]
    simp_rw [hN]
    have hsum3:(∑q:Q,if ω q=1 then 3 else 0)=3*A:=by
      simp [Finset.sum_ite,A,Fintype.card_subtype,mul_comm]
    have hsum1:(∑q:Q,if ω q=1 then 0 else 1)=m:=by
      have hh:=(Fintype.card_subtype_compl (fun q:Q=>ω q=1))
      have hle:=Fintype.card_subtype_le (fun q:Q=>ω q=1)
      simp only [Finset.sum_ite,Finset.sum_const_zero,zero_add,Finset.sum_const,
        nsmul_eq_mul,mul_one,←Fintype.card_subtype,Nat.cast_id]
      omega
    have hsplit:(∑q:Q,if ω q=1 then 3 else 1)=
        (∑q:Q,if ω q=1 then 3 else 0)+(∑q:Q,if ω q=1 then 0 else 1):=by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _hq
      split_ifs <;> rfl
    rw [hsplit,hsum3,hsum1]
  have heuler:=originalCyclicPresentation_euler_count J e
  rw [hχ,originalCyclicVertex_card_rawCorners J e,Nat.card_eq_fintype_card] at heuler
  have heven:=originalCyclicPresentation_edgeCount_twice J e
  have hside:Nat.card (OriginalRefinedSide hD)=J.n:=by
    have h:=Nat.card_congr ((originalCyclicFinIndex J).trans e)
    simpa only [Nat.card_fin] using h.symm
  refine ⟨hD,?_⟩
  rw [hside]
  change (2:ℤ)-2*(g:ℤ)=(V:ℤ)-(J.n/2:ℕ)+1 at heuler
  change J.n=12*g+4*m-6
  omega

/-- Whole-model side labels remain the literal side-element labels in every actual coordinate. -/
theorem cofinitePolygon_exists_side_equiv
    {H K:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup
      H) (Q:UnitDiscFuchsianGroup K)
    (E:H≃*K) (f:P.domain.carrier≃ₜQ.domain.carrier)
    (he:∀g x,f (g • x)=E g • f x)
    (harea:MeasureTheory.Measure.map f P.area=Q.area)
    (hiso:letI:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
      Isometry (fun z:Complex.UnitDisc=>Q.finiteCoordinate (f (P.finiteCoordinate.symm z))))
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    :
    let hQ:=equivariant_fuchsian_polygon_image P Q E f he harea hiso hD
    ∃F:FuchsianPolygonSides P D≃FuchsianPolygonSides Q (f '' D),
      ∀s,fuchsianSideElement hQ (F s)=E (fuchsianSideElement hD s) := by
  classical
  let hQ:=equivariant_fuchsian_polygon_image P Q E f he harea hiso hD
  have hmap (s:FuchsianPolygonSides P D):∃t:FuchsianPolygonSides Q (f '' D),
      fuchsianSideElement hQ t=E (fuchsianSideElement hD s):=by
    obtain ⟨_,t,ht⟩:=equivariant_fuchsian_side_element_image P Q E f he harea hiso hD s
    exact ⟨t,ht⟩
  choose φ hφ using hmap
  have hinj:Function.Injective φ:=by
    intro s t hst
    apply fuchsianSideElement_injective hD
    apply E.injective
    rw [←hφ s,←hφ t,hst]
  have hsurj:Function.Surjective φ:=by
    intro t
    have hp:=equivariant_fuchsian_side_element_preimage P Q E f he harea hiso hQ t
    have hset:f ⁻¹' (f '' D)=D:=f.injective.preimage_image D
    rw [hset] at hp
    obtain ⟨_,s,hs⟩:=hp
    refine ⟨s,?_⟩
    apply fuchsianSideElement_injective hQ
    rw [hφ s,hs,E.apply_symm_apply]
  exact ⟨Equiv.ofBijective φ ⟨hinj,hsurj⟩,hφ⟩

/-- True side-element transport also transports the actual fixed-center
subdivision, so the source no-self-pair count is coordinate independent. -/
theorem cofinitePolygon_refined_side_count_image
    {H K:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup
      H) (Q:UnitDiscFuchsianGroup K)
    (E:H≃*K) (f:P.domain.carrier≃ₜQ.domain.carrier)
    (he:∀g x,f (g • x)=E g • f x)
    (harea:MeasureTheory.Measure.map f P.area=Q.area)
    (hiso:letI:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
      Isometry (fun z:Complex.UnitDisc=>Q.finiteCoordinate (f (P.finiteCoordinate.symm z))))
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) :
    let hQ:=equivariant_fuchsian_polygon_image P Q E f he harea hiso hD
    Nat.card (OriginalRefinedSide hD)=Nat.card (OriginalRefinedSide hQ) := by
  classical
  let hQ:=equivariant_fuchsian_polygon_image P Q E f he harea hiso hD
  obtain ⟨F,hF⟩:=cofinitePolygon_exists_side_equiv P Q E f he harea hiso hD
  have hpair (s:FuchsianPolygonSides P D):F (fuchsianPairedSide hD s)=fuchsianPairedSide hQ (F s):=by
    apply fuchsianSideElement_injective hQ
    rw [hF,fuchsianSideElement_paired,fuchsianSideElement_paired,hF,map_inv]
  let T:=Equiv.prodCongr F (Equiv.refl Bool)
  have hp (v:FuchsianPolygonSides P D×Bool):
      (v.2=true→fuchsianPairedSide hD v.1=v.1)↔
      ((T v).2=true→fuchsianPairedSide hQ (T v).1=(T v).1):=by
    change (v.2=true→fuchsianPairedSide hD v.1=v.1)↔
      (v.2=true→fuchsianPairedSide hQ (F v.1)=F v.1)
    constructor
    · intro h hb
      rw [←hpair,h hb]
    · intro h hb
      exact F.injective ((hpair v.1).trans (h hb))
  exact Nat.card_congr (Equiv.subtypeEquiv T hp)

/-- Genuine equivariant disc isometries carry the literal metric
Dirichlet regions and their original centers exactly to one another. -/
theorem cofinitePolygon_dirichlet_image
    {H K:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup
      H) (Q:UnitDiscFuchsianGroup K)
    (E:H≃*K) (f:P.domain.carrier≃ₜQ.domain.carrier)
    (he:∀g x,f (g • x)=E g • f x)
    (hiso:letI:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
      Isometry (fun z:Complex.UnitDisc=>Q.finiteCoordinate (f (P.finiteCoordinate.symm z))))
    (w:P.domain.carrier) : f '' dirichletDomain P w=dirichletDomain Q (f w) := by
  have hd (x y:P.domain.carrier):Q.hyperbolicDist (f x) (f y)=P.hyperbolicDist x y:=by
    rw [Q.hyperbolicDist_eq_discPathDist,P.hyperbolicDist_eq_discPathDist]
    let cofiniteSideCountNativeMetric:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
    have hh:=hiso.dist_eq (P.finiteCoordinate x) (P.finiteCoordinate y)
    simpa only [P.finiteCoordinate.symm_apply_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance] using hh
  have hm (x:P.domain.carrier):f x∈dirichletDomain Q (f w)↔x∈dirichletDomain P w:=by
    constructor
    · intro hx g hg
      have hne:E g≠1:=fun h=>hg (E.injective (h.trans E.map_one.symm))
      have hh:=hx (E g) hne
      change Q.hyperbolicDist (f x) (f w)<Q.hyperbolicDist (f x) (E g • f w) at hh
      rw [←he,hd,hd] at hh
      exact hh
    · intro hx k hk
      have hne:E.symm k≠1:=fun h=>hk (E.symm.injective (h.trans E.symm.map_one.symm))
      have hh:=hx (E.symm k) hne
      change Q.hyperbolicDist (f x) (f w)<Q.hyperbolicDist (f x) (k • f w)
      rw [←E.apply_symm_apply k,←he,hd,hd]
      exact hh
  ext z
  obtain ⟨x,rfl⟩:=f.surjective z
  rw [f.injective.mem_set_image]
  exact (hm x).symm

/--
The almost-everywhere sharp upper count, for the
unchanged original unit-disc group and original genuine centers. Genuine
self-paired sides are divided at their actual elliptic centers as in the
source convention, rather than assumed absent for generic centers.
-/
theorem ae_dirichlet_refined_sideCard_eq_signature_bound
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H) (hFG:H.FG)
    (hfirst:P.asFuchsianDisc.IsFirstKind) (g:ℕ) (orders:List ℕ) (cusps:ℕ)
    (hSig:HasCofiniteFuchsianSignature P.asFuchsianDisc g orders cusps) :
    ∀ᵐw ∂P.area,∃hD:IsConvexFuchsianPolygon P (dirichletDomain P w),
      Nat.card (OriginalRefinedSide hD)=12*g+4*(orders.length+cusps)-6 := by
  let D₀:=P.asFuchsianDisc
  let q:=geometricDiscNormalizer D₀
  have hq:q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=geometricDiscNormalizer_image D₀
  let Q:=P.conjugateData q hq
  let f:=P.conjugateCoordinate q hq
  let E:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  have hAE:=cofinitePolygon_geometric_dirichlet_upper_ae D₀ hFG hfirst g orders cusps hSig
  have hmap:MeasureTheory.Measure.map f P.area=Q.area:=P.conjugateCoordinate_area_map q hq
  have hmp:MeasureTheory.MeasurePreserving f P.area Q.area:=⟨f.continuous.measurable,hmap⟩
  have hpull:=hmp.quasiMeasurePreserving.ae hAE
  filter_upwards [hpull,ae_dirichlet_elliptic_cycleLength_eq_one P] with w hw hEll
  obtain ⟨hQ,hcount⟩:=hw
  let hD:IsConvexFuchsianPolygon P (dirichletDomain P w):=dirichletDomain_isConvexFuchsianPolygon P w hEll.1
  have he:=P.conjugateCoordinate_equivariant q hq
  have hi:=P.conjugateCoordinate_isometry q hq
  have hregion:=cofinitePolygon_dirichlet_image P Q E f he hi w
  have hcard:=cofinitePolygon_refined_side_count_image P Q E f he hmap hi hD
  have hcongr {L M:Set Q.domain.carrier} (hL:IsConvexFuchsianPolygon Q L)
      (hM:IsConvexFuchsianPolygon Q M) (hLM:L=M):
      Nat.card (OriginalRefinedSide hL)=Nat.card (OriginalRefinedSide hM):=by
    subst M
    rfl
  exact ⟨hD,hcard.trans ((hcongr
    (equivariant_fuchsian_polygon_image P Q E f he hmap hi hD) hQ hregion).trans hcount)⟩

end LowDimensionalTopology.Geometry.Fuchsian
