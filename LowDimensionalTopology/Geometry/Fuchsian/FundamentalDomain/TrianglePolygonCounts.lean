/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalRawCuspClasses
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalFiniteAreaCompletionHomeomorph
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleSignatureCharacterization
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalRawEllipticOrderLists
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.DiscPolygonConjugation
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenCoreApproximation
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.ApproximationPolygons
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CanonicalHandleEuler
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
open Set Topology
open scoped OnePoint Pointwise Complex.UnitDisc Classical
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
open LeanEval.Topology.ClassificationOfSurfaces.Moise
local instance trianglePolygonSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex:=borel Mobius.ExtendedComplex
local instance trianglePolygonSphereBorel : BorelSpace Mobius.ExtendedComplex:=⟨rfl⟩

/-- A genuine accidental vertex has at least three different original
cycle points: its three literal incident tile labels cannot collapse
because its actual point stabilizer is trivial. -/
theorem trianglePolygon_accidental_vertex_cycle_three
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (x:P.domain.carrier) (hx:IsFuchsianPolygonVertex P D x)
    (ha:IsAccidentalFuchsianPoint P x) : 3≤Nat.card ↥(fuchsianPolygonCycle P D x) := by
  classical
  let : Fintype ↥(fuchsianPolygonCycle P D x):=(hD.locallyFinite.cycle_finite x).fintype
  have hinj:Function.Injective (fun g:H=>g • x):=by
    intro a b hab
    change a • x=b • x at hab
    have hh:(b⁻¹*a) • x=x:=by rw [mul_smul,hab,inv_smul_smul]
    exact (inv_mul_eq_one.mp ((isAccidentalFuchsianPoint_iff_no_stabilizer P x).mp ha _ hh)).symm
  obtain ⟨g,h,hg,hh,hgh,he⟩:=hx
  have hmem:x∈closure D∩fuchsianDomainTile P D g∩fuchsianDomainTile P D h:=he.symm ▸mem_singleton x
  have hgc:g⁻¹ • x∈closure D:=by
    have hz:=hmem.1.2
    simpa only [fuchsianDomainTile,mem_smul_set_iff_inv_smul_mem] using hz
  have hhc:h⁻¹ • x∈closure D:=by
    have hz:=hmem.2
    simpa only [fuchsianDomainTile,mem_smul_set_iff_inv_smul_mem] using hz
  let l:Fin 3→H:=![1,g⁻¹,h⁻¹]
  have hgi:g⁻¹≠1:=inv_ne_one.mpr hg
  have hhi:h⁻¹≠1:=inv_ne_one.mpr hh
  have hghi:g⁻¹≠h⁻¹:=inv_injective.ne hgh
  have hl:Function.Injective l:=by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [l]
  let f:Fin 3→↥(fuchsianPolygonCycle P D x):=fun i=>⟨l i • x,by
    refine ⟨?_,MulAction.mem_orbit_iff.mpr ⟨l i,rfl⟩⟩
    fin_cases i
    · simpa [l] using hmem.1.1
    · exact hgc
    · exact hhc⟩
  have hf:Function.Injective f:=by
    intro i j hij
    exact hl (hinj (congrArg Subtype.val hij))
  simpa only [Fintype.card_fin,Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hf

/-- Without self-pairing, every genuine marked finite endpoint is a true
original polygon vertex, not an inserted midpoint. -/
theorem trianglePolygon_marked_finite_vertex
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNo:∀s:FuchsianPolygonSides P D,fuchsianPairedSide hD s≠s)
    (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hD)
    (i:ZMod J.n) (x:P.domain.carrier)
    (hi:originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)) :
    IsFuchsianPolygonVertex P D x := by
  have hmark:=originalCyclicVertex_mem_endpointSet hD J hv i
  rw [hi] at hmark
  rcases hmark with ⟨v,hv⟩|⟨v,hv⟩
  · have hs:fuchsianSideClosedModel v.val.1=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment v.leftEndpoint v.rightEndpoint:=by
      simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,
        dite_eq_right (hNo v.val.1)] using v.carrier_eq_endpoints
    exact original_finite_side_endpoint_vertex hD v.val.1 _ _ v.endpoints_ne hs x hv.symm
  · have hs:fuchsianSideClosedModel v.val.1=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment v.rightEndpoint v.leftEndpoint:=by
      simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,
        dite_eq_right (hNo v.val.1)] using
        v.carrier_eq_endpoints.trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_comm _ _)
    exact original_finite_side_endpoint_vertex hD v.val.1 _ _ v.endpoints_ne.symm hs x hv.symm

/-- A genuine nonspecial raw endpoint class has at least three original
corners. The actual finite cycle bijection retains the complete class. -/
theorem trianglePolygon_weight_one_class_three
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (hNo:∀s:FuchsianPolygonSides P D,fuchsianPairedSide hD s≠s)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hD)
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
  let x:=P.finiteCoordinate.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (originalCyclicVertex hD J hv q.out) hn)
  have hx:originalCyclicVertex hD J hv q.out=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x):=by
    rw [P.finiteCoordinate.apply_symm_apply]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ hn).symm
  have hpoint:fuchsianPointOrder P x=1:=by
    have hh:=originalRawCornerClassOrder_finite hD ha J hc hv e hs q.out x hx
    rw [Quotient.out_eq,ho] at hh
    exact hh.symm
  have hthree:=trianglePolygon_accidental_vertex_cycle_three hD x
    (trianglePolygon_marked_finite_vertex hD hNo J hv q.out x hx)
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

/-- The original polygon's actual Euler count and its three actual special
classes force four or six sides; accidental classes retain at least three
literal corners each. -/
theorem trianglePolygon_cyclic_count
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (hNo:∀s:FuchsianPolygonSides P D,fuchsianPairedSide hD s≠s)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (hχ:_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic
      (originalCyclicPresentation J e).presentation=2)
    (hthree:Nat.card {q:Quotient (originalRawCornerSetoid J e) //
      originalRawCornerClassWeight hD ha J hc hv e hs q≠1}=3) : J.n=4 ∨ J.n=6 := by
  classical
  let Q:=Quotient (originalRawCornerSetoid J e)
  let w:Q→ℝ:=originalRawCornerClassWeight hD ha J hc hv e hs
  let A:=Fintype.card {q:Q // w q=1}
  let V:=Fintype.card Q
  have hpart:A+3=V:=by
    have hcard:=Fintype.card_subtype_compl (fun q:Q=>w q=1)
    have hle:Fintype.card {q:Q // w q=1}≤Fintype.card Q:=Fintype.card_subtype_le _
    rw [Nat.card_eq_fintype_card] at hthree
    change Fintype.card {q:Q // ¬w q=1}=3 at hthree
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
  change (2:ℤ)=(V:ℤ)-(J.n/2:ℕ)+1 at heuler
  omega

/-- Every actual ideal boundary point of a finitely generated first-kind
polygon is genuinely parabolic. No cusp-label hypothesis is supplied. -/
theorem trianglePolygon_ideal_parabolic
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (ht:IsMobiusTriangleGroup H)
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (u:Circle) (hu:(u:ℂ)∈fuchsianPolygonIdealBoundary P D) :
    ∃f:H,f≠1 ∧_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val ∧f.val.val ((u:ℂ):Mobius.ExtendedComplex)=((u:ℂ):Mobius.ExtendedComplex) := by
  have hFG:=mobiusTriangleGroup_finitelyGenerated ht
  have hfirst:=mobiusTriangleGroup_actual_firstKind P.asFuchsianDisc ht
  have hf:((u:ℂ):Mobius.ExtendedComplex)∈fuchsianLimitSet H:=by
    rw [hfirst]
    change ((u:ℂ):Mobius.ExtendedComplex)∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle,
      _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe, sub_zero]
    exact Circle.norm_coe u
  rcases finitelyGenerated_split_limitSet P hFG (u:ℂ) hf with hpar|hApprox
  · obtain ⟨f,hf,hfix⟩:=hpar
    exact ⟨f,fun he=>hf.1 (congrArg Subtype.val he),hf,hfix⟩
  · exact False.elim (fuchsian_pointOfApproximation_not_polygon_closure P hD (u:ℂ)
      hApprox ((mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D (u:ℂ)).mp hu).2)

/-- The actual special raw classes partition precisely into genuine ideal
classes and genuine elliptic classes, retaining all repetitions. -/
def trianglePolygon_specialRawEquiv
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier) :
    {q:Quotient (originalRawCornerSetoid J e)//originalRawCornerClassWeight hD ha J hc hv e hs q≠1}≃
      {q:Quotient (originalRawCornerSetoid J e)//originalRawCornerClassWeight hD ha J hc hv e hs q=0}⊕
      {q:Quotient (originalRawCornerSetoid J e)//originalRawEllipticClass hD J hv e q} := by
  classical
  let w:=originalRawCornerClassWeight hD ha J hc hv e hs
  have hne (q:Quotient (originalRawCornerSetoid J e)) (hq:originalRawEllipticClass hD J hv e q):w q≠1:=
    ne_of_lt ((originalRawEllipticClass_iff_weight hD ha J hc hv e hs q).mp hq).2
  let f:{q:Quotient (originalRawCornerSetoid J e)//w q≠1}→
      {q:Quotient (originalRawCornerSetoid J e)//w q=0}⊕
      {q:Quotient (originalRawCornerSetoid J e)//originalRawEllipticClass hD J hv e q}:=
    fun q=>if hz:w q.val=0 then Sum.inl ⟨q.val,hz⟩ else
      Sum.inr ⟨q.val,(originalRawEllipticClass_iff_weight hD ha J hc hv e hs q.val).mpr (by
        have hb:=originalRawCornerClassWeight_bounds hD ha J hc hv e hs q.val
        exact ⟨lt_of_le_of_ne hb.1 (Ne.symm hz),lt_of_le_of_ne hb.2 q.property⟩)⟩
  let g:{q:Quotient (originalRawCornerSetoid J e)//w q=0}⊕
      {q:Quotient (originalRawCornerSetoid J e)//originalRawEllipticClass hD J hv e q}→
      {q:Quotient (originalRawCornerSetoid J e)//w q≠1}:=fun q=>match q with
      | Sum.inl q=>⟨q.val,by rw [q.property];exact zero_ne_one⟩
      | Sum.inr q=>⟨q.val,hne q.val q.property⟩
  refine ⟨f,g,?_,?_⟩
  · intro q
    dsimp only [f]
    split_ifs <;> rfl
  · intro q
    cases q with
    | inl q=>
      dsimp only [g,f]
      rw [dite_eq_left (show w q.val=0 from q.property)]
    | inr q=>
      have hz:w q.val≠0:=ne_of_gt
        ((originalRawEllipticClass_iff_weight hD ha J hc hv e hs q.val).mp q.property).1
      dsimp only [g,f]
      rw [dite_eq_right hz]

/-- Every convex original polygon of the actual triangle group, in the
original whole-disc geometric coordinate, has four or six original sides.
Finite area and every ideal parabolic label are derived internally. -/
theorem trianglePolygon_geometric_count
    {H:Subgroup Mobius.complexMobiusGroup}
    (D₀:FuchsianDisc H)
    (ht:IsMobiusTriangleGroup H)
    {L:Set (geometricDiscData D₀).domain.carrier}
    (hL:IsConvexFuchsianPolygon (geometricDiscData D₀) L)
    (hNo:∀s:FuchsianPolygonSides (geometricDiscData D₀) L,fuchsianPairedSide hL s≠s) :
    Nat.card (FuchsianPolygonSides (geometricDiscData D₀) L)=4 ∨
      Nat.card (FuchsianPolygonSides (geometricDiscData D₀) L)=6 := by
  classical
  let P:=geometricDiscData D₀
  have ht':IsMobiusTriangleGroup (geometricDiscGroup D₀):=ht.conjugation (geometricDiscNormalizer D₀)
  have ha:P.area L≠⊤:=firstKind_finitelyGenerated_area_ne_top P
    (mobiusTriangleGroup_actual_firstKind P.asFuchsianDisc ht')
    (mobiusTriangleGroup_finitelyGenerated ht') hL.locallyFinite.fundamental
  obtain ⟨J,e,hc,hv,hs⟩:=finite_area_original_cyclic_side_model hL ha
  obtain ⟨n,S,hr,_hint⟩:=finite_area_polygon_actual_cyclic_model hL ha
  have hpar:=trianglePolygon_ideal_parabolic P ht' hL
  obtain ⟨orders,cusps,hSig,hmarks⟩:=mobiusTriangleGroup_actual_three_marked_signature D₀ ht
  obtain ⟨g,hg,hχ⟩:=originalCyclicCompletion_genus_euler D₀ hL ha J hc hv e hs S hr hpar
  have hg0:g=0:=_root_.LowDimensionalTopology.Geometry.Surfaces.hasTopologicalGenus_unique hg hSig.topologicalGenus
  have hχ2:_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic (originalCyclicPresentation J e).presentation=2:=by
    simpa only [hg0,Nat.cast_zero,mul_zero,sub_zero] using hχ
  have hcusp:=Nat.card_congr (originalRawIdealCuspEquiv D₀ hL ha J hc hv e hs S hr hpar)
  have hell:=originalRawEllipticClasses_card hL ha J hc hv e hs
  rw [geometricDiscData_asFuchsianDisc,fuchsianCyclicClassConjugacyEquiv_natCard] at hell
  have hthree:Nat.card {q:Quotient (originalRawCornerSetoid J e)//
      originalRawCornerClassWeight hL ha J hc hv e hs q≠1}=3:=by
    rw [Nat.card_congr (trianglePolygon_specialRawEquiv hL ha J hc hv e hs),Nat.card_sum,hcusp,hell]
    rw [←hSig.cuspCount,←hSig.orders_length]
    omega
  have hcount:=trianglePolygon_cyclic_count hL ha hNo J hc hv e hs hχ2 hthree
  have hnum:=originalCyclic_sideCount hL ha J e
  have hself:Nat.card {s:FuchsianPolygonSides P L // fuchsianPairedSide hL s=s}=0:=by
    let : IsEmpty {s:FuchsianPolygonSides P L // fuchsianPairedSide hL s=s}:=⟨fun s=>hNo s.val s.property⟩
    exact Nat.card_of_isEmpty
  rw [hself,add_zero] at hnum
  rwa [hnum] at hcount

/-- Whole-model conjugation preserves the actual number of original sides
and the absence of self-pairing. The correspondence is determined by the
true side element and its inverse, not by supplied labels. -/
theorem trianglePolygon_equivariant_side_count
    {H K:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (Q:UnitDiscFuchsianGroup K)
    (E:H≃*K) (f:P.domain.carrier≃ₜQ.domain.carrier)
    (he:∀g x,f (g • x)=E g • f x)
    (harea:MeasureTheory.Measure.map f P.area=Q.area)
    (hiso:letI:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
      Isometry (fun z:Complex.UnitDisc=>Q.finiteCoordinate (f (P.finiteCoordinate.symm z))))
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNo:∀s:FuchsianPolygonSides P D,fuchsianPairedSide hD s≠s) :
    ∃hQ:IsConvexFuchsianPolygon Q (f '' D),
      Nat.card (FuchsianPolygonSides P D)=Nat.card (FuchsianPolygonSides Q (f '' D)) ∧
      ∀t:FuchsianPolygonSides Q (f '' D),fuchsianPairedSide hQ t≠t := by
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
  refine ⟨hQ,Nat.card_congr (Equiv.ofBijective φ ⟨hinj,hsurj⟩),?_⟩
  intro t hpair
  obtain ⟨s,rfl⟩:=hsurj t
  apply hNo s
  apply fuchsianSideElement_injective hD
  apply E.injective
  rw [fuchsianSideElement_paired,map_inv,←hφ s]
  have hh:=congrArg (fuchsianSideElement hQ) hpair
  rwa [fuchsianSideElement_paired] at hh

/-- Every convex fundamental polygon for an actual triangle group has
four or six original sides, under the source no-self-paired-side convention.
Neither finite area nor finite side number is an added hypothesis. -/
theorem triangle_group_polygon_four_or_six
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (ht:IsMobiusTriangleGroup H)
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNo:∀s:FuchsianPolygonSides P D,fuchsianPairedSide hD s≠s) :
    Nat.card (FuchsianPolygonSides P D)=4 ∨ Nat.card (FuchsianPolygonSides P D)=6 := by
  let D₀:=P.asFuchsianDisc
  let q:=geometricDiscNormalizer D₀
  have hq:q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=geometricDiscNormalizer_image D₀
  let Q:=P.conjugateData q hq
  let f:=P.conjugateCoordinate q hq
  obtain ⟨hQ,hcard,hNo'⟩:=trianglePolygon_equivariant_side_count P Q
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H) f (P.conjugateCoordinate_equivariant q hq)
    (P.conjugateCoordinate_area_map q hq) (P.conjugateCoordinate_isometry q hq) hD hNo
  have hgeom:IsConvexFuchsianPolygon (geometricDiscData D₀) (f '' D):=hQ
  have hNgeom:∀s:FuchsianPolygonSides (geometricDiscData D₀) (f '' D),fuchsianPairedSide hgeom s≠s:=hNo'
  have hh:=trianglePolygon_geometric_count D₀ ht hgeom hNgeom
  rwa [←hcard] at hh

end LowDimensionalTopology.Geometry.Fuchsian
