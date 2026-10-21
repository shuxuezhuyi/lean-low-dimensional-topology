/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicPreGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalFiniteCornerCycles
/-!
# Finite polygon points and word gluing

Every finite point in the polygon closure has a canonical preface
representative. On these representatives the stored word relation is exactly
the original whole-group orbit relation, including self-pairing centers.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Pointwise
section FinitePointGluing
variable {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)

/-- Taking the actual model closure adds only genuine ideal points; its finite part is precisely the original topological closure. -/
theorem originalFiniteClosedModel_mem_iff (x:P.domain.carrier) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate
      x)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D)↔
      x∈closure D := by
  have E:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.comp P.finiteCoordinate.isEmbedding
  have he:=E.closure_eq_preimage_closure_image D
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,image_image,Function.comp_def,mem_preimage] using
    (Set.ext_iff.mp he x).symm

/-- The canonical original stored-face representative of every actual finite polygon-closure point. -/
def originalFinitePrePoint (x:closure D) :
    (originalCyclicPresentation J e).presentation.PolygonalPreRealization :=
  (originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs).symm
    ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate
      x.val),(originalFiniteClosedModel_mem_iff x.val).mpr x.property⟩

/-- Its original coordinates are unchanged. -/
theorem originalFinitePrePoint_coe (x:closure D) :
    (originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs
      (originalFinitePrePoint hD ha J hc hv e hs x)).val=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x.val) := by
  exact congrArg Subtype.val ((originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs).apply_symm_apply _)

/-- A genuine finite side step has both endpoints in the actual polygon closure. -/
theorem originalFiniteSidePointStep_closure {x y:P.domain.carrier}
    (hxy:fuchsianSidePointStep hD x y) : x∈closure D∧y∈closure D := by
  have hxclosure {a b:P.domain.carrier} (h:fuchsianSidePointStep hD a b) : a∈closure D:=by
    obtain ⟨s,hx,_⟩:=h
    obtain ⟨g,_hg,he⟩:=s.property.1
    exact (he ▸ hx).1
  exact ⟨hxclosure hxy,hxclosure (originalFiniteSidePointStep_symm hD hxy)⟩

/-- Actual original finite side chains preserve membership of the original polygon closure. -/
theorem originalFiniteSidePointChain_closure {x y:P.domain.carrier}
    (hxy:Relation.EqvGen (fuchsianSidePointStep hD) x y) :
    x∈closure D↔y∈closure D := by
  induction hxy with
  | rel a b hab =>
      have h:=originalFiniteSidePointStep_closure hD hab
      exact ⟨fun _=>h.2,fun _=>h.1⟩
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- Every genuine original finite side step is an actual stored-word gluing, including steps crossing a self-pairing center. -/
theorem originalFiniteSidePointStep_wordGluing
    {x y:P.domain.carrier} (hxy:fuchsianSidePointStep hD x y)
    (a b:(originalCyclicPresentation J e).presentation.PolygonalPreRealization)
    (ha':(originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs a).val=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x))
    (hb':(originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs b).val=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate y)) :
    (originalCyclicPresentation J e).presentation.PolygonalGluingRel
      (originalCyclicPresentation J e).valid a b := by
  obtain ⟨s,hx,rfl⟩:=hxy
  obtain ⟨v,hvs,hxv⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.exists_over_side hD s
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate
      x)) ((mem_fuchsianSideClosedModel_finite s x).mpr hx)
  let k:Fin J.n:=(originalCyclicFinIndex J).symm (e.symm v)
  have hkv:e (originalCyclicFinIndex J k)=v:=by simp only [k,Equiv.apply_symm_apply]
  have hxk:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈
      range (originalCyclicSideParam hD J hv e k) := by
    rw [range_originalCyclicSideParam hD J hv e hs,hkv]
    exact hxv
  obtain ⟨t,ht⟩:=hxk
  let o:=(originalCyclicOccurrenceIndex J e).symm k
  have ho:originalCyclicOccurrenceIndex J e o=k:=(originalCyclicOccurrenceIndex J e).apply_symm_apply k
  have hclosed:=originalCyclicPresentation_closed J e o.edge
  have hn:¬(originalCyclicPresentation J e).presentation.IsBoundaryEdge o.edge:=by
    rw [IsBoundaryEdge,hclosed]
    omega
  obtain ⟨pairing,hpair⟩:=(originalCyclicPresentation J e).valid.exists_pairing_source o hn
  let B:=originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs
  have hsource:(B (pairing.identification.source.point t)).val=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x):=by
    change (B (((originalCyclicPresentation J e).presentation.occurrenceSide pairing.source).point t)).val=_
    rw [originalCyclicPreClosedModelHomeomorph_side,hpair,ho]
    exact ht
  have htarget:(B (pairing.identification.target.point (pairing.identification.parameter t))).val=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate ((fuchsianSideElement hD s)⁻¹•x)):=by
    rw [←originalCyclicBoundaryPairing_geometric hD ha J hc hv e hs pairing t,hsource]
    change (P.compactifiedAction (fuchsianSideElement hD
      (e (originalCyclicFinIndex J (originalCyclicOccurrenceIndex J e pairing.source))).val.1)⁻¹).closedMap
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x))=_
    rw [hpair,ho,hkv,hvs,P.compactifiedAction_finite]
  have haeq:a=pairing.identification.source.point t:=
    B.injective (Subtype.ext (ha'.trans hsource.symm))
  have hbeq:b=pairing.identification.target.point (pairing.identification.parameter t):=
    B.injective (Subtype.ext (hb'.trans htarget.symm))
  rw [haeq,hbeq]
  exact Relation.EqvGen.rel _ _ (PolygonGluing.Generator.glue pairing.identification
    (pairing_identification_mem (originalCyclicPresentation J e).valid pairing) t)
/-- Entire genuine finite side chains lift to the literal stored-word equivalence relation on the canonical original representatives. -/
theorem originalFiniteSidePointChain_wordGluing {x y:P.domain.carrier}
    (hxy:Relation.EqvGen (fuchsianSidePointStep hD) x y) :
    ∀hx:x∈closure D,∀hy:y∈closure D,
    (originalCyclicPresentation J e).presentation.PolygonalGluingRel
      (originalCyclicPresentation J e).valid
      (originalFinitePrePoint hD ha J hc hv e hs ⟨x,hx⟩)
      (originalFinitePrePoint hD ha J hc hv e hs ⟨y,hy⟩) := by
  induction hxy with
  | rel a b hab =>
      intro ha' hb'
      exact originalFiniteSidePointStep_wordGluing hD ha J hc hv e hs hab _ _
        (originalFinitePrePoint_coe hD ha J hc hv e hs _) (originalFinitePrePoint_coe hD ha J hc hv e hs _)
  | refl a => intro ha' ha'';exact Relation.EqvGen.refl _
  | symm a b _ ih => intro ha' hb';exact Relation.EqvGen.symm _ _ (ih hb' ha')
  | trans a b c hab _ ih ih' =>
      intro ha' hc'
      have hb':b∈closure D:=(originalFiniteSidePointChain_closure hD hab).mp ha'
      exact Relation.EqvGen.trans _ _ _ (ih ha' hb') (ih' hb' hc')

/-- A literal original group orbit identification between any finite polygon-closure points is already forced by the unchanged stored side word. -/
theorem originalFiniteOrbit_wordGluing (x y:closure D) (g:H) (hg:g•x.val=y.val) :
    (originalCyclicPresentation J e).presentation.PolygonalGluingRel
      (originalCyclicPresentation J e).valid
      (originalFinitePrePoint hD ha J hc hv e hs x)
      (originalFinitePrePoint hD ha J hc hv e hs y) :=
  originalFiniteSidePointChain_wordGluing hD ha J hc hv e hs
    (hD.side_point_chain_of_orbit x.val y.val x.property y.property g hg) x.property y.property

/-- Every identification made by the literal stored word is a genuine original whole-group sphere identification; the proof uses all actual stored generators. -/
theorem originalWordGluing_sphereOrbit
    {a b:(originalCyclicPresentation J e).presentation.PolygonalPreRealization}
    (hab:(originalCyclicPresentation J e).presentation.PolygonalGluingRel
      (originalCyclicPresentation J e).valid a b) :
    ∃g:H,g.val.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended
        (originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs a).val)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs b).val := by
  change Relation.EqvGen (PolygonGluing.Generator
    ((originalCyclicPresentation J e).presentation.polygonalIdentifications
      (originalCyclicPresentation J e).valid)) a b at hab
  induction hab with
  | rel a b h =>
      cases h with
      | glue identification hi t =>
          obtain ⟨pairing,rfl⟩:=hi
          refine ⟨(fuchsianSideElement hD
            (e (originalCyclicFinIndex J (originalCyclicOccurrenceIndex J e pairing.source))).val.1)⁻¹,?_⟩
          exact (P.compactifiedAction_sphere _ _).symm.trans
            (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended
              (originalCyclicBoundaryPairing_geometric hD ha J hc hv e hs pairing t))
  | refl a => exact ⟨1,rfl⟩
  | symm a b _ ih =>
      obtain ⟨g,hg⟩:=ih
      refine ⟨g⁻¹,?_⟩
      change g.val.val.symm _=_
      rw [←hg,g.val.val.symm_apply_apply]
  | trans a b c _ _ ih ih' =>
      obtain ⟨g,hg⟩:=ih
      obtain ⟨h,hh⟩:=ih'
      refine ⟨h*g,?_⟩
      change h.val.val (g.val.val _)=_
      rw [hg,hh]

/-- On the full actual finite polygon closure, the unchanged stored-word relation is exactly the original whole-group orbit relation. This concerns every finite point, not only marked corners. -/
theorem originalFiniteWordGluing_iff_orbit (x y:closure D) :
    (originalCyclicPresentation J e).presentation.PolygonalGluingRel
      (originalCyclicPresentation J e).valid
      (originalFinitePrePoint hD ha J hc hv e hs x)
      (originalFinitePrePoint hD ha J hc hv e hs y)↔∃g:H,g•x.val=y.val := by
  constructor
  · intro hxy
    obtain ⟨g,hg⟩:=originalWordGluing_sphereOrbit hD ha J hc hv e hs hxy
    rw [originalFinitePrePoint_coe,originalFinitePrePoint_coe,
      originalFinitePoint_closedModel_sphere,originalFinitePoint_closedModel_sphere] at hg
    exact ⟨g,Subtype.ext hg⟩
  · rintro ⟨g,hg⟩
    exact originalFiniteOrbit_wordGluing hD ha J hc hv e hs x y g hg

end FinitePointGluing
end LowDimensionalTopology.Geometry.Fuchsian
