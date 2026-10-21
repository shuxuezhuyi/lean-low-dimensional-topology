/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalFiniteCornerSteps
/-!
# Finite side chains and raw corner classes

Side-point chains lift to the marked raw corner indices in both directions.
For finite marked corners, raw corner equivalence is exactly the original
whole-group orbit relation.
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
open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- A full genuine finite original side chain lifts through the actual marked corner indices; both directions are carried throughout the equivalence closure. -/
theorem originalFiniteSidePointChain_rawCorner
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    {x y:P.domain.carrier} (hxy:Relation.EqvGen (fuchsianSidePointStep hD) x y)
    (i:ZMod J.n) (hi:originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (P.finiteCoordinate x)) :
    ∃j:ZMod J.n,Relation.EqvGen (originalRawCornerStep J e) i j∧
      originalCyclicVertex hD J hv j=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate y) := by
  have hlift : ∀{a b:P.domain.carrier},Relation.EqvGen (fuchsianSidePointStep hD) a b→
      (∀i,originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (P.finiteCoordinate a)→
        ∃j,Relation.EqvGen (originalRawCornerStep J e) i j∧
          originalCyclicVertex hD J hv j=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate b)) ∧
      (∀j,originalCyclicVertex hD J hv j=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (P.finiteCoordinate b)→
        ∃i,Relation.EqvGen (originalRawCornerStep J e) j i∧
          originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate a)) := by
    intro a b h
    induction h with
    | rel a b h =>
      constructor
      · intro i hi
        obtain ⟨j,hij,hj⟩:=originalFiniteSidePointStep_rawCorner hD ha J hc hv e hs h i hi
        exact ⟨j,Relation.EqvGen.rel _ _ hij,hj⟩
      · intro j hj
        obtain ⟨i,hji,hi⟩:=originalFiniteSidePointStep_rawCorner hD ha J hc hv e hs
          (originalFiniteSidePointStep_symm hD h) j hj
        exact ⟨i,Relation.EqvGen.rel _ _ hji,hi⟩
    | refl a =>
      constructor <;> intro i hi <;> exact ⟨i,Relation.EqvGen.refl _,hi⟩
    | symm a b _ ih => exact ⟨ih.2,ih.1⟩
    | trans a b c _ _ ih1 ih2 =>
      constructor
      · intro i hi
        obtain ⟨j,hij,hj⟩:=ih1.1 i hi
        obtain ⟨k,hjk,hk⟩:=ih2.1 j hj
        exact ⟨k,Relation.EqvGen.trans _ _ _ hij hjk,hk⟩
      · intro k hk
        obtain ⟨j,hkj,hj⟩:=ih2.2 k hk
        obtain ⟨i,hji,hi⟩:=ih1.2 j hj
        exact ⟨i,Relation.EqvGen.trans _ _ _ hkj hji,hi⟩
  exact (hlift hxy).1 i hi

/-- Every genuine raw corner chain is an actual original whole-group sphere orbit identification. -/
theorem originalRawCornerChain_sphereOrbit
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    {i j:ZMod J.n} (hij:Relation.EqvGen (originalRawCornerStep J e) i j) :
    ∃g:H,g.val.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (originalCyclicVertex hD J hv
      i))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (originalCyclicVertex hD J hv j) := by
  induction hij with
  | rel i j h =>
    obtain ⟨k,h|h⟩:=h
    · refine ⟨(fuchsianSideElement hD (e k).val.1)⁻¹,?_⟩
      rw [h.1,h.2]
      exact (P.compactifiedAction_sphere _ _).symm.trans
        (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended
          (originalCyclicPairIndex_endpoint_reverse hD ha J hc hv e hs k).1)
    · refine ⟨(fuchsianSideElement hD (e k).val.1)⁻¹,?_⟩
      rw [h.1,h.2]
      exact (P.compactifiedAction_sphere _ _).symm.trans
        (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended
          (originalCyclicPairIndex_endpoint_reverse hD ha J hc hv e hs k).2)
  | refl i => exact ⟨1,rfl⟩
  | symm i j _ ih =>
    obtain ⟨g,hg⟩:=ih
    refine ⟨g⁻¹,?_⟩
    change g.val.val.symm _=_
    rw [←hg,g.val.val.symm_apply_apply]
  | trans i j k _ _ ih1 ih2 =>
    obtain ⟨g,hg⟩:=ih1
    obtain ⟨h,hh⟩:=ih2
    refine ⟨h*g,?_⟩
    change h.val.val (g.val.val _)=_
    rw [hg,hh]

/-- The actual original finite point has exactly its original sphere coordinate after model inclusion. -/
theorem originalFinitePoint_closedModel_sphere
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup
      H) (x:P.domain.carrier) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x))=x.val :=
  P.finiteCoordinate_extended x

/-- Every genuine finite marked original corner lies in the original polygon closure, including actual self-pairing centers. -/
theorem originalFiniteMarkedCorner_mem_closure
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (i:ZMod J.n) (x:P.domain.carrier)
    (hi:originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)) : x∈closure D := by
  have hxv:originalCyclicVertex hD J hv i∈(e i).carrier:=
    (originalCyclicVertex_mem_side_iff hD J hv e hs i i).mpr (Or.inl rfl)
  have hxs:= (e i).carrier_subset_original hxv
  rw [hi] at hxs
  have hx: x∈(e i).val.1.val:=(mem_fuchsianSideClosedModel_finite _ x).mp hxs
  obtain ⟨g,_hg,he⟩:=(e i).val.1.property.1
  exact (he ▸ hx).1

/-- For two actual finite marked corners, literal raw corner equivalence is precisely the genuine original whole-group orbit relation, without a supplied orbit or sideword correspondence. -/
theorem originalFiniteCorner_orbit_iff_rawCornerChain
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (i j:ZMod J.n) (x y:P.domain.carrier)
    (hi:originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (P.finiteCoordinate x))
    (hj:originalCyclicVertex hD J hv j=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (P.finiteCoordinate y)) :
    Relation.EqvGen (originalRawCornerStep J e) i j↔∃g:H,g•x=y := by
  constructor
  · intro h
    obtain ⟨g,hg⟩:=originalRawCornerChain_sphereOrbit hD ha J hc hv e hs h
    refine ⟨g,?_⟩
    apply Subtype.ext
    change g.val.val x.val=y.val
    rw [hi,hj,originalFinitePoint_closedModel_sphere,originalFinitePoint_closedModel_sphere] at hg
    exact hg
  · rintro ⟨g,hg⟩
    have hx:=originalFiniteMarkedCorner_mem_closure hD J hv e hs i x hi
    have hy:=originalFiniteMarkedCorner_mem_closure hD J hv e hs j y hj
    obtain ⟨k,hik,hk⟩:=originalFiniteSidePointChain_rawCorner hD ha J hc hv e hs
      (hD.side_point_chain_of_orbit x y hx hy g hg) i hi
    have hkj:k=j:=originalCyclicVertex_injective hD J hv (hk.trans hj.symm)
    exact hkj ▸ hik
end LowDimensionalTopology.Geometry.Fuchsian
