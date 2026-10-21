/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalFiniteCornerChains
/-!
# Raw finite corner cycles

A raw corner class based at a finite marked point consists of finite points.
Its marked indices are in bijection with the original polygon orbit cycle,
so the class size equals the cycle length.
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

/-- Every member of a genuine raw corner class based at a finite marked point is itself a finite point in its literal original polygon cycle. -/
theorem originalRawFiniteCornerClass_point_exists
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
      (P.finiteCoordinate x))
    (j:ZMod J.n) (hij:Relation.EqvGen (originalRawCornerStep J e) i j) :
    ∃y:↥(fuchsianPolygonCycle P D x),originalCyclicVertex hD J hv j=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate y.val) := by
  obtain ⟨g,hg⟩:=originalRawCornerChain_sphereOrbit hD ha J hc hv e hs hij
  have hz:originalCyclicVertex hD J hv j=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate (g•x)):=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_closedDiscToExtended.injective
    rw [originalFinitePoint_closedModel_sphere]
    rw [hi,originalFinitePoint_closedModel_sphere] at hg
    exact hg.symm
  refine ⟨⟨g•x,originalFiniteMarkedCorner_mem_closure hD J hv e hs j (g•x) hz,?_⟩,hz⟩
  exact MulAction.mem_orbit_iff.mpr ⟨g,rfl⟩

/-- The actual finite marked corner indices in one literal raw vertex class are in genuine bijection with every point of the original closed polygon's literal finite orbit cycle. -/
def originalRawFiniteCornerClassEquiv
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
    {j:ZMod J.n // Relation.EqvGen (originalRawCornerStep J e) i j}≃
      ↥(fuchsianPolygonCycle P D x) := by
  let f:{j:ZMod J.n // Relation.EqvGen (originalRawCornerStep J e) i j}→
      ↥(fuchsianPolygonCycle P D x):=fun j=>
    Classical.choose (originalRawFiniteCornerClass_point_exists hD ha J hc hv e hs i x hi j.val j.property)
  have hf (j:{j:ZMod J.n // Relation.EqvGen (originalRawCornerStep J e) i j}) :
      originalCyclicVertex hD J hv j.val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate (f j).val):=
    Classical.choose_spec (originalRawFiniteCornerClass_point_exists hD ha J hc hv e hs i x hi j.val j.property)
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    apply originalCyclicVertex_injective hD J hv
    exact (hf a).trans ((congrArg (fun y:↥(fuchsianPolygonCycle P D x)=>
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate y.val)) hab).trans (hf
        b).symm)
  · intro y
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp y.property.2
    have hx:=originalFiniteMarkedCorner_mem_closure hD J hv e hs i x hi
    obtain ⟨j,hij,hj⟩:=originalFiniteSidePointChain_rawCorner hD ha J hc hv e hs
      (hD.side_point_chain_of_orbit x y.val hx y.property.1 g hg) i hi
    refine ⟨⟨j,hij⟩,?_⟩
    apply Subtype.ext
    apply P.finiteCoordinate.injective
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective
    exact (hf ⟨j,hij⟩).symm.trans hj

theorem originalRawFiniteCornerClassEquiv_spec
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
      (P.finiteCoordinate x))
    (j:{j:ZMod J.n // Relation.EqvGen (originalRawCornerStep J e) i j}) :
    originalCyclicVertex hD J hv j.val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate
      (originalRawFiniteCornerClassEquiv hD ha J hc hv e hs i x hi j).val) :=
  Classical.choose_spec (originalRawFiniteCornerClass_point_exists hD ha J hc hv e hs i x hi j.val j.property)

/-- The actual raw corner-class size is exactly the literal original cycle length. -/
theorem originalRawFiniteCornerClass_card
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
    Nat.card {j:ZMod J.n // Relation.EqvGen (originalRawCornerStep J e) i j}=
      Nat.card ↥(fuchsianPolygonCycle P D x) :=
  Nat.card_congr (originalRawFiniteCornerClassEquiv hD ha J hc hv e hs i x hi)
end LowDimensionalTopology.Geometry.Fuchsian
