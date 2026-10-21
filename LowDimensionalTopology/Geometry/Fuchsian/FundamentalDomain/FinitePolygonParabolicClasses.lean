module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.ParabolicPolygonVertices
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.FinitePolygonEllipticClasses
/-!
# Finitely many parabolic classes from finitely many sides

Each side has finitely many ideal endpoints, so a finite side set has
finitely many proper infinite vertices. These vertices meet every parabolic
orbit and give finitely many maximal parabolic cyclic classes.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped OnePoint Topology Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance finiteParabSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance finiteParabSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- Every actual side has only finitely many genuine ideal endpoints. -/
theorem fuchsian_side_idealEndpoints_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D S : Set P.domain.carrier}
    (hS : IsFuchsianPolygonSide P D S) : {u : Circle | IsFuchsianSideIdealEndpoint P S u}.Finite := by
  obtain ⟨L,hL⟩ := hS.2.1.2
  obtain ⟨a,b,_hab,_ha,_hb,he⟩ := L.exists_idealEndpoints_pair
  have hF : L.idealEndpoints.Finite := by rw [he]; exact (finite_singleton b).insert a
  have hi : Function.Injective (fun u : Circle => ((u : ℂ) : OnePoint ℂ)) :=
    OnePoint.coe_injective.comp Subtype.val_injective
  apply (hF.preimage hi.injOn).subset
  intro u hu
  refine ⟨?_,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedDiscIdealBoundary (u : ℂ)).mpr
    (Circle.norm_coe u)⟩
  have hc := mem_closure_image OnePoint.continuous_coe.continuousAt hu
  apply closure_mono ?_ hc
  rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
  exact ⟨P.finiteCoordinate x,hL ⟨x,hx,rfl⟩,rfl⟩

/-- A finite genuine side set has only finitely many genuine proper infinite vertices. -/
theorem finite_sided_polygon_proper_infinite_vertices_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hFin : Finite (FuchsianPolygonSides P D)) :
    {u : Circle | IsProperFuchsianInfiniteVertex P D u}.Finite := by
  have : Finite (FuchsianPolygonSides P D) := hFin
  apply (Set.finite_iUnion (fun s : FuchsianPolygonSides P D =>
    fuchsian_side_idealEndpoints_finite s.property)).subset
  rintro u ⟨_hu,S,T,hS,_hT,_hST,huS,_huT⟩
  exact mem_iUnion.mpr ⟨⟨S,hS⟩,huS⟩

/-- Finite actual sides imply finitely many actual maximal parabolic cyclic subgroup
conjugacy classes; every true parabolic orbit is represented at a proper infinite vertex. -/
theorem finite_sided_polygon_parabolic_classes_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (hFin : Finite (FuchsianPolygonSides P D)) :
    Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) := by
  let X := fuchsianCyclicFixedPoints P.asFuchsianDisc .parabolic
  let V := {u : Circle | IsProperFuchsianInfiniteVertex P D u}
  let S : Set X := {p | p.val ∈ (fun u : Circle => ((u : ℂ) : OnePoint ℂ)) '' V}
  have hV : V.Finite := finite_sided_polygon_proper_infinite_vertices_finite hFin
  have hS : S.Finite := (hV.image (fun u : Circle => ((u : ℂ) : OnePoint ℂ))).preimage
    Subtype.val_injective.injOn
  have hrep (p : X) : ∃ g : H, g • p ∈ S := by
    obtain ⟨f,hfH,hf,hfix⟩ := p.property.2
    let F : H := ⟨f,hfH⟩
    obtain ⟨g,η,hgη,hη⟩ := hD.locallyFinite.parabolic_fixedPoint_orbit_mem_idealBoundary F hf p.val hfix
    let u : Circle := ⟨η,mem_sphere_zero_iff_norm.mpr ((mem_fuchsianPolygonIdealBoundary P D η).mp hη).2⟩
    have huCycle : ((u : ℂ) : OnePoint ℂ) ∈ fuchsianPolygonIdealCycle P D p.val :=
      ⟨⟨η,hη,rfl⟩,MulAction.mem_orbit_iff.mpr ⟨g,hgη⟩⟩
    have hu : u ∈ V := hD.parabolic_idealCycle_proper F hf p.val hfix u huCycle
    refine ⟨g,u,hu,?_⟩
    exact hgη.symm
  have : Finite (MulAction.orbitRel.Quotient H X) :=
    finite_orbitQuotient_of_finite_representatives S hS hrep
  exact Finite.of_equiv _ (fuchsianCyclicConjugacyClassesEquiv P.asFuchsianDisc .parabolic).symm

/-- The genuine finite-sided implication for both original elliptic and parabolic class types. -/
theorem finite_sided_polygon_elliptic_parabolic_classes_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (hFin : Finite (FuchsianPolygonSides P D))
    (kind : FuchsianCyclicKind) : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc kind) := by
  cases kind with
  | elliptic => exact finite_sided_polygon_elliptic_classes_finite hD hFin
  | parabolic => exact finite_sided_polygon_parabolic_classes_finite hD hFin

end LowDimensionalTopology.Geometry.Fuchsian
