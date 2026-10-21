/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonAccidentalCycles
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane MatrixGroups OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The original Cayley-disc distance is exactly the native path metric. -/
theorem HalfPlaneFuchsianGroup.cayleyCoordinate_hyperbolicDist
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H) (x y
      : ℍ) :
    P.cayleyData.hyperbolicDist (P.cayleyCoordinate x) (P.cayleyCoordinate y)=dist x y := by
  rw [P.cayleyData.hyperbolicDist_eq_discPathDist,P.cayleyCoordinate_finite,
    P.cayleyCoordinate_finite,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]

/-- Freeness of a genuine native point transfers to the original conjugate group. -/
theorem HalfPlaneFuchsianGroup.cayleyCoordinate_free
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H) (w :
      ℍ) :
    letI := P.nativeAction
    (∀g : H,g • w=w→g=1) → IsDirichletCenter P.cayleyData (P.cayleyCoordinate w) := by
  let nativeNearestAction := P.nativeAction
  intro hw g hg
  let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H
  apply e.symm.injective
  rw [map_one]
  apply hw
  apply P.cayleyCoordinate.injective
  rw [P.cayleyCoordinate_equivariant,e.apply_symm_apply]
  exact hg

/-- A native original orbit is identified with the literal Cayley-conjugate orbit. -/
theorem HalfPlaneFuchsianGroup.cayleyCoordinate_mem_orbit
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H) (z u
      : ℍ) :
    letI := P.nativeAction
    P.cayleyCoordinate u∈MulAction.orbit (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H)
      (P.cayleyCoordinate z) ↔ u∈MulAction.orbit H z := by
  let nativeNearestAction := P.nativeAction
  let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H
  constructor
  · intro hu
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp hu
    refine MulAction.mem_orbit_iff.mpr ⟨e.symm g,?_⟩
    apply P.cayleyCoordinate.injective
    rw [P.cayleyCoordinate_equivariant,e.apply_symm_apply]
    exact hg
  · intro hu
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp hu
    exact MulAction.mem_orbit_iff.mpr ⟨e g,(P.cayleyCoordinate_equivariant g z).symm.trans
      (congrArg P.cayleyCoordinate hg)⟩

/-- Closure of the actual Dirichlet polygon is precisely a nearest-orbit condition. -/
theorem dirichlet_closure_iff_orbit_nearest {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (z : P.domain.carrier) :
    z∈closure (dirichletDomain P w) ↔
      ∀g : H,P.hyperbolicDist z w≤P.hyperbolicDist (g • z) w := by
  rw [closure_dirichletDomain P w hw]
  constructor
  · intro h g
    have hi:=h g⁻¹
    rwa [P.hyperbolicDist_inverse_smul,inv_inv] at hi
  · intro h g
    simpa only [P.hyperbolicDist_inverse_smul] using h g⁻¹

/-- The literal closed-domain cycle is exactly the nearest part of the genuine orbit. -/
theorem dirichlet_cycle_eq_nearest_orbit {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (z : P.domain.carrier) (hz : z∈closure (dirichletDomain P w)) :
    fuchsianPolygonCycle P (dirichletDomain P w) z=
      {u | u∈MulAction.orbit H z ∧ P.hyperbolicDist u w=P.hyperbolicDist z w} := by
  ext u
  constructor
  · rintro ⟨hu,ho⟩
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp ho
    refine ⟨MulAction.mem_orbit_iff.mpr ⟨g,hg⟩,?_⟩
    rw [←hg]
    exact (dirichlet_closed_orbit_equal_distance P w z g hz (hg ▸ hu)).symm
  · rintro ⟨ho,hr⟩
    refine ⟨?_,ho⟩
    apply (dirichlet_closure_iff_orbit_nearest P w hw u).mpr
    intro g
    obtain ⟨h,hh⟩:=MulAction.mem_orbit_iff.mp ho
    rw [hr,←hh,←mul_smul]
    exact (dirichlet_closure_iff_orbit_nearest P w hw z).mp hz (g*h)

/-- Three distinct actual closed-cycle points force a genuine polygon vertex. -/
theorem IsConvexFuchsianPolygon.vertex_of_three_cycle_points
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (z u v : P.domain.carrier) (hz : z∈closure D)
    (hu : u∈fuchsianPolygonCycle P D z) (hv : v∈fuchsianPolygonCycle P D z)
    (huz : u≠z) (hvz : v≠z) (huv : u≠v) : IsFuchsianPolygonVertex P D z := by
  obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp hu.2
  obtain ⟨h,hh⟩:=MulAction.mem_orbit_iff.mp hv.2
  have hg1:g≠1:=by intro he;apply huz;rw [←hg,he,one_smul]
  have hh1:h≠1:=by intro he;apply hvz;rw [←hh,he,one_smul]
  have hgh:g≠h:=by intro he;apply huv;rw [←hg,←hh,he]
  have hzg:z∈fuchsianDomainTile P D g⁻¹:=⟨u,hu.1,by change g⁻¹ • u=z;rw [←hg,inv_smul_smul]⟩
  have hzh:z∈fuchsianDomainTile P D h⁻¹:=⟨v,hv.1,by change h⁻¹ • v=z;rw [←hh,inv_smul_smul]⟩
  exact ⟨g⁻¹,h⁻¹,inv_ne_one.mpr hg1,inv_ne_one.mpr hh1,
    fun he=>hgh (inv_injective he),
    (hD.closed_tile_triple_subsingleton (inv_ne_one.mpr hg1) (inv_ne_one.mpr hh1)
      (fun he=>hgh (inv_injective he))).eq_singleton_of_mem ⟨⟨hz,hzg⟩,hzh⟩⟩


/-- Native and sphere orbits are the same actual orbit on finite upper-half-plane points. -/
theorem HalfPlaneFuchsianGroup.native_orbit_iff_sphere
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H) (z u
      : ℍ) :
    letI := P.nativeAction
    u∈MulAction.orbit H z ↔ _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint u∈MulAction.orbit H (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z) := by
  let nativeNearestAction := P.nativeAction
  constructor
  · intro hu
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp hu
    exact MulAction.mem_orbit_iff.mpr ⟨g,(P.nativeAction_boundary g z).trans
      (congrArg _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint hg)⟩
  · intro hu
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp hu
    refine MulAction.mem_orbit_iff.mpr ⟨g,?_⟩
    exact _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective ((P.nativeAction_boundary g
      z).symm.trans hg)

/-- The whole genuine nearest native orbit maps onto the literal original Dirichlet cycle. -/
theorem HalfPlaneFuchsianGroup.cayley_nearest_cycle_image
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H) (w z
      : ℍ) :
    letI := P.nativeAction
    (∀g : H,g • w=w→g=1) →
    (∀g : H,dist z w≤dist (g • z) w) →
    P.cayleyCoordinate '' {u | u∈MulAction.orbit H z ∧ dist u w=dist z w}=
      fuchsianPolygonCycle P.cayleyData (dirichletDomain P.cayleyData (P.cayleyCoordinate w))
        (P.cayleyCoordinate z) := by
  let nativeNearestAction := P.nativeAction
  intro hw hmin
  have hw':=P.cayleyCoordinate_free w hw
  have hz:P.cayleyCoordinate z∈closure (dirichletDomain P.cayleyData (P.cayleyCoordinate w)):=by
    apply (dirichlet_closure_iff_orbit_nearest P.cayleyData _ hw' _).mpr
    intro g
    let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H
    have he:=P.cayleyCoordinate_equivariant (e.symm g) z
    rw [e.apply_symm_apply] at he
    rw [←he,P.cayleyCoordinate_hyperbolicDist,P.cayleyCoordinate_hyperbolicDist]
    exact hmin (e.symm g)
  rw [dirichlet_cycle_eq_nearest_orbit P.cayleyData _ hw' _ hz]
  ext x
  constructor
  · rintro ⟨u,⟨hu,hr⟩,rfl⟩
    exact ⟨(P.cayleyCoordinate_mem_orbit z u).mpr hu,by
      simpa only [P.cayleyCoordinate_hyperbolicDist] using hr⟩
  · rintro ⟨hx,hr⟩
    refine ⟨P.cayleyCoordinate.symm x,⟨?_,?_⟩,P.cayleyCoordinate.apply_symm_apply x⟩
    · apply (P.cayleyCoordinate_mem_orbit z _).mp
      simpa only [P.cayleyCoordinate.apply_symm_apply] using hx
    · simpa only [←P.cayleyCoordinate_hyperbolicDist,
        P.cayleyCoordinate.apply_symm_apply] using hr

/-- An actual three-point nearest orbit produces a genuine original polygon vertex and cycle of length three. -/
theorem HalfPlaneFuchsianGroup.cayley_three_cycle
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H) (w z
      : ℍ) :
    letI := P.nativeAction
    (∀g : H,g • w=w→g=1) →
    (∀g : H,dist z w≤dist (g • z) w) →
    ∀p : Fin 3→ℍ,Function.Injective p→p 0=z→
      {u | u∈MulAction.orbit H z ∧ dist u w=dist z w}=Set.range p →
      IsDirichletCenter P.cayleyData (P.cayleyCoordinate w) ∧
      IsConvexFuchsianPolygon P.cayleyData (dirichletDomain P.cayleyData (P.cayleyCoordinate w)) ∧
      IsFuchsianPolygonVertex P.cayleyData (dirichletDomain P.cayleyData (P.cayleyCoordinate w))
        (P.cayleyCoordinate z) ∧
      fuchsianPolygonCycleLength P.cayleyData
        (fuchsianPolygonCycle P.cayleyData (dirichletDomain P.cayleyData (P.cayleyCoordinate w))
          (P.cayleyCoordinate z))=3 := by
  let nativeNearestAction := P.nativeAction
  intro hw hmin p hp hp0 hrange
  have hw':=P.cayleyCoordinate_free w hw
  have hD:=dirichletDomain_isConvexFuchsianPolygon P.cayleyData (P.cayleyCoordinate w) hw'
  let f:Fin 3→P.cayleyData.domain.carrier:=P.cayleyCoordinate ∘ p
  have hf:Function.Injective f:=P.cayleyCoordinate.injective.comp hp
  have hf0:f 0=P.cayleyCoordinate z:=congrArg P.cayleyCoordinate hp0
  have hc:fuchsianPolygonCycle P.cayleyData
      (dirichletDomain P.cayleyData (P.cayleyCoordinate w)) (P.cayleyCoordinate z)=range f:=by
    rw [←P.cayley_nearest_cycle_image w z hw hmin,hrange,←range_comp]
  have hmem (i:Fin 3):f i∈fuchsianPolygonCycle P.cayleyData
      (dirichletDomain P.cayleyData (P.cayleyCoordinate w)) (P.cayleyCoordinate z):=by
    rw [hc];exact mem_range_self i
  have hz:P.cayleyCoordinate z∈closure (dirichletDomain P.cayleyData (P.cayleyCoordinate w)):=by
    have h:=(hmem 0).1
    rwa [hf0] at h
  refine ⟨hw',hD,?_,?_⟩
  · apply hD.vertex_of_three_cycle_points _ (f 1) (f 2) hz (hmem 1) (hmem 2)
    · rw [←hf0];exact hf.ne (by decide)
    · rw [←hf0];exact hf.ne (by decide)
    · exact hf.ne (by decide)
  · change (fuchsianPolygonCycle _ _ _).ncard=3
    rw [hc,Set.ncard_range_of_injective hf]
    simp

end LowDimensionalTopology.Geometry.Fuchsian
