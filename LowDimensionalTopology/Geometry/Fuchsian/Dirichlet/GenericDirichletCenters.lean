/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletGeometry
@[expose] public section
open Set Filter MeasureTheory
open scoped Topology OnePoint Pointwise UpperHalfPlane Complex.UnitDisc RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
noncomputable section
local instance genericSphereMeasurableSpace : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance genericSphereBorelSpace : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

def fuchsianEllipticPoints {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H) : Set P.domain.carrier :=
  {x | ¬IsDirichletCenter P x}

theorem fuchsianEllipticPoints_iff {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (x : P.domain.carrier) : x∈fuchsianEllipticPoints P ↔ x.val∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFixedPointSet H := by
  change ¬IsDirichletCenter P x ↔ _
  rw [isDirichletCenter_iff_not_ellipticFixed,not_not]

theorem fuchsianEllipticPoints_countable {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) :
    (fuchsianEllipticPoints P).Countable := by
  classical
  let : Countable H:=P.countable
  have hcount (g : {g : H // g≠1}) : {x : P.domain.carrier | g.val • x=x}.Countable:=by
    have hg : g.val.val≠1:=by
      intro he
      exact g.property (Subtype.val_injective he)
    have hc : {x : P.domain.carrier | g.val.val.val x.val=x.val}.Countable:=
      (mobius_boundary_fixed_finite g.val.val hg).countable.preimage Subtype.val_injective
    apply hc.mono
    intro x hx
    exact congrArg Subtype.val hx
  apply (Set.countable_iUnion hcount).mono
  intro x hx
  change ¬(∀g : H,g • x=x→g=1) at hx
  push Not at hx
  obtain ⟨g,hfix,hg⟩:=hx
  exact mem_iUnion.mpr ⟨⟨g,hg⟩,hfix⟩

theorem fuchsianEllipticPoints_area_zero {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) :
    P.area (fuchsianEllipticPoints P)=0 := (fuchsianEllipticPoints_countable P).measure_zero _

theorem fuchsianEllipticPoints_smul {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    {x : P.domain.carrier} (hx : x∈fuchsianEllipticPoints P) (g : H) : g • x∈fuchsianEllipticPoints P := by
  change ¬IsDirichletCenter P (g • x)
  intro hc
  apply hx
  intro h hh
  have hconj : (g*h*g⁻¹) • (g • x)=g • x:=by simp only [mul_smul,inv_smul_smul,hh]
  have he:=hc (g*h*g⁻¹) hconj
  have hv:=congrArg (fun a : H=>g⁻¹*a*g) he
  simpa [mul_assoc] using hv

theorem UnitDiscFuchsianGroup.equidistant_area_zero {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (a b : P.domain.carrier) (hab : a≠b) :
    P.area {w | P.hyperbolicDist w a=P.hyperbolicDist w b}=0 := by
  have hset : IsClosed {w | P.hyperbolicDist w a=P.hyperbolicDist w b}:=
    isClosed_eq (P.hyperbolicDist_left_continuous a) (P.hyperbolicDist_left_continuous b)
  rw [P.area_eq_halfPlane_volume _ hset.measurableSet]
  obtain ⟨L,hL⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_hEquidistantLine (fun h=>hab
    (P.halfPlaneCoordinate.injective h))
  have him : P.halfPlaneCoordinate '' {w | P.hyperbolicDist w a=P.hyperbolicDist w b}=L.carrier:=by
    rw [hL]
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact hw
    · intro hz
      change dist z (P.halfPlaneCoordinate a)=dist z (P.halfPlaneCoordinate b) at hz
      refine ⟨P.halfPlaneCoordinate.symm z,?_,P.halfPlaneCoordinate.apply_symm_apply z⟩
      change dist (P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm z)) (P.halfPlaneCoordinate a)=
        dist (P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm z)) (P.halfPlaneCoordinate b)
      simpa only [P.halfPlaneCoordinate.apply_symm_apply] using hz
  rw [him]
  exact L.volume_zero

def dirichletEllipticBadCenters {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H) : Set P.domain.carrier :=
  ⋃a : fuchsianEllipticPoints P,⋃b : {b : fuchsianEllipticPoints P // b.val≠a.val},
    {w | P.hyperbolicDist w a.val=P.hyperbolicDist w b.val.val}

theorem dirichletEllipticBadCenters_area_zero {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) :
    P.area (dirichletEllipticBadCenters P)=0 := by
  let : Countable (fuchsianEllipticPoints P):=(fuchsianEllipticPoints_countable P).to_subtype
  exact measure_iUnion_null (fun a=>measure_iUnion_null (fun b=>P.equidistant_area_zero a.val b.val.val
    b.property.symm))

theorem dirichlet_elliptic_cycle_subsingleton {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : w∉dirichletEllipticBadCenters P)
    (x : P.domain.carrier) (hx : x∈fuchsianEllipticPoints P) :
    (fuchsianPolygonCycle P (dirichletDomain P w) x).Subsingleton := by
  intro y hy z hz
  by_contra hne
  obtain ⟨g,rfl⟩:=MulAction.mem_orbit_iff.mp hy.2
  obtain ⟨h,rfl⟩:=MulAction.mem_orbit_iff.mp hz.2
  apply hw
  refine mem_iUnion.mpr ⟨⟨g • x,fuchsianEllipticPoints_smul P hx g⟩,
    mem_iUnion.mpr ⟨⟨⟨h • x,fuchsianEllipticPoints_smul P hx h⟩,Ne.symm hne⟩,?_⟩⟩
  change P.hyperbolicDist w (g • x)=P.hyperbolicDist w (h • x)
  have he:=dirichlet_cycle_distance_to_center_eq P w x hy hz
  simpa only [P.hyperbolicDist_comm] using he

theorem dirichlet_elliptic_cycle_length_one {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (hwB : w∉dirichletEllipticBadCenters P) (x : P.domain.carrier) (hx : x∈fuchsianEllipticPoints P) :
    fuchsianPolygonCycleLength P (fuchsianPolygonCycle P (dirichletDomain P w) x)=1 := by
  obtain ⟨a,ha⟩:=(dirichletDomain_fundamental P w hw).cycle_nonempty x
  apply Set.ncard_eq_one.mpr
  refine ⟨a,Set.Subset.antisymm (fun _ hz=>(dirichlet_elliptic_cycle_subsingleton P w hwB x hx hz ha) ▸ mem_singleton a)
    (singleton_subset_iff.mpr ha)⟩

/-- The elliptic-cycle clause holds for almost every genuine center. -/
theorem ae_dirichlet_elliptic_cycleLength_eq_one {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) :
    ∀ᵐ w ∂P.area,IsDirichletCenter P w ∧ ∀x∈fuchsianEllipticPoints P,
      fuchsianPolygonCycleLength P (fuchsianPolygonCycle P (dirichletDomain P w) x)=1 := by
  have hzero : P.area (fuchsianEllipticPoints P∪dirichletEllipticBadCenters P)=0:=
    measure_union_null (fuchsianEllipticPoints_area_zero P) (dirichletEllipticBadCenters_area_zero P)
  rw [ae_iff]
  apply measure_mono_null _ hzero
  intro w hw
  by_contra hn
  have hc : IsDirichletCenter P w:=by
    by_contra hc
    exact hn (Or.inl hc)
  have hb : w∉dirichletEllipticBadCenters P:=fun hb=>hn (Or.inr hb)
  exact hw ⟨hc,fun x hx=>dirichlet_elliptic_cycle_length_one P w hc hb x hx⟩

end
end LowDimensionalTopology.Geometry.Fuchsian
