/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletIdealWeights
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.ParabolicPolygonVertices
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.GenericDirichletCenters
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology OnePoint UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Actual ideal points fixed by at least one nonidentity element of the original group. -/
def fuchsianIdealFixedPoints {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (_P :
  UnitDiscFuchsianGroup H) : Set ℂ :=
  {ξ | ‖ξ‖=1 ∧ ∃g : H,g≠1 ∧ g.val.val (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)}

/-- Discreteness makes the literal original group countable; each nonidentity map has finitely many fixed points. -/
theorem fuchsianIdealFixedPoints_countable {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : (fuchsianIdealFixedPoints P).Countable := by
  classical
  let : Countable H:=P.countable
  have hc (g : {g : H // g≠1}) : {ξ : ℂ | g.val.val.val (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)}.Countable :=
    (mobius_boundary_fixed_finite g.val.val (fun h=>g.property (Subtype.ext h))).countable.preimage
      OnePoint.coe_injective
  apply (Set.countable_iUnion hc).mono
  rintro ξ ⟨_hξ,g,hg,hfix⟩
  exact mem_iUnion.mpr ⟨⟨g,hg⟩,hfix⟩

/-- A literal nontrivial moved ideal image has at most one finite coordinate. -/
def MovedIdealImage {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (g : H) (ξ : ℂ) :=
  {η : ℂ // ‖η‖=1 ∧ g.val.val (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧ ξ≠η}

instance movedIdealImageSubsingleton {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (g
  : H) (ξ : ℂ) :
    Subsingleton (MovedIdealImage g ξ) := ⟨by
  intro a b
  exact Subtype.ext (OnePoint.coe_injective (a.property.2.1.symm.trans b.property.2.1))⟩

/-- The exceptional centers are indexed by countably many actual fixed ideal points and actual original maps. -/
def dirichletFixedIdealBadCenters {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : Set P.domain.carrier :=
  ⋃ξ : fuchsianIdealFixedPoints P,⋃g : H,⋃η : MovedIdealImage g ξ.val,
    {w | _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate w) ξ.val=
      idealPoissonFactor P g ξ.val η.val*_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate w) η.val}

theorem dirichletFixedIdealBadCenters_area_zero {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : P.area (dirichletFixedIdealBadCenters P)=0 := by
  let : Countable H:=P.countable
  let : Countable (fuchsianIdealFixedPoints P):=(fuchsianIdealFixedPoints_countable P).to_subtype
  exact measure_iUnion_null (fun ξ=>measure_iUnion_null (fun g=>measure_iUnion_null
    (fun η=>P.poisson_equal_area_zero ξ.val η.val ξ.property.1 η.property.1 η.property.2.2
      (idealPoissonFactor P g ξ.val η.val))))

/-- Outside the genuine null exceptional set an actual fixed ideal boundary point has a singleton literal whole-group cycle. -/
theorem dirichlet_fixed_ideal_cycle_singleton {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier)
    (hw : w∉dirichletFixedIdealBadCenters P) (ξ : ℂ) (hfixed : ξ∈fuchsianIdealFixedPoints P)
    (hξ : ξ∈fuchsianPolygonIdealBoundary P (dirichletDomain P w)) :
    fuchsianPolygonIdealCycle P (dirichletDomain P w) (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)={(ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)} := by
  apply Subset.antisymm
  · rintro p ⟨⟨η,hη,rfl⟩,horbit⟩
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp horbit
    by_contra hne
    have hn : ξ≠η := fun he=>hne (by simp [he])
    let v : MovedIdealImage g ξ:=⟨η,((mem_fuchsianPolygonIdealBoundary _ _ _).mp hη).2,hg,hn⟩
    apply hw
    exact mem_iUnion.mpr ⟨⟨ξ,hfixed⟩,mem_iUnion.mpr ⟨g,mem_iUnion.mpr
      ⟨v,dirichlet_ideal_pair_poisson_factor P w g ξ η hξ hη hg⟩⟩⟩
  · intro p hp
    rw [mem_singleton_iff] at hp
    subst p
    exact ⟨mem_image_of_mem _ hξ,MulAction.mem_orbit_self _⟩

/-- For almost every true center every parabolic fixed ideal vertex has actual cycle length one and is proper. -/
theorem ae_dirichlet_parabolic_fixed_boundary_singleton_cycle_and_proper_vertex {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) :
    ∀ᵐw∂P.area,IsDirichletCenter P w ∧ ∀(f : H),_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val→
      ∀ξ : Circle,(ξ:ℂ)∈fuchsianPolygonIdealBoundary P (dirichletDomain P w)→
        f.val.val ((ξ:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((ξ:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→
        fuchsianPolygonIdealCycle P (dirichletDomain P w) ((ξ:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)={((ξ:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)} ∧
          IsProperFuchsianInfiniteVertex P (dirichletDomain P w) ξ := by
  have hae : ∀ᵐw∂P.area,w∉dirichletFixedIdealBadCenters P := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using dirichletFixedIdealBadCenters_area_zero P
  filter_upwards [ae_dirichlet_elliptic_cycleLength_eq_one P,hae] with w hw hbad
  refine ⟨hw.1,?_⟩
  intro f hf ξ hξ hfix
  have hfixed : (ξ:ℂ)∈fuchsianIdealFixedPoints P :=
    ⟨ξ.norm_coe, f,fun he=>hf.1 (congrArg Subtype.val he),hfix⟩
  exact ⟨dirichlet_fixed_ideal_cycle_singleton P w hbad ξ hfixed hξ,
    (dirichletDomain_isConvexFuchsianPolygon P w hw.1).parabolic_ideal_isProper f hf ξ hξ hfix⟩


/-- The original parabolic cycle clause, with no assumption that the initially supplied fixed point is already a domain representative. -/
theorem ae_dirichlet_parabolic_fixed_cycle_singleton_proper_vertex {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) :
    ∀ᵐw∂P.area,IsDirichletCenter P w ∧ ∀(f : H),_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val→
      ∀ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,f.val.val ξ=ξ→∃η : Circle,
        fuchsianPolygonIdealCycle P (dirichletDomain P
          w) ξ={((η:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)} ∧
          IsProperFuchsianInfiniteVertex P (dirichletDomain P w) η := by
  filter_upwards [ae_dirichlet_parabolic_fixed_boundary_singleton_cycle_and_proper_vertex P] with w hw
  refine ⟨hw.1,?_⟩
  intro f hf ξ hfix
  let hD:=dirichletDomain_isConvexFuchsianPolygon P w hw.1
  obtain ⟨g,u,hgu,hu⟩:=hD.locallyFinite.parabolic_fixedPoint_orbit_mem_idealBoundary f hf ξ hfix
  let η : Circle:=⟨u,mem_sphere_zero_iff_norm.mpr ((mem_fuchsianPolygonIdealBoundary _ _ _).mp hu).2⟩
  let F : H:=g*f*g⁻¹
  have hF : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic F.val :=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨g.val,rfl⟩)).mp hf
  have hFfix : F.val.val ((η:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((η:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    change F.val.val (u:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(u:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [←hgu]
    change g.val.val (f.val.val (g.val.val.symm (g.val.val ξ)))=g.val.val ξ
    rw [Equiv.symm_apply_apply,hfix]
  obtain ⟨he,hproper⟩:=hw.2 F hF η hu hFfix
  refine ⟨η,?_,hproper⟩
  have horb : MulAction.orbit H ((η:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=MulAction.orbit H ξ :=
    MulAction.orbit_eq_iff.mpr (MulAction.mem_orbit_iff.mpr ⟨g,hgu⟩)
  change (OnePoint.some '' fuchsianPolygonIdealBoundary P (dirichletDomain P w))∩MulAction.orbit H ξ=_
  rw [←horb]
  exact he

end LowDimensionalTopology.Geometry.Fuchsian
