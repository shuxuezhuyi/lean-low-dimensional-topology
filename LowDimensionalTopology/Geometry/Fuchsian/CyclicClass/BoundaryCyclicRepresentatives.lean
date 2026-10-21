module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.ParabolicFundamentalBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.FinitePolygonEllipticClasses
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology Pointwise OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance boundaryRepSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance boundaryRepSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- The original boundary representatives are genuine fixed points of the indicated actual types. -/
def fuchsianCyclicBoundaryPoints {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set
      P.domain.carrier) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  frontier ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D) ∩
    {p | ∃ f : H, (_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f.val ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val) ∧ f.val.val p = p}

/-- The actual boundary fixed-point set is countable, as in the geometric indexed family. -/
theorem fuchsianCyclicBoundaryPoints_countable {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) :
    (fuchsianCyclicBoundaryPoints P D).Countable := by
  have : Countable H := P.countable
  have hU : (⋃ f : {f : H // f ≠ 1},Function.fixedPoints f.val.val.val).Countable := by
    apply countable_iUnion
    intro f
    exact (mobius_boundary_fixed_finite f.val.val
      (fun he => f.property (Subtype.ext he))).countable
  apply hU.mono
  rintro p ⟨_hfront,f,hf,hfix⟩
  have hfn : f ≠ 1 := by
    intro he
    have hv : f.val = 1 := congrArg Subtype.val he
    rcases hf with hf | hf <;> exact hf.1 hv
  exact mem_iUnion.mpr ⟨⟨f,hfn⟩,hfix⟩

/-- A literal Euclidean ideal-boundary point lies on the actual ambient polygon frontier. -/
theorem fuchsian_idealBoundary_mem_ambientFrontier {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (η : ℂ)
    (hη : η ∈ fuchsianPolygonIdealBoundary P D) :
    (η : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ frontier ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D) := by
  obtain ⟨hn,hcl⟩ := (mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D η).mp hη
  refine ⟨hcl,?_⟩
  intro hint
  obtain ⟨x,_hx,hxη⟩ := interior_subset hint
  have he : (P.finiteCoordinate x : ℂ) = η :=
    OnePoint.coe_injective ((P.finiteCoordinate_extended x).trans hxη)
  have hh := (P.finiteCoordinate x).norm_lt_one
  rw [he,hn] at hh
  exact lt_irrefl 1 hh

/-- The genuine internal point stabilizer is cyclic, including ideal boundary points. -/
theorem fuchsian_internal_stabilizer_isCyclic {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : IsCyclic (MulAction.stabilizer H p) := by
  have : IsCyclic (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H
    p) := P.asFuchsianDisc.stabilizer_isCyclic p
  let e : MulAction.stabilizer H p ≃* _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p :=
    (MulAction.stabilizer H p).equivMapOfInjective H.subtype Subtype.val_injective
  exact isCyclic_of_injective e.toMonoidHom e.injective

/-- Every original actual point stabilizer has a genuine generator in the original subgroup. -/
theorem fuchsian_exists_internal_stabilizer_generator {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    ∃ g : H, Subgroup.zpowers g = MulAction.stabilizer H p := by
  have : IsCyclic (MulAction.stabilizer H p) := fuchsian_internal_stabilizer_isCyclic P p
  obtain ⟨a,ha⟩ := exists_zpow_surjective (MulAction.stabilizer H p)
  refine ⟨a.val,?_⟩
  ext g
  constructor
  · intro hg
    obtain ⟨n,rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (a^n).property
  · intro hg
    obtain ⟨n,hn⟩ := ha ⟨g,hg⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨n,congrArg Subtype.val hn⟩

/-- Every actual elliptic member has an actual conjugate fixing the genuine fundamental-domain boundary. -/
theorem elliptic_conjugate_boundary_fixed {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      f.val) :
    ∃ (h : H) (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),
      p ∈ frontier ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
        D) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (h*f*h⁻¹).val ∧ (h*f*h⁻¹).val.val p = p := by
  obtain ⟨x,hfx,_hunique⟩ := elliptic_disc_existsUnique_fixed f.val hf
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc (P.image_eq f)
  have hx : x ∈ (⋃ g : H,(fun y : P.domain.carrier => g • y) '' closure D) := by
    rw [hD.fundamental.closure_cover]
    trivial
  obtain ⟨g,y,hy,hgy⟩ := mem_iUnion.mp hx
  change g • y = x at hgy
  let h := g⁻¹
  let F : H := h*f*h⁻¹
  have hFE : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic F.val :=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_isConj (isConj_iff.mpr ⟨h.val,rfl⟩)).mp hf
  have hFy : F • y = y := by
    change g⁻¹ • (f • (g • y)) = y
    have hfxH : f • (g • y) = g • y := by
      apply Subtype.ext
      change f.val.val (g • y).val = (g • y).val
      rw [hgy]
      exact hfx
    rw [hfxH,inv_smul_smul]
  have hFn : F ≠ 1 := fun he => hFE.1 (congrArg Subtype.val he)
  have hyfront := polygon_fixed_point_mem_frontier hD.fundamental y hy F hFn hFy
  have hycl : y.val ∈ closure ((Subtype.val : P.domain.carrier →
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D) :=
    image_closure_subset_closure_image continuous_subtype_val ⟨y,hy,rfl⟩
  have hynot : y.val ∉ interior ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D) := by
    intro hint
    obtain ⟨z,hz,hzy⟩ := interior_subset hint
    have he : z = y := Subtype.ext hzy
    have hh := hyfront.2
    rw [hD.fundamental.isOpen.interior_eq] at hh
    exact hh (he ▸ hz)
  exact ⟨h,y.val,⟨hycl,hynot⟩,hFE,congrArg Subtype.val hFy⟩

/-- The full original representative claim for both elliptic and parabolic members. -/
theorem elliptic_or_parabolic_conjugate_boundary_fixed {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (f : H)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f.val ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val) :
    ∃ (h : H) (p : fuchsianCyclicBoundaryPoints P D), (h*f*h⁻¹).val.val p.val = p.val := by
  rcases hf with he | hp
  · obtain ⟨h,p,hpfront,hFE,hfix⟩ := elliptic_conjugate_boundary_fixed hD f he
    exact ⟨h,⟨p,hpfront,h*f*h⁻¹,Or.inl hFE,hfix⟩,hfix⟩
  · obtain ⟨h,η,hhη,hη⟩ := hD.parabolic_fixedPoint_orbit_mem_idealBoundary f hp
      hp.2.choose ((hp.2.choose_spec hp.2.choose).mpr rfl)
    let p := (η : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    have hFE : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (h*f*h⁻¹).val :=
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨h.val,rfl⟩)).mp hp
    have hfix : (h*f*h⁻¹).val.val p = p := by
      change (h*f*h⁻¹).val.val (η : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (η :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      rw [←hhη]
      change h.val.val (f.val.val (h.val.val.symm (h.val.val hp.2.choose))) = _
      rw [Equiv.symm_apply_apply,(hp.2.choose_spec hp.2.choose).mpr rfl]
    exact ⟨h,⟨p,fuchsian_idealBoundary_mem_ambientFrontier P D η hη,
      h*f*h⁻¹,Or.inr hFE,hfix⟩,hfix⟩

/-- The stabilizer generators stipulated in exist on the actual boundary-point set. -/
theorem fuchsian_boundary_stabilizer_generators_exist {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) :
    ∃ generators : fuchsianCyclicBoundaryPoints P D → H,
      ∀ p, Subgroup.zpowers (generators p) = MulAction.stabilizer H p.val := by
  classical
  choose g hg using (fun p : fuchsianCyclicBoundaryPoints P D =>
    fuchsian_exists_internal_stabilizer_generator P p.val)
  exact ⟨g,hg⟩

/--
For the original actual convex fundamental polygon,
its genuine boundary points, and any prescribed genuine stabilizer generators.
-/
theorem elliptic_or_parabolic_conjugate_boundary_stabilizer_generator_power {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D)
    (generators : fuchsianCyclicBoundaryPoints P D → H)
    (hgen : ∀ p, Subgroup.zpowers (generators p) = MulAction.stabilizer H p.val)
    (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f.val ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val) :
    ∃ (p : fuchsianCyclicBoundaryPoints P D) (n : ℤ), IsConj f (generators p ^ n) := by
  obtain ⟨h,p,hfix⟩ := elliptic_or_parabolic_conjugate_boundary_fixed hD.locallyFinite f hf
  have hmem : h*f*h⁻¹ ∈ MulAction.stabilizer H p.val := hfix
  rw [←hgen p] at hmem
  obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact ⟨p,n,isConj_iff.mpr ⟨h,hn.symm⟩⟩

end LowDimensionalTopology.Geometry.Fuchsian
