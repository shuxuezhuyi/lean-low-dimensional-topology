/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.FiniteOrbit
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.FiniteIndexCriteria
@[expose] public section
open Set Filter
open scoped Topology OnePoint
namespace LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

local instance fullTopologyChordalMetric : MetricSpace ExtendedComplex:=complexChordalMetricSpace

/-- The entire real reflection group in actual complex coordinates, including direct and anti maps. -/
def fullMobiusContinuousMap (f : complexGeneralMobiusGroup) : C(ExtendedComplex, ExtendedComplex) :=
  ⟨(f : Equiv.Perm ExtendedComplex), by
    obtain ⟨g,hg,he⟩:=f.property
    rw [←he]
    exact extendedComplexEuclideanHomeomorph.symm.continuous.comp
      (g.continuous.comp extendedComplexEuclideanHomeomorph.continuous)⟩

theorem fullMobiusContinuousMap_injective : Function.Injective fullMobiusContinuousMap := by
  intro f g h
  apply Subtype.ext
  apply Equiv.ext
  intro z
  exact congrArg (fun k : C(ExtendedComplex, ExtendedComplex) => k z) h

/-- The canonical uniform chordal metric on the actual complex Mobius group. -/
@[instance_reducible]
def fullMobiusMetricSpace : MetricSpace complexGeneralMobiusGroup :=
  MetricSpace.induced fullMobiusContinuousMap fullMobiusContinuousMap_injective inferInstance

attribute [instance] fullMobiusMetricSpace

theorem fullMobiusContinuousMap_isometry : Isometry fullMobiusContinuousMap :=
  MetricSpace.isometry_induced fullMobiusContinuousMap fullMobiusContinuousMap_injective

/-- The uniform-convergence topology. -/
@[instance_reducible]
def fullMobiusUniformTopology : TopologicalSpace complexGeneralMobiusGroup := inferInstance

/-- The source's supremum displacement metric. -/
def fullMobiusUniformDist (f g : complexGeneralMobiusGroup) : ℝ := dist f g

theorem fullMobiusUniformDist_eq_iSup (f g : complexGeneralMobiusGroup) :
    fullMobiusUniformDist f g =
      ⨆ z : ExtendedComplex, complexChordalDist ((f : Equiv.Perm ExtendedComplex) z)
        ((g : Equiv.Perm ExtendedComplex) z) :=
  ContinuousMap.dist_eq_iSup

theorem fullMobiusUniformDist_mul_right (f g h : complexGeneralMobiusGroup) :
    fullMobiusUniformDist (f * h) (g * h) = fullMobiusUniformDist f g := by
  apply le_antisymm
  · change dist (fullMobiusContinuousMap (f * h)) (fullMobiusContinuousMap (g * h)) ≤
      dist (fullMobiusContinuousMap f) (fullMobiusContinuousMap g)
    apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro z
    exact ContinuousMap.dist_apply_le_dist (f := fullMobiusContinuousMap f)
      (g := fullMobiusContinuousMap g) ((h : Equiv.Perm ExtendedComplex) z)
  · change dist (fullMobiusContinuousMap f) (fullMobiusContinuousMap g) ≤
      dist (fullMobiusContinuousMap (f * h)) (fullMobiusContinuousMap (g * h))
    apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro z
    have hp := ContinuousMap.dist_apply_le_dist (f := fullMobiusContinuousMap (f * h))
      (g := fullMobiusContinuousMap (g * h)) ((h : Equiv.Perm ExtendedComplex).symm z)
    change dist ((f : Equiv.Perm ExtendedComplex)
      ((h : Equiv.Perm ExtendedComplex) ((h : Equiv.Perm ExtendedComplex).symm z)))
      ((g : Equiv.Perm ExtendedComplex)
        ((h : Equiv.Perm ExtendedComplex) ((h : Equiv.Perm ExtendedComplex).symm z))) ≤ _ at hp
    simpa only [fullMobiusContinuousMap, ContinuousMap.coe_mk, Equiv.apply_symm_apply] using hp

theorem fullMobiusUniformDist_eq_mul_inv (f g : complexGeneralMobiusGroup) :
    fullMobiusUniformDist f g = fullMobiusUniformDist (f * g⁻¹) 1 := by
  simpa only [mul_inv_cancel] using (fullMobiusUniformDist_mul_right f g g⁻¹).symm

theorem fullMobius_tendsto_iff_tendstoUniformly {α : Type*} {p : Filter α}
    (F : α → complexGeneralMobiusGroup) (f : complexGeneralMobiusGroup) :
    Tendsto F p (𝓝 f) ↔
      TendstoUniformly (fun i z => (F i : Equiv.Perm ExtendedComplex) z)
        (fun z => (f : Equiv.Perm ExtendedComplex) z) p := by
  rw [fullMobiusContinuousMap_isometry.isEmbedding.isInducing.tendsto_nhds_iff]
  exact ContinuousMap.tendsto_iff_tendstoUniformly

theorem fullMobius_uniform_continuous_mul :
    Continuous (fun p : complexGeneralMobiusGroup × complexGeneralMobiusGroup => p.1 * p.2) := by
  apply fullMobiusContinuousMap_isometry.comp_continuous_iff.mp
  have h : Continuous (fun p : complexGeneralMobiusGroup × complexGeneralMobiusGroup =>
      (fullMobiusContinuousMap p.2, fullMobiusContinuousMap p.1)) :=
    (fullMobiusContinuousMap_isometry.continuous.comp continuous_snd).prodMk
      (fullMobiusContinuousMap_isometry.continuous.comp continuous_fst)
  exact ContinuousMap.continuous_comp'.comp h

theorem fullMobius_uniform_continuous_inv :
    Continuous (fun f : complexGeneralMobiusGroup => f⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro g
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have hu : UniformContinuous (fun z => (g : Equiv.Perm ExtendedComplex).symm z) :=
    CompactSpace.uniformContinuous_of_continuous (fullMobiusContinuousMap g⁻¹).continuous
  obtain ⟨δ, hδ, hprop⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  refine ⟨δ, hδ, ?_⟩
  intro f hf
  change dist (fullMobiusContinuousMap f⁻¹) (fullMobiusContinuousMap g⁻¹) < ε
  apply ContinuousMap.dist_lt_iff_of_nonempty.mpr
  intro z
  change dist ((f : Equiv.Perm ExtendedComplex).symm z)
    ((g : Equiv.Perm ExtendedComplex).symm z) < ε
  have hpoint : dist ((f : Equiv.Perm ExtendedComplex) ((f : Equiv.Perm ExtendedComplex).symm z))
      ((g : Equiv.Perm ExtendedComplex) ((f : Equiv.Perm ExtendedComplex).symm z)) < δ :=
    (ContinuousMap.dist_apply_le_dist (f := fullMobiusContinuousMap f)
      (g := fullMobiusContinuousMap g) ((f : Equiv.Perm ExtendedComplex).symm z)).trans_lt hf
  have hh := hprop hpoint
  simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, dist_comm] using hh

theorem fullMobius_isTopologicalGroup : IsTopologicalGroup complexGeneralMobiusGroup :=
  { continuous_mul:=fullMobius_uniform_continuous_mul
    continuous_inv:=fullMobius_uniform_continuous_inv }


attribute [instance] fullMobius_isTopologicalGroup

/-- The actual positive-Jacobian subgroup of the full geometric group. -/
def fullMobiusPositiveSubgroup : Subgroup complexGeneralMobiusGroup:=
  complexMobiusGroup.comap complexGeneralMobiusGroup.subtype

def complexMobiusToFull : complexMobiusGroup →* complexGeneralMobiusGroup where
  toFun f:=⟨f.val,f.property.1⟩
  map_one':=rfl
  map_mul' _ _:=rfl

theorem complexMobiusToFull_isometry : Isometry complexMobiusToFull := by
  apply Isometry.of_dist_eq
  intro f g
  rfl

def fullMobiusConjugation : complexGeneralMobiusGroup:=
  ⟨complexConjugation,fractionalOrAntiGroup_le_complexGeneralMobiusGroup
    (Or.inr (by rw [complexConjugation_sq];exact fractionalLinearGroup.one_mem))⟩

theorem fullMobiusPositiveSubgroup_index_two : fullMobiusPositiveSubgroup.index=2 := by
  apply (Subgroup.index_eq_two_iff).mpr
  refine ⟨fullMobiusConjugation,?_⟩
  intro f
  change Xor (f.val*complexConjugation∈complexMobiusGroup) (f.val∈complexMobiusGroup)
  rw [complexMobiusGroup_eq_fractionalLinearGroup]
  have hf:=complexGeneralMobiusGroup_le_fractionalOrAntiGroup f.property
  change f.val∈fractionalLinearGroup ∨ f.val*complexConjugation∈fractionalLinearGroup at hf
  rw [xor_iff_or_and_not_and]
  exact ⟨hf.symm,fun h=>fractional_and_anti_disjoint h.2 h.1⟩

theorem fullMobiusPositiveSubgroup_finiteIndex : fullMobiusPositiveSubgroup.FiniteIndex:=
  ⟨by rw [fullMobiusPositiveSubgroup_index_two];norm_num⟩

attribute [instance] fullMobiusPositiveSubgroup_finiteIndex

/-- The original derivative orientation condition identifies the actual positive subgroup. -/
theorem mem_fullMobiusPositiveSubgroup (f : complexGeneralMobiusGroup) :
    f∈fullMobiusPositiveSubgroup ↔ PreservesComplexOrientation f.val := by
  change f.val∈complexMobiusGroup ↔ _
  exact ⟨fun h=>h.2,fun h=>⟨f.property,h⟩⟩

/-- The actual positive part of any full group, as a subgroup of the original conformal group. -/
def fullGroupPositivePart (H : Subgroup complexGeneralMobiusGroup) : Subgroup complexMobiusGroup:=
  H.comap complexMobiusToFull

/-- The very same actual subgroup inside the full group. -/
def fullGroupPositiveKernel (H : Subgroup complexGeneralMobiusGroup) : Subgroup H:=
  fullMobiusPositiveSubgroup.comap H.subtype

theorem fullGroupPositiveKernel_finiteIndex (H : Subgroup complexGeneralMobiusGroup) :
    (fullGroupPositiveKernel H).FiniteIndex:=by
  change (fullMobiusPositiveSubgroup.comap H.subtype).FiniteIndex
  infer_instance

attribute [instance] fullGroupPositiveKernel_finiteIndex

def fullGroupPositivePartEquiv (H : Subgroup complexGeneralMobiusGroup) :
    fullGroupPositivePart H ≃* fullGroupPositiveKernel H where
  toFun x:=⟨⟨complexMobiusToFull x.val,x.property⟩,x.val.property⟩
  invFun x:=⟨⟨x.val.val.val,x.property⟩,x.val.property⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_mul' _ _:=rfl

theorem fullGroupPositivePartEquiv_isometry (H : Subgroup complexGeneralMobiusGroup) :
    Isometry (fullGroupPositivePartEquiv H) := by
  apply Isometry.of_dist_eq
  intro f g
  rfl

def fullGroupPositivePartHomeomorph (H : Subgroup complexGeneralMobiusGroup) :
    fullGroupPositivePart H ≃ₜ fullGroupPositiveKernel H where
  toEquiv:=(fullGroupPositivePartEquiv H).toEquiv
  continuous_toFun:=(fullGroupPositivePartEquiv_isometry H).continuous
  continuous_invFun:=by
    have hi : Isometry (fullGroupPositivePartEquiv H).symm:=by
      apply Isometry.of_dist_eq
      intro f g
      rfl
    exact hi.continuous

/-- The existing real geometric group and its actual extended-complex coordinate image are isomorphic. -/
def realGeneralMobiusEquivComplex : Inversive.GM 2 ≃* complexGeneralMobiusGroup:=
  (Inversive.generalMobiusGroup 2).equivMapOfInjective euclideanToComplexHom euclideanToComplexHom_injective

/-- The real representative is the actual global coordinate change, not a reflection-word choice. -/
def fullMobiusRealRepresentative : complexGeneralMobiusGroup →* Inversive.GM 2:=
  realGeneralMobiusEquivComplex.symm.toMonoidHom

theorem fullMobiusRealRepresentative_direct (f : complexMobiusGroup) :
    fullMobiusRealRepresentative (complexMobiusToFull f)=mobiusRealRepresentativeHom f := by
  apply realGeneralMobiusEquivComplex.injective
  change realGeneralMobiusEquivComplex (realGeneralMobiusEquivComplex.symm (complexMobiusToFull f))=_
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  change f.val=euclideanToComplexHom (mobiusRealRepresentativeHom f)
  exact (mobiusRealRepresentative_coordinates f).symm

/-- The actual full Poincare extension, including every genuine orientation-reversing map. -/
def fullMobiusPoincareHom : complexGeneralMobiusGroup →* Inversive.GM 3:=
  Hyperbolic.poincareExtensionHom.comp fullMobiusRealRepresentative

theorem fullMobiusPoincareHom_direct (f : complexMobiusGroup) :
    fullMobiusPoincareHom (complexMobiusToFull f)=mobiusGeometricPoincareHom f := by
  change Hyperbolic.poincareExtensionHom (fullMobiusRealRepresentative (complexMobiusToFull f))=_
  rw [fullMobiusRealRepresentative_direct]
  rfl

@[instance_reducible]
def fullMobiusCompactifiedSpaceMulAction : MulAction complexGeneralMobiusGroup (Inversive.ExtendedEuclidean 3) where
  smul f z:=(fullMobiusPoincareHom f : Inversive.ExtendedHomeomorph 3) z
  one_smul z:=by
    change ((fullMobiusPoincareHom 1 : Inversive.GM 3) : Inversive.ExtendedHomeomorph 3) z=z;rw [map_one];rfl
  mul_smul f g z:=by
    change ((fullMobiusPoincareHom (f*g) : Inversive.GM 3) : Inversive.ExtendedHomeomorph 3) z=
      (fullMobiusPoincareHom f : Inversive.ExtendedHomeomorph 3) ((fullMobiusPoincareHom g :
        Inversive.ExtendedHomeomorph 3) z)
    rw [map_mul]
    rfl

attribute [instance] fullMobiusCompactifiedSpaceMulAction

theorem fullMobiusCompactifiedSpace_action_direct (f : complexMobiusGroup) (z : Inversive.ExtendedEuclidean 3) :
    complexMobiusToFull f • z=f • z := by
  change (fullMobiusPoincareHom (complexMobiusToFull f) : Inversive.ExtendedHomeomorph 3) z=_
  rw [fullMobiusPoincareHom_direct]
  rfl

/-- Non-elementarity uses the actual entire compactified Poincare space, in the existing formulation convention. -/
def IsFullNonElementary (H : Subgroup complexGeneralMobiusGroup) : Prop:=
  ¬DiscreteGroups.Action.HasFiniteOrbit H (Inversive.ExtendedEuclidean 3)

theorem fullGroupPositivePart_orbit (H : Subgroup complexGeneralMobiusGroup) (z : Inversive.ExtendedEuclidean 3) :
    MulAction.orbit (fullGroupPositivePart H) z=MulAction.orbit (fullGroupPositiveKernel H) z := by
  ext x
  constructor
  · rintro ⟨f,rfl⟩
    refine ⟨fullGroupPositivePartEquiv H f,?_⟩
    exact fullMobiusCompactifiedSpace_action_direct f.val z
  · rintro ⟨f,rfl⟩
    refine ⟨(fullGroupPositivePartEquiv H).symm f,?_⟩
    exact (fullMobiusCompactifiedSpace_action_direct ((fullGroupPositivePartEquiv H).symm f).val z).symm

/-- A non-elementary full group has a genuinely non-elementary actual conformal part. -/
theorem IsFullNonElementary.positivePart {H : Subgroup complexGeneralMobiusGroup}
    (hH : IsFullNonElementary H) : DiscreteGroups.IsNonElementary (fullGroupPositivePart H) := by
  intro hE
  apply hH
  obtain ⟨z,hz⟩:=(DiscreteGroups.isElementary_iff_compactified_finite_orbit (fullGroupPositivePart H)).mp hE
  rw [fullGroupPositivePart_orbit] at hz
  exact DiscreteGroups.hasFiniteOrbit_of_finiteIndex (fullGroupPositiveKernel H) ⟨z,hz⟩

end
end LowDimensionalTopology.Geometry.Mobius
