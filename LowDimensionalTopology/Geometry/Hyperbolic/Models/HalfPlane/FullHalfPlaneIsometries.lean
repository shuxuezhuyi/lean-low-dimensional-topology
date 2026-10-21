/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.FiniteOrbit
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.DiscreteGroups.Discreteness.FullDiscretenessCriteria
@[expose] public section
open Set Filter
open scoped Topology OnePoint UpperHalfPlane MatrixGroups ComplexConjugate
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- The genuine global axis reflection is the anti-fractional map z ↦ -conj z, including infinity. -/
def fullMobiusAxisReflection : Mobius.complexGeneralMobiusGroup:=
  Mobius.complexMobiusToFull (Mobius.mobiusScaling (-1))*Mobius.fullMobiusConjugation

theorem fullMobiusAxisReflection_coe (z : ℂ) :
    fullMobiusAxisReflection.val z=((-conj z : ℂ) : Mobius.ExtendedComplex) := by
  change (Mobius.mobiusScaling (-1)).val (Mobius.complexConjugation z)=_
  rw [Mobius.complexConjugation_coe,Mobius.mobiusScaling_coe]
  simp only [Units.val_neg,Units.val_one,neg_one_mul]

theorem fullMobiusAxisReflection_infty : fullMobiusAxisReflection.val ∞=∞ := by
  change (Mobius.mobiusScaling (-1)).val (Mobius.complexConjugation ∞)=∞
  rw [Mobius.complexConjugation_infty,Mobius.mobiusScaling_infty]

theorem fullMobiusAxisReflection_sq : fullMobiusAxisReflection^2=1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  cases z with
  | none => change fullMobiusAxisReflection.val (fullMobiusAxisReflection.val ∞)=∞;rw [fullMobiusAxisReflection_infty,fullMobiusAxisReflection_infty]
  | some z =>
    change fullMobiusAxisReflection.val (fullMobiusAxisReflection.val z)=z
    rw [fullMobiusAxisReflection_coe,fullMobiusAxisReflection_coe]
    simp

theorem fullMobiusAxisReflection_halfPlane (z : ℍ) :
    fullMobiusAxisReflection.val (Mobius.halfPlaneBoundaryPoint z)=Mobius.halfPlaneBoundaryPoint (UpperHalfPlane.J •
      z) := by
  change fullMobiusAxisReflection.val ((z : ℂ) : Mobius.ExtendedComplex)=(((UpperHalfPlane.J • z : ℍ) : ℂ) :
    Mobius.ExtendedComplex)
  rw [fullMobiusAxisReflection_coe,UpperHalfPlane.coe_J_smul]

theorem halfPlaneBoundaryPoint_range : range Mobius.halfPlaneBoundaryPoint=openHalfPlaneSet := by
  ext p
  constructor
  · rintro ⟨z,rfl⟩
    exact Mobius.halfPlaneBoundaryPoint_mem z
  · rintro ⟨z,hz,rfl⟩
    exact ⟨⟨z,hz⟩,rfl⟩

theorem fullMobiusAxisReflection_preserves_halfPlane :
    fullMobiusAxisReflection.val '' openHalfPlaneSet=openHalfPlaneSet := by
  rw [←halfPlaneBoundaryPoint_range]
  ext p
  constructor
  · rintro ⟨_,⟨z,rfl⟩,rfl⟩
    exact ⟨UpperHalfPlane.J • z,(fullMobiusAxisReflection_halfPlane z).symm⟩
  · rintro ⟨z,rfl⟩
    refine ⟨Mobius.halfPlaneBoundaryPoint (UpperHalfPlane.J • z),mem_range_self _,?_⟩
    rw [fullMobiusAxisReflection_halfPlane,smul_smul,←pow_two,UpperHalfPlane.J_sq,one_smul]

/-- Every genuine full map preserving H has exactly the expected direct-or-reflected actual form. -/
theorem fullMobius_preserves_halfPlane_normal_form (f : Mobius.complexGeneralMobiusGroup)
    (hf : f.val '' openHalfPlaneSet=openHalfPlaneSet) :
    ∃A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      f=Mobius.complexMobiusToFull (realSLMobius A) ∨
      f=Mobius.complexMobiusToFull (realSLMobius A)*fullMobiusAxisReflection := by
  have hn:=Mobius.complexGeneralMobiusGroup_le_fractionalOrAntiGroup f.property
  rcases hn with hd | ha
  · have hM : f.val∈Mobius.complexMobiusGroup:=by rw [Mobius.complexMobiusGroup_eq_fractionalLinearGroup];exact hd
    obtain ⟨A,hA⟩:=Fuchsian.mobius_preserves_halfPlane_exists_SL ⟨f.val,hM⟩ hf
    exact ⟨A,Or.inl (congrArg Mobius.complexMobiusToFull hA).symm⟩
  · let F:=f*fullMobiusAxisReflection
    have hFdirect : F.val∈Mobius.complexMobiusGroup:=by
      rw [Mobius.complexMobiusGroup_eq_fractionalLinearGroup]
      have hs : (Mobius.mobiusScaling (-1)).val∈Mobius.fractionalLinearGroup:=by
        rw [←Mobius.complexMobiusGroup_eq_fractionalLinearGroup]
        exact (Mobius.mobiusScaling (-1)).property
      have hh:=Mobius.anti_mul_direct ha hs
      simpa only [F,fullMobiusAxisReflection,Subgroup.coe_mul,Mobius.complexMobiusToFull,
        MonoidHom.coe_mk,OneHom.coe_mk,Mobius.fullMobiusConjugation,mul_assoc] using hh
    have hFH : F.val '' openHalfPlaneSet=openHalfPlaneSet:=by
      change (f.val*fullMobiusAxisReflection.val) '' openHalfPlaneSet=_
      rw [Equiv.Perm.coe_mul,Function.comp_def,←Set.image_image f.val fullMobiusAxisReflection.val openHalfPlaneSet]
      rw [fullMobiusAxisReflection_preserves_halfPlane,hf]
    obtain ⟨A,hA⟩:=Fuchsian.mobius_preserves_halfPlane_exists_SL ⟨F.val,hFdirect⟩ hFH
    have hAF : Mobius.complexMobiusToFull (realSLMobius A)=F:=congrArg Mobius.complexMobiusToFull hA
    refine ⟨A,Or.inr ?_⟩
    rw [hAF]
    change f=(f*fullMobiusAxisReflection)*fullMobiusAxisReflection
    rw [mul_assoc,←pow_two,fullMobiusAxisReflection_sq,mul_one]

/-- Every native isometry has a genuine full global extension. -/
theorem exists_fullMobius_extension_isometry {f : ℍ → ℍ} (hf : Isometry f) :
    ∃F : Mobius.complexGeneralMobiusGroup,F.val '' openHalfPlaneSet=openHalfPlaneSet ∧
      ∀z : ℍ,F.val (Mobius.halfPlaneBoundaryPoint z)=Mobius.halfPlaneBoundaryPoint (f z) := by
  obtain ⟨A,hA | hA⟩:=isometry_exists_sl2_or_reflected hf
  · refine ⟨Mobius.complexMobiusToFull (realSLMobius A),Fuchsian.realSLMobius_image_openHalfPlane A,?_⟩
    intro z
    rw [hA]
    exact realSLMobius_action A z
  · refine ⟨Mobius.complexMobiusToFull (realSLMobius A)*fullMobiusAxisReflection,?_,?_⟩
    · change ((realSLMobius A).val*fullMobiusAxisReflection.val) '' openHalfPlaneSet=_
      rw [Equiv.Perm.coe_mul,Function.comp_def,←Set.image_image (realSLMobius A).val fullMobiusAxisReflection.val
        openHalfPlaneSet]
      rw [fullMobiusAxisReflection_preserves_halfPlane,Fuchsian.realSLMobius_image_openHalfPlane]
    · intro z
      change (realSLMobius A).val (fullMobiusAxisReflection.val (Mobius.halfPlaneBoundaryPoint z))=_
      rw [fullMobiusAxisReflection_halfPlane]
      exact (realSLMobius_action A (UpperHalfPlane.J • z)).trans (congrArg Mobius.halfPlaneBoundaryPoint (congrFun hA
        z).symm)

/-- Each full geometric H preserver induces a genuine native hyperbolic isometry. -/
theorem fullMobius_preserves_halfPlane_isometry (F : Mobius.complexGeneralMobiusGroup)
    (hF : F.val '' openHalfPlaneSet=openHalfPlaneSet) :
    ∃f : ℍ → ℍ,Isometry f ∧ ∀z : ℍ,F.val (Mobius.halfPlaneBoundaryPoint z)=Mobius.halfPlaneBoundaryPoint (f z) := by
  obtain ⟨A,rfl | rfl⟩:=fullMobius_preserves_halfPlane_normal_form F hF
  · exact ⟨(A • · : ℍ → ℍ),isometry_smul ℍ A,realSLMobius_action A⟩
  · refine ⟨(A • · : ℍ → ℍ) ∘ (UpperHalfPlane.J • ·),
      (isometry_smul ℍ A).comp (realGL_isometry UpperHalfPlane.J),?_⟩
    intro z
    change (realSLMobius A).val (fullMobiusAxisReflection.val (Mobius.halfPlaneBoundaryPoint z))=_
    rw [fullMobiusAxisReflection_halfPlane]
    exact realSLMobius_action A (UpperHalfPlane.J • z)

/-- A negative determinant GL action cannot be the identity on the actual half-plane. -/
theorem negative_realGL_not_identity (g : GL (Fin 2) ℝ) (hg : g.val.det<0) :
    ¬∀z : ℍ,g • z=z := by
  intro hall
  have hc:=UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mp hall
  obtain ⟨a,ha⟩:=Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hc
  have hd : g.val.det=a^2:=by
    rw [←ha]
    simp [Matrix.scalar_apply,pow_two]
  rw [hd] at hg
  exact not_lt_of_ge (sq_nonneg a) hg

/-- The genuine extension is faithful on H, including the anti-fractional branch. -/
theorem fullMobius_eq_one_of_halfPlane_identity (F : Mobius.complexGeneralMobiusGroup)
    (hF : F.val '' openHalfPlaneSet=openHalfPlaneSet)
    (hfix : ∀z : ℍ,F.val (Mobius.halfPlaneBoundaryPoint z)=Mobius.halfPlaneBoundaryPoint z) : F=1 := by
  obtain ⟨A,rfl | rfl⟩:=fullMobius_preserves_halfPlane_normal_form F hF
  · have he : realSLMobius A=1:=by
      apply Fuchsian.mobius_ext_on_halfPlane
      exact hfix
    rw [he,map_one]
  · exfalso
    let g : GL (Fin 2) ℝ:=Matrix.SpecialLinearGroup.mapGL ℝ A*UpperHalfPlane.J
    have hg : g.val.det<0:=by
      change (g.det : ℝ)<0
      simp [g,map_mul]
    apply negative_realGL_not_identity g hg
    intro z
    apply Mobius.halfPlaneBoundaryPoint_injective
    have he:=hfix z
    change (realSLMobius A).val (fullMobiusAxisReflection.val (Mobius.halfPlaneBoundaryPoint
      z))=Mobius.halfPlaneBoundaryPoint z at he
    rw [fullMobiusAxisReflection_halfPlane] at he
    change (realSLMobius A).val (((UpperHalfPlane.J • z : ℍ) : ℂ) :
      Mobius.ExtendedComplex)=Mobius.halfPlaneBoundaryPoint z at he
    rw [realSLMobius_action] at he
    change Mobius.halfPlaneBoundaryPoint ((Matrix.SpecialLinearGroup.mapGL ℝ A*UpperHalfPlane.J) •
      z)=Mobius.halfPlaneBoundaryPoint z
    rw [mul_smul]
    change (((Matrix.SpecialLinearGroup.mapGL ℝ A • (UpperHalfPlane.J • z) : ℍ) : ℂ) :
      Mobius.ExtendedComplex)=Mobius.halfPlaneBoundaryPoint z
    simpa only [MulAction.compHom_smul_def] using he


/-- The entire actual full geometric subgroup preserving the native half-plane. -/
def fullHalfPlaneGroup : Subgroup Mobius.complexGeneralMobiusGroup where
  carrier:={F | F.val '' openHalfPlaneSet=openHalfPlaneSet}
  one_mem':=by change (id : Mobius.ExtendedComplex → Mobius.ExtendedComplex) '' openHalfPlaneSet=_;exact Set.image_id _
  mul_mem':=by
    intro F G hF hG
    change (F.val*G.val) '' openHalfPlaneSet=_
    rw [Equiv.Perm.coe_mul,Function.comp_def,←Set.image_image F.val G.val openHalfPlaneSet,hG,hF]
  inv_mem':=by
    intro F hF
    have hi:=congrArg (fun S : Set Mobius.ExtendedComplex=>F.val.symm '' S) hF
    change F.val.symm '' openHalfPlaneSet=openHalfPlaneSet
    rw [←hi,Set.image_image]
    simp only [Equiv.symm_apply_apply,Set.image_id']

/-- The native action is chosen from the proved genuine direct-or-reflected representation. -/
def fullHalfPlaneNative (F : fullHalfPlaneGroup) : ℍ → ℍ:=
  (fullMobius_preserves_halfPlane_isometry F.val F.property).choose

theorem fullHalfPlaneNative_isometry (F : fullHalfPlaneGroup) : Isometry (fullHalfPlaneNative F):=
  (fullMobius_preserves_halfPlane_isometry F.val F.property).choose_spec.1

theorem fullHalfPlaneNative_action (F : fullHalfPlaneGroup) (z : ℍ) :
    F.val.val (Mobius.halfPlaneBoundaryPoint z)=Mobius.halfPlaneBoundaryPoint (fullHalfPlaneNative F z):=
  (fullMobius_preserves_halfPlane_isometry F.val F.property).choose_spec.2 z

/-- Every full preserver gives an actual bijective native isometry. -/
def fullHalfPlaneNativeEquiv (F : fullHalfPlaneGroup) : ℍ ≃ᵢ ℍ where
  toEquiv:=Equiv.ofBijective (fullHalfPlaneNative F)
    ⟨(fullHalfPlaneNative_isometry F).injective,(fullHalfPlaneNative_isometry F).halfPlane_surjective⟩
  isometry_toFun:=fullHalfPlaneNative_isometry F

theorem fullHalfPlaneNativeEquiv_action (F : fullHalfPlaneGroup) (z : ℍ) :
    F.val.val (Mobius.halfPlaneBoundaryPoint z)=Mobius.halfPlaneBoundaryPoint (fullHalfPlaneNativeEquiv F z):=
  fullHalfPlaneNative_action F z

/-- The representation respects genuine composition, not just the metric of individual maps. -/
def fullHalfPlaneNativeHom : fullHalfPlaneGroup →* (ℍ ≃ᵢ ℍ) where
  toFun:=fullHalfPlaneNativeEquiv
  map_one':=by
    apply IsometryEquiv.ext
    intro z
    apply Mobius.halfPlaneBoundaryPoint_injective
    exact (fullHalfPlaneNativeEquiv_action 1 z).symm
  map_mul':=by
    intro F G
    apply IsometryEquiv.ext
    intro z
    apply Mobius.halfPlaneBoundaryPoint_injective
    calc
      Mobius.halfPlaneBoundaryPoint (fullHalfPlaneNativeEquiv (F*G) z)=
          (F*G).val.val (Mobius.halfPlaneBoundaryPoint z):=(fullHalfPlaneNativeEquiv_action (F*G) z).symm
      _=F.val.val (G.val.val (Mobius.halfPlaneBoundaryPoint z)):=by rfl
      _=F.val.val (Mobius.halfPlaneBoundaryPoint (fullHalfPlaneNativeEquiv G z)):=
        by rw [fullHalfPlaneNativeEquiv_action]
      _=Mobius.halfPlaneBoundaryPoint (fullHalfPlaneNativeEquiv F (fullHalfPlaneNativeEquiv G
        z)):=fullHalfPlaneNativeEquiv_action F _

/-- Faithfulness includes the orientation reversing component. -/
theorem fullHalfPlaneNativeHom_injective : Function.Injective fullHalfPlaneNativeHom := by
  apply (injective_iff_map_eq_one _).mpr
  intro F hF
  apply Subtype.ext
  apply fullMobius_eq_one_of_halfPlane_identity F.val F.property
  intro z
  have he:=fullHalfPlaneNativeEquiv_action F z
  have hz : fullHalfPlaneNativeEquiv F z=z:=congrArg (fun e : ℍ ≃ᵢ ℍ=>e z) hF
  rw [hz] at he
  exact he

/-- Every native half-plane isometry occurs in the full geometric group. -/
theorem fullHalfPlaneNativeHom_surjective : Function.Surjective fullHalfPlaneNativeHom := by
  intro f
  obtain ⟨F,hF,hact⟩:=exists_fullMobius_extension_isometry f.isometry
  refine ⟨⟨F,hF⟩,?_⟩
  apply IsometryEquiv.ext
  intro z
  apply Mobius.halfPlaneBoundaryPoint_injective
  exact (fullHalfPlaneNativeEquiv_action ⟨F,hF⟩ z).symm.trans (hact z)

/-- The actual full geometric group preserving H is exactly the entire native isometry group. -/
def fullHalfPlaneIsometryEquiv : fullHalfPlaneGroup ≃* (ℍ ≃ᵢ ℍ):=
  MulEquiv.ofBijective fullHalfPlaneNativeHom ⟨fullHalfPlaneNativeHom_injective,fullHalfPlaneNativeHom_surjective⟩


/-- The unique actual global boundary extension of a native half-plane isometry. -/
def nativeHalfPlaneExtension : (ℍ ≃ᵢ ℍ) →* Mobius.complexGeneralMobiusGroup:=
  fullHalfPlaneGroup.subtype.comp fullHalfPlaneIsometryEquiv.symm.toMonoidHom

theorem nativeHalfPlaneExtension_injective : Function.Injective nativeHalfPlaneExtension:=
  Subtype.val_injective.comp fullHalfPlaneIsometryEquiv.symm.injective

theorem nativeHalfPlaneExtension_preserves (f : ℍ ≃ᵢ ℍ) :
    (nativeHalfPlaneExtension f).val '' openHalfPlaneSet=openHalfPlaneSet:=
  (fullHalfPlaneIsometryEquiv.symm f).property

theorem nativeHalfPlaneExtension_action (f : ℍ ≃ᵢ ℍ) (z : ℍ) :
    (nativeHalfPlaneExtension f).val (Mobius.halfPlaneBoundaryPoint z)=Mobius.halfPlaneBoundaryPoint (f z) := by
  have he:=fullHalfPlaneNativeEquiv_action (fullHalfPlaneIsometryEquiv.symm f) z
  have heq : fullHalfPlaneNativeEquiv (fullHalfPlaneIsometryEquiv.symm
    f)=f:=fullHalfPlaneIsometryEquiv.apply_symm_apply f
  rw [heq] at he
  exact he

/-- Native all-isometry groups carry the geometric actual uniform chordal boundary topology. -/
@[instance_reducible]
def nativeHalfPlaneMetricSpace : MetricSpace (ℍ ≃ᵢ ℍ):=
  MetricSpace.induced nativeHalfPlaneExtension nativeHalfPlaneExtension_injective inferInstance
attribute [instance] nativeHalfPlaneMetricSpace

theorem nativeHalfPlaneExtension_isometry : Isometry nativeHalfPlaneExtension:=by
  apply Isometry.of_dist_eq
  intro f g
  rfl

theorem fullHalfPlaneIsometryEquiv_isometry : Isometry fullHalfPlaneIsometryEquiv := by
  apply Isometry.of_dist_eq
  intro F G
  change dist (fullHalfPlaneIsometryEquiv.symm (fullHalfPlaneIsometryEquiv F)).val
    (fullHalfPlaneIsometryEquiv.symm (fullHalfPlaneIsometryEquiv G)).val=dist F.val G.val
  rw [fullHalfPlaneIsometryEquiv.symm_apply_apply,fullHalfPlaneIsometryEquiv.symm_apply_apply]

/-- The algebraic all-isometry representation also preserves the precise boundary uniform topology. -/
def fullHalfPlaneIsometryHomeomorph : fullHalfPlaneGroup ≃ₜ (ℍ ≃ᵢ ℍ):=
  (⟨fullHalfPlaneIsometryEquiv.toEquiv,fullHalfPlaneIsometryEquiv_isometry⟩ : fullHalfPlaneGroup ≃ᵢ (ℍ ≃ᵢ
    ℍ)).toHomeomorph

/-- A native subgroup represented by its actual global boundary extensions. -/
def nativeHalfPlaneImage (H : Subgroup (ℍ ≃ᵢ ℍ)) : Subgroup Mobius.complexGeneralMobiusGroup:=
  H.map nativeHalfPlaneExtension

/-- The actual subgroup isomorphism, with no additional faithfulness assumption. -/
def nativeHalfPlaneSubgroupEquiv (H : Subgroup (ℍ ≃ᵢ ℍ)) : H ≃* nativeHalfPlaneImage H:=
  H.equivMapOfInjective nativeHalfPlaneExtension nativeHalfPlaneExtension_injective

theorem nativeHalfPlaneSubgroupEquiv_isometry (H : Subgroup (ℍ ≃ᵢ ℍ)) :
    Isometry (nativeHalfPlaneSubgroupEquiv H):=by
  apply Isometry.of_dist_eq
  intro f g
  rfl

def nativeHalfPlaneSubgroupHomeomorph (H : Subgroup (ℍ ≃ᵢ ℍ)) : H ≃ₜ nativeHalfPlaneImage H:=
  (⟨(nativeHalfPlaneSubgroupEquiv H).toEquiv,nativeHalfPlaneSubgroupEquiv_isometry H⟩ : H ≃ᵢ nativeHalfPlaneImage
    H).toHomeomorph

theorem nativeHalfPlane_subgroup_discrete_iff (H : Subgroup (ℍ ≃ᵢ ℍ)) :
    DiscreteTopology H ↔ DiscreteTopology (nativeHalfPlaneImage H):=
  (nativeHalfPlaneSubgroupHomeomorph H).discreteTopology_iff

/-- The native plane and its actual open sphere model have identical topologies. -/
theorem halfPlaneBoundaryPoint_isOpenEmbedding : Topology.IsOpenEmbedding Mobius.halfPlaneBoundaryPoint:=
  OnePoint.isOpenEmbedding_coe.comp UpperHalfPlane.isOpenEmbedding_coe

def halfPlaneOpenModelHomeomorph : ℍ ≃ₜ openHalfPlaneSet:=
  halfPlaneBoundaryPoint_isOpenEmbedding.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr halfPlaneBoundaryPoint_range)


/-- The genuine action of all native isometries is evaluation. -/
@[instance_reducible]
def nativeHalfPlaneMulAction : MulAction (ℍ ≃ᵢ ℍ) ℍ where
  smul f z:=f z
  one_smul _:=rfl
  mul_smul _ _ _:=rfl
attribute [instance] nativeHalfPlaneMulAction

/-- Every subgroup's full boundary image really preserves the half-plane. -/
theorem nativeHalfPlaneImage_preserves (H : Subgroup (ℍ ≃ᵢ ℍ))
    (F : nativeHalfPlaneImage H) : F.val.val '' openHalfPlaneSet=openHalfPlaneSet:=by
  obtain ⟨f,hf,he⟩:=F.property
  change nativeHalfPlaneExtension f=F.val at he
  rw [←he]
  exact nativeHalfPlaneExtension_preserves f

/-- Actual compact-set discontinuity agrees in the native and sphere models. -/
theorem nativeHalfPlane_discontinuous_iff (H : Subgroup (ℍ ≃ᵢ ℍ)) :
    DiscreteGroups.Action.IsDiscontinuous H ℍ ↔ DiscreteGroups.IsFullMobiusDiscontinuousOn (nativeHalfPlaneImage
      H) openHalfPlaneSet := by
  have hi : ∀(F : nativeHalfPlaneImage H) p,p∈openHalfPlaneSet → F • p∈openHalfPlaneSet:=by
    intro F p hp
    rw [←nativeHalfPlaneImage_preserves H F]
    exact mem_image_of_mem _ hp
  let : MulAction (nativeHalfPlaneImage
    H) openHalfPlaneSet:=DiscreteGroups.Action.invariantSubsetMulAction openHalfPlaneSet hi
  have he (f : H) (z : ℍ) :
      halfPlaneOpenModelHomeomorph (f • z)=nativeHalfPlaneSubgroupEquiv H f • halfPlaneOpenModelHomeomorph z:=by
    apply Subtype.ext
    exact (nativeHalfPlaneExtension_action f.val z).symm
  rw [DiscreteGroups.isFullMobiusDiscontinuousOn_iff_subtype _ _ hi]
  constructor
  · exact fun h=>h.transport (nativeHalfPlaneSubgroupEquiv H).toEquiv halfPlaneOpenModelHomeomorph he
  · intro h
    apply h.transport (nativeHalfPlaneSubgroupEquiv H).symm.toEquiv halfPlaneOpenModelHomeomorph.symm
    intro F p
    apply halfPlaneOpenModelHomeomorph.injective
    rw [Homeomorph.apply_symm_apply]
    change F • p=halfPlaneOpenModelHomeomorph ((nativeHalfPlaneSubgroupEquiv H).symm F •
      halfPlaneOpenModelHomeomorph.symm p)
    simpa only [Homeomorph.apply_symm_apply,MulEquiv.apply_symm_apply] using
      (he ((nativeHalfPlaneSubgroupEquiv H).symm F) (halfPlaneOpenModelHomeomorph.symm p)).symm


/-- The actual native elliptic type is read from its unique global geometric extension. -/
def NativeHalfPlaneElliptic (f : ℍ ≃ᵢ ℍ) : Prop:=DiscreteGroups.FullMobiusElliptic (nativeHalfPlaneExtension f)

def nativeHalfPlaneEllipticFixedPointSet (H : Subgroup (ℍ ≃ᵢ ℍ)) : Set ℍ:=
  {z | ∃f : H,NativeHalfPlaneElliptic f.val ∧ f.val z=z}

def NativeHalfPlaneFixedPointsNonaccumulating (H : Subgroup (ℍ ≃ᵢ ℍ)) : Prop:=
  ∀z : ℍ,¬AccPt z (𝓟 (nativeHalfPlaneEllipticFixedPointSet H))

def NativeHalfPlaneEllipticsNonaccumulatingAtIdentity (H : Subgroup (ℍ ≃ᵢ ℍ)) : Prop:=
  ∀ᶠf in 𝓝 (1 : H),¬NativeHalfPlaneElliptic f.val

def NativeHalfPlaneEllipticsFiniteOrder (H : Subgroup (ℍ ≃ᵢ ℍ)) : Prop:=
  ∀f∈H,NativeHalfPlaneElliptic f → IsOfFinOrder f

def NativeHalfPlaneAllCyclicSubgroupsDiscrete (H : Subgroup (ℍ ≃ᵢ ℍ)) : Prop:=
  ∀f∈H,DiscreteTopology (Subgroup.zpowers f)

theorem nativeHalfPlane_fixedPointSet_preimage (H : Subgroup (ℍ ≃ᵢ ℍ)) :
    Mobius.halfPlaneBoundaryPoint ⁻¹' DiscreteGroups.fullEllipticFixedPointSet (nativeHalfPlaneImage H)=
      nativeHalfPlaneEllipticFixedPointSet H := by
  ext z
  constructor
  · rintro ⟨F,hE,hfix⟩
    obtain ⟨f,hf,he⟩:=F.property
    change nativeHalfPlaneExtension f=F.val at he
    refine ⟨⟨f,hf⟩,?_,?_⟩
    · change DiscreteGroups.FullMobiusElliptic (nativeHalfPlaneExtension f)
      rw [he]
      exact hE
    · apply Mobius.halfPlaneBoundaryPoint_injective
      rw [←nativeHalfPlaneExtension_action,he]
      exact hfix
  · rintro ⟨f,hE,hfix⟩
    refine ⟨nativeHalfPlaneSubgroupEquiv H f,hE,?_⟩
    change (nativeHalfPlaneExtension f.val).val (Mobius.halfPlaneBoundaryPoint z)=Mobius.halfPlaneBoundaryPoint z
    rw [nativeHalfPlaneExtension_action,hfix]

theorem nativeHalfPlane_fixedPointsNonaccumulating_iff (H : Subgroup (ℍ ≃ᵢ ℍ)) :
    NativeHalfPlaneFixedPointsNonaccumulating H ↔
      DiscreteGroups.FullEllipticFixedPointsNonaccumulating (nativeHalfPlaneImage H) openHalfPlaneSet := by
  have hacc (z : ℍ) : AccPt z (𝓟 (nativeHalfPlaneEllipticFixedPointSet H)) ↔
      AccPt (Mobius.halfPlaneBoundaryPoint z) (𝓟 (DiscreteGroups.fullEllipticFixedPointSet (nativeHalfPlaneImage H))):=
        by
    simpa only [Filter.comap_principal,nativeHalfPlane_fixedPointSet_preimage] using
      (halfPlaneBoundaryPoint_isOpenEmbedding.accPt_comap_iff
        (x:=z) (l:=𝓟 (DiscreteGroups.fullEllipticFixedPointSet (nativeHalfPlaneImage H))))
  constructor
  · intro h p hp
    obtain ⟨z,rfl⟩:=halfPlaneBoundaryPoint_range.symm ▸ hp
    exact fun ha=>h z ((hacc z).mpr ha)
  · intro h z ha
    exact h _ (Mobius.halfPlaneBoundaryPoint_mem z) ((hacc z).mp ha)

theorem full_ellipticsNonaccumulating_iff_subtype (H : Subgroup Mobius.complexGeneralMobiusGroup) :
    DiscreteGroups.FullEllipticsNonaccumulatingAtIdentity H ↔
      ∀ᶠF in 𝓝 (1 : H),¬DiscreteGroups.FullMobiusElliptic F.val := by
  constructor
  · intro h
    exact ((continuous_subtype_val.tendsto (1 : H)).eventually h).mono (fun F hF=>hF F.property)
  · intro h
    rw [nhds_subtype_eq_comap,Filter.eventually_comap] at h
    filter_upwards [h] with F hF hFH
    exact hF ⟨F,hFH⟩ rfl

theorem nativeHalfPlane_ellipticsNonaccumulating_iff (H : Subgroup (ℍ ≃ᵢ ℍ)) :
    NativeHalfPlaneEllipticsNonaccumulatingAtIdentity H ↔
      DiscreteGroups.FullEllipticsNonaccumulatingAtIdentity (nativeHalfPlaneImage H) := by
  rw [full_ellipticsNonaccumulating_iff_subtype]
  have hm:=(nativeHalfPlaneSubgroupHomeomorph H).map_nhds_eq (1 : H)
  rw [show nativeHalfPlaneSubgroupHomeomorph H (1 : H)=1 from map_one (nativeHalfPlaneSubgroupEquiv H)] at hm
  rw [←hm,Filter.eventually_map]
  rfl

theorem nativeHalfPlane_ellipticsFiniteOrder_iff (H : Subgroup (ℍ ≃ᵢ ℍ)) :
    NativeHalfPlaneEllipticsFiniteOrder H ↔ DiscreteGroups.FullEllipticsFiniteOrder (nativeHalfPlaneImage H) := by
  constructor
  · intro h F hF hE
    obtain ⟨f,hf,rfl⟩:=hF
    exact nativeHalfPlaneExtension.isOfFinOrder (h f hf hE)
  · intro h f hf hE
    have ho:=h _ ⟨f,hf,rfl⟩ hE
    exact nativeHalfPlaneExtension_injective.isOfFinOrder_iff.mp ho

theorem nativeHalfPlane_allCyclicSubgroupsDiscrete_iff (H : Subgroup (ℍ ≃ᵢ ℍ)) :
    NativeHalfPlaneAllCyclicSubgroupsDiscrete H ↔ DiscreteGroups.FullAllCyclicSubgroupsDiscrete (nativeHalfPlaneImage
      H) := by
  have hc (f : ℍ ≃ᵢ ℍ) : DiscreteTopology (Subgroup.zpowers f) ↔
      DiscreteTopology (Subgroup.zpowers (nativeHalfPlaneExtension f)):=by
    have he:=nativeHalfPlane_subgroup_discrete_iff (Subgroup.zpowers f)
    change DiscreteTopology (Subgroup.zpowers f) ↔ DiscreteTopology ((Subgroup.zpowers f).map
      nativeHalfPlaneExtension) at he
    rw [nativeHalfPlaneExtension.map_zpowers] at he
    exact he
  constructor
  · intro h F hF
    obtain ⟨f,hf,rfl⟩:=hF
    exact (hc f).mp (h f hf)
  · intro h f hf
    exact (hc f).mpr (h _ ⟨f,hf,rfl⟩)


/-- The full actual geometric Poincare action of every native isometry. -/
@[instance_reducible]
def nativeHalfPlanePoincareMulAction : MulAction (ℍ ≃ᵢ ℍ) (Inversive.ExtendedEuclidean 3):=
  MulAction.compHom (Inversive.ExtendedEuclidean 3) nativeHalfPlaneExtension
attribute [instance] nativeHalfPlanePoincareMulAction

def IsNativeHalfPlaneNonElementary (H : Subgroup (ℍ ≃ᵢ ℍ)) : Prop:=
  ¬DiscreteGroups.Action.HasFiniteOrbit H (Inversive.ExtendedEuclidean 3)

set_option maxHeartbeats 800000 in
theorem nativeHalfPlaneImage_orbit (H : Subgroup (ℍ ≃ᵢ ℍ)) (z : Inversive.ExtendedEuclidean 3) :
    MulAction.orbit H z=MulAction.orbit (nativeHalfPlaneImage H) z := by
  ext x
  constructor
  · rintro ⟨f,rfl⟩
    exact ⟨nativeHalfPlaneSubgroupEquiv H f,rfl⟩
  · rintro ⟨F,rfl⟩
    refine ⟨(nativeHalfPlaneSubgroupEquiv H).symm F,?_⟩
    have he:=(nativeHalfPlaneSubgroupEquiv H).apply_symm_apply F
    exact congrArg (fun G : nativeHalfPlaneImage H=>G.val • z) he

theorem nativeHalfPlane_nonElementary_iff (H : Subgroup (ℍ ≃ᵢ ℍ)) :
    IsNativeHalfPlaneNonElementary H ↔ Mobius.IsFullNonElementary (nativeHalfPlaneImage H) := by
  unfold IsNativeHalfPlaneNonElementary Mobius.IsFullNonElementary DiscreteGroups.Action.HasFiniteOrbit
  simp only [nativeHalfPlaneImage_orbit]

theorem openHalfPlaneSet_isComplexOpenDisc : Mobius.IsComplexOpenDisc openHalfPlaneSet := by
  have hD:=DiscreteGroups.extendedUnitDisc_isComplexOpenDisc.image cayleyMobius⁻¹
  have he : cayleyMobius⁻¹.val '' extendedUnitDisc=openHalfPlaneSet:=by
    rw [←Fuchsian.cayleyMobius_image_openHalfPlane,Set.image_image]
    change (fun z : Mobius.ExtendedComplex=>cayleyMobius⁻¹ • (cayleyMobius • z)) '' openHalfPlaneSet=openHalfPlaneSet
    simp only [inv_smul_smul,Set.image_id']
  rw [he] at hD
  exact hD

/-- For all native hyperbolic-plane isometries, with its actual six conditions. -/
theorem halfPlane_discreteness_elliptic_and_cyclic_criteria_tfae (H : Subgroup (ℍ ≃ᵢ ℍ))
    (hH : IsNativeHalfPlaneNonElementary H) :
    List.TFAE [DiscreteTopology H,DiscreteGroups.Action.IsDiscontinuous H ℍ,
      NativeHalfPlaneFixedPointsNonaccumulating H,NativeHalfPlaneEllipticsNonaccumulatingAtIdentity H,
      NativeHalfPlaneEllipticsFiniteOrder H,NativeHalfPlaneAllCyclicSubgroupsDiscrete H] := by
  have ht:=DiscreteGroups.full_discreteness_elliptic_and_cyclic_criteria_tfae (nativeHalfPlaneImage H)
    ((nativeHalfPlane_nonElementary_iff H).mp hH) openHalfPlaneSet openHalfPlaneSet_isComplexOpenDisc
    (nativeHalfPlaneImage_preserves H)
  simpa only [←nativeHalfPlane_subgroup_discrete_iff,←nativeHalfPlane_discontinuous_iff,
    ←nativeHalfPlane_fixedPointsNonaccumulating_iff,←nativeHalfPlane_ellipticsNonaccumulating_iff,
    ←nativeHalfPlane_ellipticsFiniteOrder_iff,←nativeHalfPlane_allCyclicSubgroupsDiscrete_iff] using ht


/-- The actual native metric is precisely the source's uniform sphere-boundary displacement. -/
theorem nativeHalfPlane_dist_eq_iSup (f g : ℍ ≃ᵢ ℍ) :
    dist f g=⨆z : Mobius.ExtendedComplex,
      Mobius.complexChordalDist ((nativeHalfPlaneExtension f).val z) ((nativeHalfPlaneExtension g).val z):=
  Mobius.fullMobiusUniformDist_eq_iSup _ _

theorem nativeHalfPlane_isTopologicalGroup : IsTopologicalGroup (ℍ ≃ᵢ ℍ) where
  continuous_mul:=by
    apply nativeHalfPlaneExtension_isometry.isEmbedding.isInducing.continuous_iff.mpr
    have hc : Continuous (fun p : (ℍ ≃ᵢ ℍ) × (ℍ ≃ᵢ ℍ)=>
        nativeHalfPlaneExtension p.1*nativeHalfPlaneExtension p.2):=
      continuous_mul.comp ((nativeHalfPlaneExtension_isometry.continuous.comp continuous_fst).prodMk
        (nativeHalfPlaneExtension_isometry.continuous.comp continuous_snd))
    convert hc using 1
    funext p
    exact map_mul nativeHalfPlaneExtension p.1 p.2
  continuous_inv:=by
    apply nativeHalfPlaneExtension_isometry.isEmbedding.isInducing.continuous_iff.mpr
    have hc : Continuous (fun f : ℍ ≃ᵢ ℍ=>(nativeHalfPlaneExtension f)⁻¹):=
      continuous_inv.comp nativeHalfPlaneExtension_isometry.continuous
    convert hc using 1
    funext f
    exact map_inv nativeHalfPlaneExtension f
attribute [instance] nativeHalfPlane_isTopologicalGroup

/-- The elliptic-free source observation also holds in the entire native isometry group. -/
theorem nativeHalfPlane_ellipticFree_all_six_criteria (H : Subgroup (ℍ ≃ᵢ ℍ))
    (hH : IsNativeHalfPlaneNonElementary H) (hE : ∀f∈H,¬NativeHalfPlaneElliptic f) :
    DiscreteTopology H ∧ DiscreteGroups.Action.IsDiscontinuous H ℍ ∧ NativeHalfPlaneFixedPointsNonaccumulating H ∧
      NativeHalfPlaneEllipticsNonaccumulatingAtIdentity H ∧ NativeHalfPlaneEllipticsFiniteOrder H ∧
      NativeHalfPlaneAllCyclicSubgroupsDiscrete H := by
  have ht:=halfPlane_discreteness_elliptic_and_cyclic_criteria_tfae H hH
  have h5 : NativeHalfPlaneEllipticsFiniteOrder H:=fun f hf he=>(hE f hf he).elim
  exact ⟨(ht.out 1 5).mpr h5,(ht.out 2 5).mpr h5,(ht.out 3 5).mpr h5,
    (ht.out 4 5).mpr h5,h5,(ht.out 6 5).mpr h5⟩

end
end LowDimensionalTopology.Geometry.Hyperbolic
