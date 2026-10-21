/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.MobiusHyperboloid.Orientation
public import LowDimensionalTopology.Geometry.Mobius.ReflectionEquivalence
public import LowDimensionalTopology.Geometry.Mobius.Topology

/-!
# The complex Mobius group and the positive special Lorentz group

Original formalization of the final statement. The target
uses determinant one, as required by the actual orientation correspondence.
The groups carry their native uniform chordal and matrix topologies.
-/

@[expose] public section
noncomputable section
open Set Matrix
open scoped MatrixGroups Topology
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
attribute [local instance] Inversive.pureTranslationBoundaryChordalMetric Inversive.pureTranslationBoundaryMobiusMetric

theorem lorentzSpecialPositive_le_positive (n : ℕ) :
    lorentzSpecialPositiveOrthogonalGroup n≤lorentzPositiveOrthogonalGroup n := by
  intro A hA
  obtain ⟨hO,_,hp⟩:=(mem_lorentzSpecialPositiveOrthogonalGroup A).mp hA
  exact (mem_lorentzPositiveOrthogonalGroup A).mpr ⟨hO,hp⟩

def lorentzSpecialPositiveInclusion (n : ℕ) :
    lorentzSpecialPositiveOrthogonalGroup n →* lorentzPositiveOrthogonalGroup n :=
  Subgroup.inclusion (lorentzSpecialPositive_le_positive n)

def complexMobiusRealEquiv : Mobius.complexMobiusGroup ≃* Inversive.orientationPreservingMobiusGroup 2 :=
  Mobius.complexMobiusEquivFractionalLinear.trans Mobius.mobiusEquivFractionalLinear.symm

def complexMobiusGeneralHom : Mobius.complexMobiusGroup →* Inversive.GM 2 :=
  (Subgroup.inclusion (Inversive.orientationPreservingMobiusGroup_le_general 2)).comp
    complexMobiusRealEquiv.toMonoidHom

theorem complexMobiusGeneralHom_coe (f : Mobius.complexMobiusGroup) :
    (complexMobiusGeneralHom f : Inversive.ExtendedHomeomorph 2)=
      (complexMobiusRealEquiv f : Inversive.ExtendedHomeomorph 2) := rfl

theorem complexMobiusGeneralHom_injective : Function.Injective complexMobiusGeneralHom := by
  intro f g h
  apply complexMobiusRealEquiv.injective
  apply Subtype.ext
  have he:=congrArg (fun q : Inversive.GM 2=>q.val) h
  rw [complexMobiusGeneralHom_coe,complexMobiusGeneralHom_coe] at he
  exact he

theorem complexMobiusGeneralHom_action (f : Mobius.complexMobiusGroup) (z : Mobius.ExtendedComplex) :
    (complexMobiusGeneralHom f : Inversive.ExtendedHomeomorph 2) (Mobius.extendedComplexEuclideanHomeomorph z)=
      Mobius.extendedComplexEuclideanHomeomorph ((f : Equiv.Perm Mobius.ExtendedComplex) z) := by
  have h:=Mobius.mobiusEquivFractionalLinear_action (complexMobiusRealEquiv f) z
  have he : Mobius.mobiusEquivFractionalLinear (complexMobiusRealEquiv f)=
      Mobius.complexMobiusEquivFractionalLinear f := by
    exact Mobius.mobiusEquivFractionalLinear.apply_symm_apply _
  rw [he,Mobius.complexMobiusEquivFractionalLinear_apply] at h
  rw [complexMobiusGeneralHom_coe]
  simpa only [Homeomorph.apply_symm_apply] using (congrArg Mobius.extendedComplexEuclideanHomeomorph h).symm

theorem complexMobiusGeneralHom_isometry : Isometry complexMobiusGeneralHom := by
  apply Isometry.of_dist_eq
  intro f g
  rw [Inversive.mobius_uniform_dist_eq_iSup]
  change (⨆ x, Inversive.chordalDist ((complexMobiusGeneralHom f : Inversive.ExtendedHomeomorph 2) x)
    ((complexMobiusGeneralHom g : Inversive.ExtendedHomeomorph 2) x))=Mobius.mobiusUniformDist f g
  rw [Mobius.mobiusUniformDist_eq_iSup]
  calc
    _ = ⨆ z : Mobius.ExtendedComplex,
        Inversive.chordalDist ((complexMobiusGeneralHom f : Inversive.ExtendedHomeomorph 2)
          (Mobius.extendedComplexEuclideanHomeomorph z))
          ((complexMobiusGeneralHom g : Inversive.ExtendedHomeomorph 2)
            (Mobius.extendedComplexEuclideanHomeomorph z)) :=
      (Mobius.extendedComplexEuclideanHomeomorph.surjective.iSup_comp _).symm
    _ = _ := by
      congr 1
      funext z
      rw [complexMobiusGeneralHom_action,complexMobiusGeneralHom_action]
      rfl

def complexMobiusLorentzGLHom : Mobius.complexMobiusGroup →* GL (Fin 4) ℝ :=
  ((lorentzPositiveOrthogonalGroup 3).subtype.comp
    (mobiusLorentzTopologicalEquiv (n:=2)).toMonoidHom).comp complexMobiusGeneralHom

theorem complexMobiusLorentzGLHom_mem_special (f : Mobius.complexMobiusGroup) :
    complexMobiusLorentzGLHom f∈lorentzSpecialPositiveOrthogonalGroup 3 := by
  apply (cayleyPoincareLorentz_mem_special_iff_preservesOrientation (complexMobiusGeneralHom f)).mpr
  exact (complexMobiusRealEquiv f).property.2

def complexMobiusLorentzHom :
    Mobius.complexMobiusGroup →* lorentzSpecialPositiveOrthogonalGroup 3 :=
  complexMobiusLorentzGLHom.codRestrict (lorentzSpecialPositiveOrthogonalGroup 3)
    complexMobiusLorentzGLHom_mem_special

theorem complexMobiusLorentzHom_coe (f : Mobius.complexMobiusGroup) :
    (complexMobiusLorentzHom f).val=
      (mobiusLorentzTopologicalEquiv (complexMobiusGeneralHom f)).val := rfl

theorem complexMobiusLorentzHom_injective : Function.Injective complexMobiusLorentzHom := by
  intro f g h
  apply complexMobiusGeneralHom_injective
  apply (mobiusLorentzTopologicalEquiv (n:=2)).injective
  apply Subtype.ext
  have he:=congrArg (fun q : lorentzSpecialPositiveOrthogonalGroup 3=>q.val) h
  rw [complexMobiusLorentzHom_coe,complexMobiusLorentzHom_coe] at he
  exact he

theorem complexMobiusLorentzHom_surjective : Function.Surjective complexMobiusLorentzHom := by
  intro A
  let Ap : lorentzPositiveOrthogonalGroup 3:=lorentzSpecialPositiveInclusion 3 A
  let g : Inversive.GM 2:=(mobiusLorentzTopologicalEquiv (n:=2)).symm Ap
  have hg : Inversive.PreservesOrientation (g : Inversive.ExtendedHomeomorph 2) := by
    apply (cayleyPoincareLorentz_mem_special_iff_preservesOrientation g).mp
    change (mobiusLorentzTopologicalEquiv g).val∈lorentzSpecialPositiveOrthogonalGroup 3
    rw [show g=(mobiusLorentzTopologicalEquiv (n:=2)).symm Ap from rfl,
      ContinuousMulEquiv.apply_symm_apply]
    exact A.property
  let d : Inversive.orientationPreservingMobiusGroup 2:=⟨g.val,⟨g.property,hg⟩⟩
  refine ⟨complexMobiusRealEquiv.symm d,Subtype.ext ?_⟩
  change (mobiusLorentzTopologicalEquiv
    (complexMobiusGeneralHom (complexMobiusRealEquiv.symm d))).val=A.val
  have he : complexMobiusGeneralHom (complexMobiusRealEquiv.symm d)=g := by
    apply Subtype.ext
    change (complexMobiusRealEquiv (complexMobiusRealEquiv.symm d)).val=g.val
    rw [MulEquiv.apply_symm_apply]
  rw [he]
  change (mobiusLorentzTopologicalEquiv ((mobiusLorentzTopologicalEquiv (n:=2)).symm Ap)).val=A.val
  rw [ContinuousMulEquiv.apply_symm_apply]
  rfl

def complexMobiusLorentzEquiv : Mobius.complexMobiusGroup ≃* lorentzSpecialPositiveOrthogonalGroup 3 :=
  MulEquiv.ofBijective complexMobiusLorentzHom
    ⟨complexMobiusLorentzHom_injective,complexMobiusLorentzHom_surjective⟩

theorem complexMobiusLorentzEquiv_det (f : Mobius.complexMobiusGroup) :
    (complexMobiusLorentzEquiv f).val.val.det=1 :=
  ((mem_lorentzSpecialPositiveOrthogonalGroup _).mp (complexMobiusLorentzEquiv f).property).2.1

theorem complexMobiusLorentzEquiv_time (f : Mobius.complexMobiusGroup) :
    0<(complexMobiusLorentzEquiv f).val 0 0 :=
  ((mem_lorentzSpecialPositiveOrthogonalGroup _).mp (complexMobiusLorentzEquiv f).property).2.2

theorem lorentzPositive_three_contains_orientation_reverser :
    ∃ A : lorentzPositiveOrthogonalGroup 3,
      A.val∉lorentzSpecialPositiveOrthogonalGroup 3 := by
  let L:=Inversive.cartanPlaneLinearIsometry (Inversive.northPole 2)
  refine ⟨lorentzSpatialGroup L,?_⟩
  rw [lorentzPositive_mem_special_iff_det,lorentzSpatialGroup_det]
  rw [show LinearMap.det L.toLinearMap= -1 from
    Inversive.cartanPlaneLinearIsometry_det (Inversive.northPole 2) (by
      intro h
      have hn:=Inversive.norm_northPole 2
      rw [h,norm_zero] at hn
      norm_num at hn)]
  norm_num

theorem complexMobiusLorentzHom_continuous : Continuous complexMobiusLorentzHom := by
  apply Continuous.subtype_mk
  change Continuous (fun f : Mobius.complexMobiusGroup=>
    (mobiusLorentzTopologicalEquiv (complexMobiusGeneralHom f)).val)
  exact continuous_subtype_val.comp
    ((mobiusLorentzTopologicalEquiv (n:=2)).continuous.comp complexMobiusGeneralHom_isometry.continuous)

theorem complexMobiusLorentzEquiv_symm_continuous : Continuous complexMobiusLorentzEquiv.symm := by
  apply complexMobiusGeneralHom_isometry.comp_continuous_iff.mp
  have he : complexMobiusGeneralHom ∘ complexMobiusLorentzEquiv.symm=
      (mobiusLorentzTopologicalEquiv (n:=2)).symm ∘ lorentzSpecialPositiveInclusion 3 := by
    funext A
    apply (mobiusLorentzTopologicalEquiv (n:=2)).injective
    change mobiusLorentzTopologicalEquiv
      (complexMobiusGeneralHom (complexMobiusLorentzEquiv.symm A))=
      mobiusLorentzTopologicalEquiv ((mobiusLorentzTopologicalEquiv (n:=2)).symm
        (lorentzSpecialPositiveInclusion 3 A))
    rw [ContinuousMulEquiv.apply_symm_apply]
    apply Subtype.ext
    have h:=congrArg (fun q : lorentzSpecialPositiveOrthogonalGroup 3=>q.val)
      (complexMobiusLorentzEquiv.apply_symm_apply A)
    change (mobiusLorentzTopologicalEquiv
      (complexMobiusGeneralHom (complexMobiusLorentzEquiv.symm A))).val=A.val at h
    exact h
  rw [he]
  have hinc : Continuous (lorentzSpecialPositiveInclusion 3) := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  exact (mobiusLorentzTopologicalEquiv (n:=2)).symm.continuous.comp hinc

def complexMobiusLorentzTopologicalEquiv :
    Mobius.complexMobiusGroup ≃ₜ* lorentzSpecialPositiveOrthogonalGroup 3 where
  toMulEquiv:=complexMobiusLorentzEquiv
  continuous_toFun:=complexMobiusLorentzHom_continuous
  continuous_invFun:=complexMobiusLorentzEquiv_symm_continuous

theorem complexMobiusLorentzEquiv_source_quadratic (f : Mobius.complexMobiusGroup)
    (x : LorentzVector 3) :
    ‖(lorentzRowLinearMap (complexMobiusLorentzEquiv f).val.val x).2‖^2-
      (lorentzRowLinearMap (complexMobiusLorentzEquiv f).val.val x).1^2=
      ‖x.2‖^2-x.1^2 := by
  have hO:=((mem_lorentzSpecialPositiveOrthogonalGroup _).mp
    (complexMobiusLorentzEquiv f).property).1
  have h:=lorentzOrthogonal_preserves_form hO x x
  rw [lorentzForm_self,lorentzForm_self] at h
  linarith

end LowDimensionalTopology.Geometry.Hyperbolic
