/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckePingPongGroups
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem native_subgroupConjugate_discrete (e : ℍ≃ᵢℍ) (G : Subgroup (ℍ≃ᵢℍ))
    [DiscreteTopology G] : DiscreteTopology (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e G) :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete e G

theorem standardHeckeGroup_infinite_discrete :
    DiscreteTopology (standardHeckeGroup ⊤ (by simp)) := by
  have ht : standardHeckeTriangle ⊤ (by simp)=infiniteHeckeTriangle:=by
    unfold standardHeckeTriangle infiniteHeckeTriangle
    simp only [triangleOrderAngle_top]
  change DiscreteTopology (triangleConformalGroup _)
  rw [ht]
  exact infiniteHeckeTriangle_discrete

theorem standardHeckeGroup_discrete (q : ℕ∞) (hq : 3≤q) :
    DiscreteTopology (standardHeckeGroup q hq) := by
  induction q using ENat.recTopCoe with
  | top => exact standardHeckeGroup_infinite_discrete
  | coe n => exact standardHeckeGroup_finite_discrete n (by exact_mod_cast hq)

theorem unitHeckeGroup_discrete (q : ℕ∞) (hq : 3≤q) :
    DiscreteTopology (unitHeckeGroup q hq) := by
  let : DiscreteTopology (standardHeckeGroup q hq):=standardHeckeGroup_discrete q hq
  exact native_subgroupConjugate_discrete _ _

theorem IsHeckeGroup.discrete {G : Subgroup (ℍ≃ᵢℍ)} (hG : IsHeckeGroup G) :
    DiscreteTopology G := by
  obtain ⟨q,hq,e,_heconf,he⟩:=hG.conformal_conjugate_standard
  let : DiscreteTopology (standardHeckeGroup q hq):=standardHeckeGroup_discrete q hq
  have hd :=native_subgroupConjugate_discrete e⁻¹ (standardHeckeGroup q hq)
  rw [←he,native_subgroupConjugate_compose,inv_mul_cancel,native_subgroupConjugate_one] at hd
  exact hd


theorem nativeConformalSubgroup_halfPlaneData (H : Subgroup (ℍ≃ᵢℍ))
    (hH : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) [DiscreteTopology H] :
    HalfPlaneFuchsianGroup (nativeConformalSubgroupMobiusHom H hH).range where
  preserves g:=by
    obtain ⟨f,hf⟩:=g.property
    obtain ⟨A,hA⟩:=hH f.property
    have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A∈H:=by
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom A∈H
      rw [hA]
      exact f.property
    have he : f=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,hm⟩:=Subtype.ext hA.symm
    change g.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    rw [←hf,he,nativeConformalSubgroupMobiusHom_matrix]
    exact realSLMobius_image_openHalfPlane A
  discrete:=native_conformal_subgroup_image_discrete H hH

theorem standardHeckeGroup_le_conformal (q : ℕ∞) (hq : 3≤q) :
    standardHeckeGroup q hq≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := inf_le_right

theorem unitHeckeGroup_le_conformal (q : ℕ∞) (hq : 3≤q) :
    unitHeckeGroup q hq≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  intro f hf
  obtain ⟨g,hg,hgf⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL q hq)) (standardHeckeGroup q hq) f).mp hf
  rw [←hgf]
  exact native_conjugate_conformal_mem _ _ (standardHeckeGroup_le_conformal q hq hg)

def standardHeckeMobiusGroup
    (q : ℕ∞)
    (hq : 3≤q) : Subgroup Mobius.complexMobiusGroup :=
  (nativeConformalSubgroupMobiusHom (standardHeckeGroup q hq) (standardHeckeGroup_le_conformal q hq)).range

def unitHeckeMobiusGroup
    (q : ℕ∞)
    (hq : 3≤q) : Subgroup Mobius.complexMobiusGroup :=
  (nativeConformalSubgroupMobiusHom (unitHeckeGroup q hq) (unitHeckeGroup_le_conformal q hq)).range

theorem standardHeckeMobiusData (q : ℕ∞) (hq : 3≤q) :
    HalfPlaneFuchsianGroup (standardHeckeMobiusGroup q hq) := by
  let : DiscreteTopology (standardHeckeGroup q hq):=standardHeckeGroup_discrete q hq
  exact nativeConformalSubgroup_halfPlaneData _ _

theorem unitHeckeMobiusData (q : ℕ∞) (hq : 3≤q) :
    HalfPlaneFuchsianGroup (unitHeckeMobiusGroup q hq) := by
  let : DiscreteTopology (unitHeckeGroup q hq):=unitHeckeGroup_discrete q hq
  exact nativeConformalSubgroup_halfPlaneData _ _

theorem nativeConformalSubgroupMobiusGroup_matrix_mem (H : Subgroup (ℍ≃ᵢℍ))
    (hH : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A∈H) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈(nativeConformalSubgroupMobiusHom H hH).range :=
  ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,hA⟩,nativeConformalSubgroupMobiusHom_matrix H hH A hA⟩

theorem standardHeckeMobiusGroup_translation_mem (q : ℕ∞) (hq : 3≤q) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (triangleOrderAngle q)))∈standardHeckeMobiusGroup q hq := by
  apply nativeConformalSubgroupMobiusGroup_matrix_mem
  rw [standardHeckeGroup_generators]
  exact Subgroup.subset_closure (by simp)

theorem standardHeckeMobiusGroup_inversion_mem (q : ℕ∞) (hq : 3≤q) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius modularInversionSL∈standardHeckeMobiusGroup q hq := by
  apply nativeConformalSubgroupMobiusGroup_matrix_mem
  rw [standardHeckeGroup_generators]
  exact Subgroup.subset_closure (by simp)

theorem standardHeckeMobiusGroup_product_mem (n : ℕ) (hn : 3≤n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (standardHeckeCornerSL n)∈standardHeckeMobiusGroup n (by exact_mod_cast hn) := by
  unfold standardHeckeCornerSL
  rw [map_mul]
  exact (standardHeckeMobiusGroup n (by exact_mod_cast hn)).mul_mem
    (by simpa only [triangleOrderAngle_nat] using standardHeckeMobiusGroup_translation_mem n (by exact_mod_cast hn))
    (standardHeckeMobiusGroup_inversion_mem n (by exact_mod_cast hn))


theorem realSLMobius_order_eq_native (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) := by
  let f : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,⟨A,rfl⟩⟩
  have h1:=orderOf_injective halfPlaneConformalMobiusHom
    halfPlaneConformalMobiusHom_isometry.injective f
  have h2:=orderOf_injective _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup.subtype Subtype.val_injective f
  have he : halfPlaneConformalMobiusHom f=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A:=by
    change halfPlaneConformalMobiusHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalElement A)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A
    exact halfPlaneConformalMobiusHom_matrix A
  rw [he] at h1
  exact h1.trans h2.symm

theorem standardHeckeMobiusProduct_order (n : ℕ) (hn : 3≤n) :
    orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (standardHeckeCornerSL n))=n := by
  rw [realSLMobius_order_eq_native]
  exact standardHeckeCornerSL_order n hn

end LowDimensionalTopology.Geometry.Fuchsian
