/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.TwoParabolicTraceClassification
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeMaximality
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TwoIdealTriangleDiscreteness
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

def twoParabolicNativeGroup (c : ℝ) : Subgroup (ℍ≃ᵢℍ) :=
  Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (twoParabolicModelSL c)} : Set (ℍ≃ᵢℍ))

theorem twoParabolicNativeGroup_conformal (c : ℝ) :
    twoParabolicNativeGroup c≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  apply (Subgroup.closure_le _).mpr
  rintro f (rfl|rfl)
  · exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1,rfl⟩
  · exact ⟨twoParabolicModelSL c,rfl⟩

theorem native_matrix_pair_mobius_image (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hH : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B} : Set (ℍ≃ᵢℍ))≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) :
    (nativeConformalSubgroupMobiusHom (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B} : Set (ℍ≃ᵢℍ))) hH).range=
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup) := by
  let H := Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B} : Set (ℍ≃ᵢℍ))
  let F := nativeConformalSubgroupMobiusHom H hH
  let J := Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)
  have hall : ∀g (hg : g∈H),F ⟨g,hg⟩∈J := by
    intro g hg
    change g∈Subgroup.closure _ at hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl|rfl
      · rw [nativeConformalSubgroupMobiusHom_matrix]
        exact Subgroup.subset_closure (by simp)
      · rw [nativeConformalSubgroupMobiusHom_matrix]
        exact Subgroup.subset_closure (by simp)
    | one =>
      change F 1∈J
      rw [map_one]
      exact J.one_mem
    | mul x y hx hy ihx ihy =>
      change F (⟨x,hx⟩*⟨y,hy⟩)∈J
      rw [map_mul]
      exact J.mul_mem ihx ihy
    | inv x hx ih =>
      change F (⟨x,hx⟩⁻¹)∈J
      rw [map_inv]
      exact J.inv_mem ih
  apply le_antisymm
  · rintro f ⟨g,rfl⟩
    exact hall g.val g.property
  · apply (Subgroup.closure_le _).mpr
    rintro f (rfl|rfl)
    · exact ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,Subgroup.subset_closure (by simp)⟩,
        nativeConformalSubgroupMobiusHom_matrix H hH A _⟩
    · exact ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B,Subgroup.subset_closure (by simp)⟩,
        nativeConformalSubgroupMobiusHom_matrix H hH B _⟩

theorem twoParabolicNativeGroup_mobius_image (c : ℝ) :
    (nativeConformalSubgroupMobiusHom (twoParabolicNativeGroup c)
      (twoParabolicNativeGroup_conformal c)).range=twoParabolicCanonicalGroup c :=
  native_matrix_pair_mobius_image _ _ _

theorem closure_pair_replace_left_quotient {G : Type*} [Group G] (a b : G) :
    Subgroup.closure ({a,b} : Set G)=Subgroup.closure ({b*a⁻¹,b} : Set G) := by
  let H := Subgroup.closure ({a,b} : Set G)
  let K := Subgroup.closure ({b*a⁻¹,b} : Set G)
  have ha : a∈H := Subgroup.subset_closure (by simp)
  have hb : b∈H := Subgroup.subset_closure (by simp)
  have hk : b*a⁻¹∈K := Subgroup.subset_closure (by simp)
  have hbK : b∈K := Subgroup.subset_closure (by simp)
  change H=K
  apply le_antisymm
  · apply (Subgroup.closure_le K).mpr
    intro f hf
    simp only [mem_insert_iff,mem_singleton_iff] at hf
    rcases hf with hfa|hfb
    · rw [hfa]
      have he : (b*a⁻¹)⁻¹*b∈K := K.mul_mem (K.inv_mem hk) hbK
      have hid : (b*a⁻¹)⁻¹*b=a := by group
      rwa [hid] at he
    · rw [hfb]
      exact hbK
  · apply (Subgroup.closure_le H).mpr
    intro f hf
    simp only [mem_insert_iff,mem_singleton_iff] at hf
    rcases hf with hfa|hfb
    · rw [hfa]
      exact H.mul_mem hb (H.inv_mem ha)
    · rw [hfb]
      exact hb

def twoIdealParabolicCoefficient (p : ℕ) : ℝ := 2+2*Real.cos (Real.pi/(p:ℝ))

theorem twoIdealParabolicCoefficient_pos (p : ℕ) (hp : 2≤p) :
    0<twoIdealParabolicCoefficient p := by
  have hs := twoIdealHeckeParameter_sq p hp
  have hp0 := twoIdealHeckeParameter_pos p hp
  change 0<2+2*Real.cos (Real.pi/(p:ℝ))
  nlinarith [hs,hp0]

theorem twoIdeal_cross_quotient_translation (p : ℕ) :
    twoIdealRightSL*(twoIdealLeftSL p)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (twoIdealParabolicCoefficient p) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoIdealRightSL,twoIdealLeftSL,twoIdealParabolicCoefficient,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,
      modularInversionSL,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
  ring

theorem twoIdeal_right_centering :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)*twoIdealRightSL*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1))⁻¹=twoParabolicModelSL 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoIdealRightSL,twoParabolicModelSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]

def twoIdealParabolicNormalizer (p : ℕ) (hp : 2≤p) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (1/twoIdealParabolicCoefficient p)
    (one_div_pos.mpr (twoIdealParabolicCoefficient_pos p hp))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)

theorem twoIdealParabolicNormalizer_translation (p : ℕ) (hp : 2≤p) :
    twoIdealParabolicNormalizer p hp*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (twoIdealParabolicCoefficient p)*
      (twoIdealParabolicNormalizer p hp)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1 := by
  let D := _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (1/twoIdealParabolicCoefficient p)
    (one_div_pos.mpr (twoIdealParabolicCoefficient_pos p hp))
  have he : (D*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (twoIdealParabolicCoefficient p)*
      (D*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1))⁻¹=
      D*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (twoIdealParabolicCoefficient p)*
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1))⁻¹)*D⁻¹ := by group
  change (D*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1))*_*(D*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1))⁻¹=_
  rw [he,hTranslationSL_conjugate_translation,verticalDilationSL_conjugate_translation_matrix]
  congr 1
  exact one_div_mul_cancel (twoIdealParabolicCoefficient_pos p hp).ne'

theorem twoIdealParabolicNormalizer_right (p : ℕ) (hp : 2≤p) :
    twoIdealParabolicNormalizer p hp*twoIdealRightSL*(twoIdealParabolicNormalizer p hp)⁻¹=
      twoParabolicModelSL (twoIdealParabolicCoefficient p) := by
  let D := _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (1/twoIdealParabolicCoefficient p)
    (one_div_pos.mpr (twoIdealParabolicCoefficient_pos p hp))
  have he : (D*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1))*twoIdealRightSL*(D*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1))⁻¹=
      D*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)*twoIdealRightSL*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1))⁻¹)*D⁻¹ := by group
  change (D*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1))*_*(D*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1))⁻¹=_
  rw [he,twoIdeal_right_centering,verticalDilationSL_conjugate_twoParabolicModel]
  congr 1
  field_simp

theorem twoIdeal_conformal_group_two_parabolics (p : ℕ) (hp : 2≤p) :
    triangleConformalGroup (twoIdealIntegralTriangle p hp)=Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (twoIdealParabolicCoefficient p)),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry twoIdealRightSL} : Set (ℍ≃ᵢℍ)) := by
  rw [triangleConformalGroup_eq_crossPairProducts,reflectionProductSL_native,
    reflectionProductSL_native,twoIdealIntegralTriangle_left_product,twoIdealIntegralTriangle_right_product,
    closure_pair_replace_left_quotient]
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry twoIdealRightSL*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (twoIdealLeftSL p))⁻¹=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (twoIdealParabolicCoefficient p)) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _)⁻¹=_
    rw [←map_inv,←map_mul,twoIdeal_cross_quotient_translation]
    rfl
  rw [he]

theorem twoIdeal_native_group_normalization (p : ℕ) (hp : 2≤p) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (twoIdealParabolicNormalizer p hp))
      (triangleConformalGroup (twoIdealIntegralTriangle p hp))=
      twoParabolicNativeGroup (twoIdealParabolicCoefficient p) := by
  rw [twoIdeal_conformal_group_two_parabolics,native_subgroupConjugate_closure]
  have ht : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (twoIdealParabolicNormalizer p hp)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (twoIdealParabolicCoefficient p))*
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (twoIdealParabolicNormalizer p hp))⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _*
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _)⁻¹=_
    rw [←map_inv,←map_mul,←map_mul,twoIdealParabolicNormalizer_translation]
    rfl
  have hx : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (twoIdealParabolicNormalizer p hp)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry twoIdealRightSL*
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (twoIdealParabolicNormalizer p hp))⁻¹=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (twoParabolicModelSL (twoIdealParabolicCoefficient p)) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _*
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _)⁻¹=_
    rw [←map_inv,←map_mul,←map_mul,twoIdealParabolicNormalizer_right]
    rfl
  simp only [image_insert_eq,image_singleton,ht,hx,twoParabolicNativeGroup]

theorem twoIdeal_mobius_group_normalization (p : ℕ) (hp : 2≤p) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoIdealParabolicNormalizer p hp))
      (nativeConformalSubgroupMobiusHom (triangleConformalGroup (twoIdealIntegralTriangle p hp))
        inf_le_right).range=twoParabolicCanonicalGroup (twoIdealParabolicCoefficient p) := by
  have h := nativeConformal_range_conjugate_eq (triangleConformalGroup (twoIdealIntegralTriangle p hp))
    (twoParabolicNativeGroup (twoIdealParabolicCoefficient p)) inf_le_right
    (twoParabolicNativeGroup_conformal _) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (twoIdealParabolicNormalizer p hp))
    ⟨twoIdealParabolicNormalizer p hp,rfl⟩ (twoIdeal_native_group_normalization p hp)
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (halfPlaneConformalMobiusHom
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalElement (twoIdealParabolicNormalizer p hp))) _=_ at h
  rw [halfPlaneConformalMobiusHom_matrix,twoParabolicNativeGroup_mobius_image] at h
  exact h

end LowDimensionalTopology.Geometry.Fuchsian
