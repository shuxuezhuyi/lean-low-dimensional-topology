/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleRationalCounterexample
public import LowDimensionalTopology.Geometry.Fuchsian.Modular.ModularDirichlet
public import Mathlib.Data.ZMod.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint
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

/-- The genuine right triangle with two ideal vertices. -/
def infiniteHeckeTriangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle :=
  prescribedIdealHTriangle (Real.pi/2) 0 (by positivity) (by norm_num)
    (by linarith only [Real.pi_pos])

theorem infiniteHeckeTriangle_angles :
    infiniteHeckeTriangle.alpha=Real.pi/2 ∧ infiniteHeckeTriangle.beta=0 ∧
      infiniteHeckeTriangle.gamma=0 :=
  prescribedIdealHTriangle_angles _ _ _ _ _

theorem infiniteHeckeTriangle_first_matrix :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL infiniteHeckeTriangle.sideLineA infiniteHeckeTriangle.sideLineB=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 2 := by
  rw [infiniteHeckeTriangle,prescribedIdealHTriangle_sideA,prescribedIdealHTriangle_sideB,
    Real.cos_pi_div_two,Real.cos_zero,neg_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.mul_apply,Fin.sum_univ_two]

theorem infiniteHeckeTriangle_second_matrix :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL infiniteHeckeTriangle.sideLineC infiniteHeckeTriangle.sideLineB=
      -modularInversionSL := by
  rw [infiniteHeckeTriangle,prescribedIdealHTriangle_circle,prescribedIdealHTriangle_sideB,
    Real.cos_pi_div_two,neg_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflectionMatrix,modularInversionSL,
      Matrix.SpecialLinearGroup.coe_neg,Matrix.mul_apply,Fin.sum_univ_two]

theorem modularNativeHom_S_eq : modularNativeHom ModularGroup.S=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL := by
  apply congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ModularGroup.S,modularInversionSL,Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply,Matrix.map_apply]

theorem modularNativeHom_T_sq_eq :
    modularNativeHom (ModularGroup.T^2)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 2) := by
  apply congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ModularGroup.T,pow_two,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.mul_apply,Fin.sum_univ_two]

theorem infiniteHeckeTriangle_group :
    triangleConformalGroup infiniteHeckeTriangle=
      Subgroup.closure ({modularNativeHom (ModularGroup.T^2),modularNativeHom ModularGroup.S}:
        Set (ℍ≃ᵢℍ)) := by
  rw [triangleConformalGroup_eq_pairProductGroup]
  change Subgroup.closure _=Subgroup.closure _
  rw [reflectionProductSL_native,reflectionProductSL_native,
    infiniteHeckeTriangle_first_matrix,infiniteHeckeTriangle_second_matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_neg,
    modularNativeHom_S_eq,modularNativeHom_T_sq_eq]

theorem infiniteHeckeTriangle_isHeckeGroup :
    IsHeckeGroup (triangleConformalGroup infiniteHeckeTriangle) := by
  refine ⟨⊤,le_top,by norm_num,by simp,by simp,?_⟩
  have htwo : triangleOrderAngle 2=Real.pi/2 := by norm_num [triangleOrderAngle]
  rw [htwo,triangleOrderAngle_top]
  exact ⟨infiniteHeckeTriangle,infiniteHeckeTriangle_angles.1,
    infiniteHeckeTriangle_angles.2.1,infiniteHeckeTriangle_angles.2.2,rfl⟩

/-- Reduction modulo two and the genuine linear action define the parity obstruction. -/
def heckeParitySubgroup : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
  (MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (![1,1] : Fin 2→ZMod 2)).comap
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2)))

theorem heckeParity_S : ModularGroup.S∈heckeParitySubgroup := by
  change (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2)) ModularGroup.S) •
    (![1,1] : Fin 2→ZMod 2)=![1,1]
  ext i
  fin_cases i <;>
    norm_num [Matrix.SpecialLinearGroup.smul_def,ModularGroup.S,
      Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,Matrix.map_apply,
      Matrix.mulVec,Fin.sum_univ_two,Matrix.vecHead,Matrix.vecTail]
  all_goals decide

theorem heckeParity_T_sq : ModularGroup.T^2∈heckeParitySubgroup := by
  change (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2)) (ModularGroup.T^2)) •
    (![1,1] : Fin 2→ZMod 2)=![1,1]
  ext i
  fin_cases i <;>
    norm_num [Matrix.SpecialLinearGroup.smul_def,ModularGroup.T,pow_two,
      Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,Matrix.map_apply,
      Matrix.mul_apply,Matrix.mulVec,Fin.sum_univ_two,Matrix.vecHead,Matrix.vecTail]
  all_goals decide

theorem heckeParity_T_not_mem : ModularGroup.T∉heckeParitySubgroup := by
  intro h
  have he:=congrFun h 0
  norm_num [Matrix.SpecialLinearGroup.smul_def,ModularGroup.T,heckeParitySubgroup,
    Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,Matrix.map_apply,
    Matrix.mulVec,Fin.sum_univ_two,Matrix.vecHead,Matrix.vecTail] at he
  exact (by decide : (2:ZMod 2)≠1) he

theorem heckeParity_neg_T_not_mem : -ModularGroup.T∉heckeParitySubgroup := by
  intro h
  have he:=congrFun h 0
  norm_num [Matrix.SpecialLinearGroup.smul_def,ModularGroup.T,heckeParitySubgroup,
    Matrix.SpecialLinearGroup.coe_neg,Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.mulVec,Fin.sum_univ_two,
    Matrix.vecHead,Matrix.vecTail] at he
  exact (by decide : (2:ZMod 2)≠1) he

/-- The native projective action has exactly its two genuine scalar lifts. -/
theorem modularNativeHom_eq_iff (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    modularNativeHom A=modularNativeHom B ↔ A=B ∨ A= -B := by
  constructor
  · intro h
    have hk : modularNativeHom (A*B⁻¹)=1 := by rw [map_mul,map_inv,h,mul_inv_cancel]
    have he : A*B⁻¹=1 ∨ A*B⁻¹= -1 := by
      by_contra hn
      push Not at hn
      exact (modularNativeHom_ne_one_iff _).mpr hn hk
    rcases he with he|he
    · left
      have hm:=congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) ℤ=>C*B) he
      simpa only [mul_assoc,inv_mul_cancel,mul_one,one_mul] using hm
    · right
      have hm:=congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) ℤ=>C*B) he
      simpa only [mul_assoc,inv_mul_cancel,mul_one,neg_mul,one_mul] using hm
  · rintro (rfl|rfl)
    · rfl
    · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry _
      have hm : Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (-B)=
          -(Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) B) := by
        ext i j
        simp only [Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,
          Matrix.map_apply,Matrix.SpecialLinearGroup.coe_neg,Matrix.neg_apply,map_neg]
      rw [hm,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_neg]

theorem infiniteHeckeTriangle_translation_not_mem :
    modularNativeHom ModularGroup.T∉triangleConformalGroup infiniteHeckeTriangle := by
  have hle : triangleConformalGroup infiniteHeckeTriangle≤heckeParitySubgroup.map modularNativeHom := by
    rw [infiniteHeckeTriangle_group]
    apply (Subgroup.closure_le _).mpr
    rintro f (rfl|hf)
    · exact ⟨_,heckeParity_T_sq,rfl⟩
    · exact mem_singleton_iff.mp hf ▸ ⟨_,heckeParity_S,rfl⟩
  intro h
  obtain ⟨A,hA,he⟩:=hle h
  rcases (modularNativeHom_eq_iff A ModularGroup.T).mp he with rfl|rfl
  · exact heckeParity_T_not_mem hA
  · exact heckeParity_neg_T_not_mem hA

theorem infiniteHeckeTriangle_lt_modular :
    triangleConformalGroup infiniteHeckeTriangle<modularNativeHom.range := by
  apply lt_of_le_of_ne
  · rw [infiniteHeckeTriangle_group]
    apply (Subgroup.closure_le _).mpr
    rintro f (rfl|hf)
    · exact ⟨_,rfl⟩
    · exact mem_singleton_iff.mp hf ▸ ⟨_,rfl⟩
  · intro he
    apply infiniteHeckeTriangle_translation_not_mem
    rw [he]
    exact ⟨_,rfl⟩

theorem modularNativeHom_range_conformal :
    modularNativeHom.range≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  rintro f ⟨A,rfl⟩
  exact ⟨Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A,rfl⟩

theorem modularNativeHom_range_discrete : DiscreteTopology modularNativeHom.range := by
  apply native_conformal_subgroup_discrete_of_image modularNativeHom.range
    modularNativeHom_range_conformal _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup_discrete
  intro f
  obtain ⟨A,hA⟩:=f.property
  have hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A)∈
      modularNativeHom.range := ⟨A,rfl⟩
  have he : f=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A),hmem⟩ :=
    Subtype.ext hA.symm
  rw [he,nativeConformalSubgroupMobiusHom_matrix]
  rw [←integralHalfPlaneMobiusHom_range]
  exact ⟨A,rfl⟩

theorem infiniteHeckeTriangle_discrete :
    DiscreteTopology (triangleConformalGroup infiniteHeckeTriangle) := by
  let : DiscreteTopology modularNativeHom.range:=modularNativeHom_range_discrete
  let F : triangleConformalGroup infiniteHeckeTriangle→modularNativeHom.range :=
    fun f=>⟨f.val,infiniteHeckeTriangle_lt_modular.le f.property⟩
  have hcont : Continuous F:=continuous_subtype_val.subtype_mk _
  have hinj : Function.Injective F:=by
    intro f g he
    exact Subtype.ext (congrArg (fun z : modularNativeHom.range=>z.val) he)
  exact DiscreteTopology.of_continuous_injective hcont hinj

/--
The infinite-order case in the source definition gives a genuine counterexample
to the unrestricted maximality statement.
-/
theorem hecke_maximality_fails_at_infinite_order :
    ∃G₀ G : Subgroup (ℍ≃ᵢℍ), IsHeckeGroup G₀ ∧ DiscreteTopology G₀ ∧
      G≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup ∧ DiscreteTopology G ∧ G₀<G :=
  ⟨triangleConformalGroup infiniteHeckeTriangle,modularNativeHom.range,
    infiniteHeckeTriangle_isHeckeGroup,infiniteHeckeTriangle_discrete,
    modularNativeHom_range_conformal,modularNativeHom_range_discrete,
    infiniteHeckeTriangle_lt_modular⟩

end LowDimensionalTopology.Geometry.Fuchsian
