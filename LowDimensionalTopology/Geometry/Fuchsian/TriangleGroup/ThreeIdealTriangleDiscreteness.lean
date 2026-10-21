/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.OneIdealTriangleDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeInfiniteCounterexample
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane OnePoint MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

def threeIdealStandardTriangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle:=
  prescribedIdealHTriangle 0 0 (by norm_num) (by norm_num) (by linarith [Real.pi_pos])

def threeIdealRightMatrix : Matrix.SpecialLinearGroup (Fin 2) ℤ:=
  ⟨!![2,-1;1,0],by norm_num [Matrix.det_fin_two]⟩

def threeIdealLeftMatrix : Matrix.SpecialLinearGroup (Fin 2) ℤ:=
  ⟨!![-2,-1;1,0],by norm_num [Matrix.det_fin_two]⟩

theorem threeIdealStandardTriangle_angles :
    threeIdealStandardTriangle.alpha=0 ∧ threeIdealStandardTriangle.beta=0 ∧
      threeIdealStandardTriangle.gamma=0 := prescribedIdealHTriangle_angles _ _ _ _ _

theorem threeIdealStandardTriangle_right_matrix :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL threeIdealStandardTriangle.sideLineA threeIdealStandardTriangle.sideLineC=
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) threeIdealRightMatrix := by
  rw [threeIdealStandardTriangle,prescribedIdealHTriangle_sideA,prescribedIdealHTriangle_circle]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflectionMatrix,threeIdealRightMatrix,
      Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,Matrix.map_apply,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem threeIdealStandardTriangle_left_matrix :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL threeIdealStandardTriangle.sideLineB threeIdealStandardTriangle.sideLineC=
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) threeIdealLeftMatrix := by
  rw [threeIdealStandardTriangle,prescribedIdealHTriangle_sideB,prescribedIdealHTriangle_circle]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflectionMatrix,threeIdealLeftMatrix,
      Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,Matrix.map_apply,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem threeIdealStandardTriangle_conformal_le_modular :
    triangleConformalGroup threeIdealStandardTriangle≤modularNativeHom.range := by
  rw [triangleConformalGroup_eq_crossPairProducts,reflectionProductSL_native,
    reflectionProductSL_native,threeIdealStandardTriangle_left_matrix,threeIdealStandardTriangle_right_matrix]
  apply (Subgroup.closure_le _).mpr
  rintro g (rfl|he)
  · exact ⟨threeIdealLeftMatrix,rfl⟩
  · exact mem_singleton_iff.mp he ▸ (show _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (Matrix.SpecialLinearGroup.map
      (Int.castRingHom ℝ) threeIdealRightMatrix)∈modularNativeHom.range from ⟨threeIdealRightMatrix,rfl⟩)

theorem threeIdealStandardTriangle_conformal_discrete :
    DiscreteTopology (triangleConformalGroup threeIdealStandardTriangle) := by
  let : DiscreteTopology modularNativeHom.range:=modularNativeHom_range_discrete
  let F : triangleConformalGroup threeIdealStandardTriangle→modularNativeHom.range:=
    fun f=>⟨f.val,threeIdealStandardTriangle_conformal_le_modular f.property⟩
  have hcont : Continuous F:=continuous_subtype_val.subtype_mk _
  have hinj : Function.Injective F:=by
    intro f g he
    exact Subtype.ext (congrArg (fun z : modularNativeHom.range=>z.val) he)
  exact DiscreteTopology.of_continuous_injective hcont hinj

/-- Every original ideal triangle has a genuinely discrete original conformal group. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_three_ideal
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha : T.alpha=0) (hb : T.beta=0) (hc : T.gamma=0) :
    DiscreteTopology (triangleConformalGroup T) := by
  obtain ⟨e,he⟩:=equal_angle_triangle_conformalGroups_conjugate T threeIdealStandardTriangle
    (ha.trans threeIdealStandardTriangle_angles.1.symm)
    (hb.trans threeIdealStandardTriangle_angles.2.1.symm)
    (hc.trans threeIdealStandardTriangle_angles.2.2.symm)
  let : DiscreteTopology (triangleConformalGroup threeIdealStandardTriangle):=
    threeIdealStandardTriangle_conformal_discrete
  have hd : DiscreteTopology (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e⁻¹ (triangleConformalGroup threeIdealStandardTriangle)):=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete e⁻¹ (triangleConformalGroup threeIdealStandardTriangle)
  rw [←he,native_subgroupConjugate_compose,inv_mul_cancel,native_subgroupConjugate_one] at hd
  exact hd

/-- The same statement for the original full three-mirror group. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.reflection_discrete_of_three_ideal
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha : T.alpha=0) (hb : T.beta=0) (hc : T.gamma=0) :
    DiscreteTopology (triangleReflectionGroup T) :=
  (triangle_discrete_full_iff_conformal T).mpr
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_three_ideal T ha hb hc)

end LowDimensionalTopology.Geometry.Fuchsian
