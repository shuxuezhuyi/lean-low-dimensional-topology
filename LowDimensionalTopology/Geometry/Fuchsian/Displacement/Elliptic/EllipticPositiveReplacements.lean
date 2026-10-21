/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticPrimitiveRotationGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.NonEllipticMaximumDisplacement
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.CollinearHalfTurns
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfPlaneDisk
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HorocyclicRegions
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveEllipticAngles
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.EllipticProducts
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.AngleParallelism
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.AngularMeasure
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticCenterMinimum
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.CommutatorGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticPairReflectionGroups
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleAngleSum
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticRotationAngles
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.MobiusTriangleGroups
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleSupergroups
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticPairSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticTriangleDisplacementSharpness
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleIntegralDiscreteness
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticMinimizers
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set InnerProductGeometry
open scoped UpperHalfPlane MatrixGroups OnePoint Pointwise ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem elliptic_realSL_inverse (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹) := by
  have hi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹ ≠ 1 := by rw [map_inv]; exact inv_ne_one.mpr hA.1
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A⁻¹ hi).mpr
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_inverse]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA

theorem elliptic_realSL_inverse_center (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hi : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A⁻¹ ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A⁻¹ hi.1).mp hi) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) := by
  let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  have hv : A • v = v := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ v).mpr rfl
  have hiv : A⁻¹ • v = v := by rw [inv_smul_eq_iff]; exact hv.symm
  exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A⁻¹ _ v).mp hiv).symm

theorem elliptic_realSL_inverse_angle (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hi : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A⁻¹ hi = 2*Real.pi-_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA := by
  let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  let θ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA
  let φ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A⁻¹ hi
  have hv : A • v = v := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ v).mpr rfl
  have hd := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hasDerivAt A
    v).unique (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A hA).2.1
  have hdi := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hasDerivAt A⁻¹ v).unique (by
    simpa only [elliptic_realSL_inverse_center A hA hi] using
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A⁻¹ hi).2.1)
  have hc := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLDenom_mul A⁻¹ A v
  rw [inv_mul_cancel, hv] at hc
  have hc' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLDenom A⁻¹ v * _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLDenom A v = 1 := by
    simpa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLDenom] using hc.symm
  have hp : Complex.exp (Complex.I*(φ:ℂ)) * Complex.exp (Complex.I*(θ:ℂ)) = 1 := by
    rw [←hd, ←hdi]
    rw [div_mul_div_comm, ←mul_pow, hc']
    norm_num
  have he : Complex.exp (Complex.I*(φ:ℂ)) =
      Complex.exp (Complex.I*((2*Real.pi-θ:ℝ):ℂ)) := by
    have he' : Complex.exp (Complex.I*(φ:ℂ)) = (Complex.exp (Complex.I*(θ:ℂ)))⁻¹ :=
      eq_inv_of_mul_eq_one_left hp
    rw [he']
    rw [show Complex.I*((2*Real.pi-θ:ℝ):ℂ) =
      2*Real.pi*Complex.I + -(Complex.I*(θ:ℂ)) by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul, Complex.exp_neg]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.rotation_exp_injective_Ico (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A⁻¹ hi).1 _ he
  have hθ := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A hA).1
  have hpos := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_pos A hA
  constructor <;> dsimp only [θ] <;> linarith only [hθ.2, hpos]

theorem least_elliptic_positive_orientation
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hleast : HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ, (B=A ∨ B=A⁻¹) ∧
      ∃ hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B),
        HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) ∧
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) =
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ∧
        orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          B) = orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∧
        Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          B) = Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∧
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB = 2*Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) := by
  rcases least_elliptic_actual_angle A hA hleast with hpos | hneg
  · exact ⟨A, Or.inl rfl, hA, hleast, rfl, rfl, rfl, hpos⟩
  · have hi := elliptic_realSL_inverse A hA
    have hc : IsConj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹) :=
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_isConj_iff_squaredTrace_eq _ _ hA.1 hi.1).mpr (by
        rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_inverse])
    have hleastI := (hasLeastEllipticRotation_isConj hc).mp hleast
    refine ⟨A⁻¹, Or.inr rfl, hi, hleastI, elliptic_realSL_inverse_center A hA hi, ?_, ?_, ?_⟩
    · rw [map_inv, orderOf_inv]
    · rw [map_inv, Subgroup.zpowers_inv]
    · rw [elliptic_realSL_inverse_angle A hA hi, hneg, map_inv, orderOf_inv]
      ring

def PositiveNativeEllipticReplacement (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) : Prop :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H ∧ HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB = 2*Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ∧
    Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) =
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H
        (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)) : ℂ) :
          _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) ∧
    orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A) ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)

theorem HalfPlaneFuchsianGroup.elliptic_exists_native_positive_replacement
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B),
      PositiveNativeEllipticReplacement H A hA B hB := by
  obtain ⟨C, hC, hCH, hleast, hcenter, hstab⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_exists_native_least_generator P A hA hAH
  obtain ⟨B, hBC, hB, hleastB, hcenterB, _horderB, hcyclicB, hangleB⟩ :=
    least_elliptic_positive_orientation C hC hleast
  have hBH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H := by
    rcases hBC with rfl | rfl
    · exact hCH
    · rw [map_inv]
      exact H.inv_mem hCH
  have hstabB := hcyclicB.trans hstab
  have hpower : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) := by
    rw [hstabB]
    apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H _ _).mpr
    refine ⟨hAH, ?_⟩
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ _).mpr rfl]
  have hn := least_elliptic_realSL_order_two_le B hB hleastB
  have hord : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    A) ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) :=
    Nat.le_of_dvd (by omega) (orderOf_dvd_of_mem_zpowers hpower)
  exact ⟨B, hB, hBH, hleastB, hangleB, hcenterB.trans hcenter, hstabB, hpower, hord⟩

theorem HalfPlaneFuchsianGroup.elliptic_pair_native_positive_replacements
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A E : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hE :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E))
    (hgen : Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E} = H) :
    ∃ B F : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∃ hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B), ∃ hF : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F),
        PositiveNativeEllipticReplacement H A hA B hB ∧
        PositiveNativeEllipticReplacement H E hE F hF ∧
        Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F} = H := by
  have hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H := hgen ▸ Subgroup.subset_closure (by simp)
  have hEH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E ∈ H := hgen ▸ Subgroup.subset_closure (by simp)
  obtain ⟨B, hB, hAB⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_exists_native_positive_replacement P A hA hAH
  obtain ⟨F, hF, hEF⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_exists_native_positive_replacement P E hE hEH
  refine ⟨B, F, hB, hF, hAB, hEF, le_antisymm ?_ ?_⟩
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hAB.1
    · exact hEF.1
  · rw [←hgen]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) hAB.2.2.2.2.2.1
    · exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) hEF.2.2.2.2.2.1

end LowDimensionalTopology.Geometry.Fuchsian
