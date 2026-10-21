/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HyperbolicReflectionPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.GeodesicInversiveProducts
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticRotationAngles
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set InnerProductGeometry
open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The positive normalization scale of the literal real reflection matrix. -/
def HalfPlaneLine.reflectionScale : HalfPlaneLine → ℝ
  | .vertical _ => 1
  | .circle _ r _ => r

theorem HalfPlaneLine.reflectionScale_pos (L : HalfPlaneLine) : 0<L.reflectionScale := by
  cases L with
  | vertical _ => exact zero_lt_one
  | circle _ _ hr => exact hr

theorem HalfPlaneLine.reflectionMatrix_det_scale (L : HalfPlaneLine) :
    L.reflectionMatrix.val.det= -(L.reflectionScale^2) := by
  cases L with
  | vertical x => simpa [HalfPlaneLine.reflectionMatrix,
    HalfPlaneLine.reflectionScale] using verticalReflectionMatrix_det x
  | circle c r hr => exact circleReflectionMatrix_det c r hr

/-- An actual determinant-one lift of the product of two genuine h-line reflections. -/
def reflectionProductSL (L M : HalfPlaneLine) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨(1/(L.reflectionScale*M.reflectionScale)) • (L.reflectionMatrix.val*M.reflectionMatrix.val), by
    rw [Matrix.det_smul,Matrix.det_mul,L.reflectionMatrix_det_scale,M.reflectionMatrix_det_scale]
    simp only [Fintype.card_fin]
    field_simp [(L.reflectionScale_pos).ne',(M.reflectionScale_pos).ne']⟩

theorem reflectionProductSL_coe (L M : HalfPlaneLine) :
    (reflectionProductSL L M).val=
      (1/(L.reflectionScale*M.reflectionScale)) • (L.reflectionMatrix.val*M.reflectionMatrix.val) := rfl

/-- The normalized lift acts by the original two reflections on every native point. -/
theorem reflectionProductSL_action (L M : HalfPlaneLine) (z : ℍ) :
    reflectionProductSL L M • z=L.reflection (M.reflection z) := by
  let u : ℝˣ := Units.mk0 (1/(L.reflectionScale*M.reflectionScale)) (by
    exact one_div_ne_zero (mul_ne_zero (L.reflectionScale_pos).ne' (M.reflectionScale_pos).ne'))
  have he : Matrix.SpecialLinearGroup.mapGL ℝ (reflectionProductSL L M)=
      Matrix.GeneralLinearGroup.scalar (Fin 2) u*(L.reflectionMatrix*M.reflectionMatrix) := by
    apply Units.ext
    change (reflectionProductSL L M).val=Matrix.scalar (Fin 2) u.val*
      (L.reflectionMatrix.val*M.reflectionMatrix.val)
    rw [reflectionProductSL_coe]
    have hs : Matrix.scalar (Fin 2) u.val=u.val • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j
      by_cases h : i=j <;> simp [Matrix.scalar,h]
    rw [hs,smul_mul_assoc,Matrix.one_mul]
    rfl
  change Matrix.SpecialLinearGroup.mapGL ℝ (reflectionProductSL L M) • z= _
  rw [he,mul_smul,UpperHalfPlane.glScalar_smul,mul_smul,
    L.reflectionMatrix_action,M.reflectionMatrix_action]

/-- The signed normalized matrix trace is the genuine Lorentz pairing of line normals. -/
theorem reflectionProductSL_trace_pairing (L M : HalfPlaneLine) :
    Matrix.trace (reflectionProductSL L M).val/2=
      inner ℝ L.incenterNormal M.incenterNormal-L.incenterOffset*M.incenterOffset := by
  rw [reflectionProductSL_coe,Matrix.trace_smul]
  cases L <;> cases M
  all_goals
    simp only [HalfPlaneLine.reflectionScale,HalfPlaneLine.reflectionMatrix,
      verticalReflectionMatrix,circleReflectionMatrix,Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      smul_eq_mul,Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      HalfPlaneLine.incenterNormal, HalfPlaneLine.incenterOffset,
        _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    field_simp
    ring

/-- For the actual determinant-one product lift. -/
theorem reflectionProductSL_abs_trace (L M : HalfPlaneLine) :
    Inversive.inversiveProduct L.extendedCircle.realModel M.extendedCircle.realModel=
      |Matrix.trace (reflectionProductSL L M).val|/2 := by
  rw [halfPlane_inversiveProduct_eq_normal_product,← reflectionProductSL_trace_pairing,
    abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]

/-- The actual Mobius absolute trace agrees with every real determinant-one lift. -/
theorem realSLMobius_traceAbs (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Mobius.mobiusTraceAbs (realSLMobius A)=|Matrix.trace A.val| := by
  rw [Mobius.mobiusTraceAbs,realSLMobius_squaredTrace,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _),Real.sqrt_sq_eq_abs]

/-- The geometric trace formula is independent of the lift chosen for the reflection product. -/
theorem reflection_product_abs_trace (L M : HalfPlaneLine)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : ∀ z : ℍ, A • z=L.reflection (M.reflection z)) :
    Inversive.inversiveProduct L.extendedCircle.realModel M.extendedCircle.realModel=|Matrix.trace A.val|/2 := by
  have he : realSLMobius A=realSLMobius (reflectionProductSL L M) :=
    realSLMobius_eq_of_native_action A (reflectionProductSL L M) (fun z=> (hA z).trans (reflectionProductSL_action L M
      z).symm)
  rw [← realSLMobius_traceAbs A,he,realSLMobius_traceAbs]
  exact reflectionProductSL_abs_trace L M

/-- The source formula directly in the original actual geometric Mobius group. -/
theorem reflection_product_actual_trace (L M : HalfPlaneLine) :
    Inversive.inversiveProduct L.extendedCircle.realModel M.extendedCircle.realModel=
      Mobius.mobiusTraceAbs (realSLMobius (reflectionProductSL L M))/2 := by
  rw [realSLMobius_traceAbs]
  exact reflectionProductSL_abs_trace L M

/-- A common genuine reflection factor cancels in the original actual group. -/
theorem reflection_product_common_factor (L M N : HalfPlaneLine) :
    realSLMobius (reflectionProductSL L M)*realSLMobius (reflectionProductSL M N)=
      realSLMobius (reflectionProductSL L N) := by
  rw [← map_mul]
  apply realSLMobius_eq_of_native_action
  intro z
  rw [mul_smul,reflectionProductSL_action,reflectionProductSL_action,
    M.reflection_involutive,reflectionProductSL_action]

/-- The associated source pencil, specified by actual centers, ideal fixed points or axis orthogonality. -/
def hAssociatedPencil (f : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Set HalfPlaneLine :=
  {L | (∃ hf : Mobius.MobiusElliptic (realSLMobius f),
      hEllipticCenter f ((realSLMobius_elliptic_iff f hf.1).mp hf) ∈ L.carrier) ∨
    (∃ hf : Mobius.MobiusParabolic (realSLMobius f), hParabolicIdealPoint f hf ∈ L.idealEndpoints) ∨
    (∃ (hf : realSLMobius f≠1) (ht : 4<(Matrix.trace f.val)^2),
      L.Orthogonal (hHyperbolicAxis f hf ht))}

/-- Every member of the actual associated pencil can be prescribed as the second factor. -/
theorem hAssociatedPencil_factor (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (L : HalfPlaneLine) (hL : L ∈ hAssociatedPencil f) :
    ∃ M : HalfPlaneLine, (f • · : ℍ → ℍ)=M.reflection ∘ L.reflection := by
  rcases hL with ⟨hf,hL⟩ | ⟨hf,hL⟩ | ⟨hf,ht,hL⟩
  · obtain ⟨M,hM,_⟩ := realSL_elliptic_reflection_factor f hf L hL
    exact ⟨M,hM.2⟩
  · exact realSL_parabolic_reflection_factor f hf L hL
  · obtain ⟨M,hM,_⟩ := realSL_hyperbolic_reflection_factor f hf ht L hL
    exact ⟨M,hM.2⟩

/-- Every member of the same geometric pencil can instead be prescribed as the first factor. -/
theorem hAssociatedPencil_factor_right (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (L : HalfPlaneLine) (hL : L ∈ hAssociatedPencil f) :
    ∃ M : HalfPlaneLine, (f • · : ℍ → ℍ)=L.reflection ∘ M.reflection := by
  rcases hL with ⟨hf,hL⟩ | ⟨hf,hL⟩ | ⟨hf,ht,hL⟩
  · obtain ⟨M,hM,_⟩ := realSL_elliptic_reflection_factor_right f hf L hL
    exact ⟨M,hM.2⟩
  · obtain ⟨M,hM,_⟩ := realSL_parabolic_reflection_factor_right f hf L hL
    exact ⟨M,hM.2.2⟩
  · obtain ⟨M,hM,_⟩ := realSL_hyperbolic_reflection_factor_right f hf ht L hL
    exact ⟨M,hM.2⟩

/-- The source common-pencil reduction includes genuine factors and the trace of the actual product. -/
theorem common_associated_pencil_product (f g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (L : HalfPlaneLine) (hf : L ∈ hAssociatedPencil f) (hg : L ∈ hAssociatedPencil g) :
    ∃ M N : HalfPlaneLine, (f • · : ℍ → ℍ)=M.reflection ∘ L.reflection ∧
      (g • · : ℍ → ℍ)=L.reflection ∘ N.reflection ∧
      ((f*g) • · : ℍ → ℍ)=M.reflection ∘ N.reflection ∧
      realSLMobius f*realSLMobius g=realSLMobius (reflectionProductSL M N) ∧
      Mobius.mobiusTraceAbs (realSLMobius f*realSLMobius g)/2=
        Inversive.inversiveProduct M.extendedCircle.realModel N.extendedCircle.realModel := by
  obtain ⟨M,hM⟩ := hAssociatedPencil_factor f L hf
  obtain ⟨N,hN⟩ := hAssociatedPencil_factor_right g L hg
  have he : ((f*g) • · : ℍ → ℍ)=M.reflection ∘ N.reflection := by
    funext z
    rw [mul_smul,congrFun hM,congrFun hN]
    change M.reflection (L.reflection (L.reflection (N.reflection z)))= _
    rw [L.reflection_involutive]
    rfl
  have hproj : realSLMobius f*realSLMobius g=realSLMobius (reflectionProductSL M N) := by
    rw [← map_mul]
    apply realSLMobius_eq_of_native_action
    intro z
    rw [congrFun he,reflectionProductSL_action]
    rfl
  refine ⟨M,N,hM,hN,he,hproj,?_⟩
  rw [hproj]
  exact (reflection_product_actual_trace M N).symm

end LowDimensionalTopology.Geometry.Hyperbolic
