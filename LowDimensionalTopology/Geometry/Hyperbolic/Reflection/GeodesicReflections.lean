/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicAxes
public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The genuine real matrix for either native h-line reflection. -/
def HalfPlaneLine.reflectionMatrix : HalfPlaneLine → GL (Fin 2) ℝ
  | .vertical x => verticalReflectionMatrix x
  | .circle c r hr => circleReflectionMatrix c r hr

theorem HalfPlaneLine.reflectionMatrix_action (L : HalfPlaneLine) (z : ℍ) :
    L.reflectionMatrix • z = L.reflection z := by
  cases L <;> rfl

theorem HalfPlaneLine.reflectionMatrix_det_neg (L : HalfPlaneLine) :
    L.reflectionMatrix.val.det < 0 := by
  cases L with
  | vertical x => rw [HalfPlaneLine.reflectionMatrix,verticalReflectionMatrix_det]; norm_num
  | circle c r hr => rw [HalfPlaneLine.reflectionMatrix,circleReflectionMatrix_det]; nlinarith [sq_pos_of_pos hr]

theorem HalfPlaneLine.reflectionMatrix_trace (L : HalfPlaneLine) :
    Matrix.trace L.reflectionMatrix.val = 0 := by
  cases L <;> simp [HalfPlaneLine.reflectionMatrix,verticalReflectionMatrix,circleReflectionMatrix,Matrix.trace_fin_two]

theorem HalfPlaneLine.reflection_fixed_iff (L : HalfPlaneLine) (z : ℍ) :
    L.reflection z = z ↔ z ∈ L.carrier := by
  rw [← L.mem_extendedCircle,← L.realReflection_fixedPoints]
  change L.reflection z = z ↔ Mobius.euclideanToComplexHom L.realReflection ((z : ℂ) : Mobius.ExtendedComplex) = (z : ℂ)
  rw [L.realReflection_coe,OnePoint.coe_eq_coe]
  exact UpperHalfPlane.ext_iff

theorem HalfPlaneLine.reflection_involutive (L : HalfPlaneLine) : Function.Involutive L.reflection := by
  have hrr : L.realReflection * L.realReflection = 1 := by
    calc
      L.realReflection * L.realReflection = L.realReflection⁻¹ * L.realReflection := by
        rw [L.realReflection_isReflection.inv_eq]
      _ = 1 := inv_mul_cancel _
  have hh : Mobius.euclideanToComplexHom L.realReflection * Mobius.euclideanToComplexHom L.realReflection = 1 := by
    rw [← map_mul,hrr,map_one]
  intro z
  have he := congrArg (fun f : Equiv.Perm Mobius.ExtendedComplex => f ((z : ℂ) : Mobius.ExtendedComplex)) hh
  change Mobius.euclideanToComplexHom L.realReflection
    (Mobius.euclideanToComplexHom L.realReflection ((z : ℂ) : Mobius.ExtendedComplex)) = (z : ℂ) at he
  rw [L.realReflection_coe,L.realReflection_coe] at he
  exact UpperHalfPlane.ext (OnePoint.coe_eq_coe.mp he)

/-- Every negative-determinant trace-zero action is reflection in a genuine h-line. -/
theorem realGL_trace_zero_is_reflection (g : GL (Fin 2) ℝ) (hg : g.val.det < 0)
    (ht : Matrix.trace g.val = 0) : ∃ L : HalfPlaneLine, (g • · : ℍ → ℍ) = L.reflection := by
  have ha : g 0 0 = -g 1 1 := by rw [Matrix.trace_fin_two] at ht; linarith
  by_cases hc : g 1 0 = 0
  · have hd : g 1 1 ≠ 0 := by
      intro hd
      have hdet := g.det_ne_zero
      simp [Matrix.det_fin_two,ha,hc,hd] at hdet
    refine ⟨.vertical (g 0 1 / (2 * g 1 1)),?_⟩
    funext z
    apply UpperHalfPlane.ext
    rw [realGL_coe_of_det_neg g hg]
    simp only [map_div₀,map_add,map_mul,Complex.conj_ofReal]
    change (((g 0 0 : ℂ) * conj (z : ℂ) + (g 0 1 : ℂ)) /
      ((g 1 0 : ℂ) * conj (z : ℂ) + (g 1 1 : ℂ))) = (verticalReflection _ z : ℂ)
    rw [verticalReflection_coe,hc,ha]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hd]
    ring
  · let c := -g 1 1 / g 1 0
    let r := Real.sqrt (-g.val.det) / |g 1 0|
    have hr : 0 < r := div_pos (Real.sqrt_pos.mpr (neg_pos.mpr hg)) (abs_pos.mpr hc)
    have hr2 : r ^ 2 = -g.val.det / (g 1 0) ^ 2 := by
      dsimp only [r]
      rw [div_pow,Real.sq_sqrt (le_of_lt (neg_pos.mpr hg)),sq_abs]
    refine ⟨.circle c r hr,?_⟩
    funext z
    apply UpperHalfPlane.ext
    rw [realGL_coe_of_det_neg g hg]
    simp only [map_div₀,map_add,map_mul,Complex.conj_ofReal]
    change (((g 0 0 : ℂ) * conj (z : ℂ) + (g 0 1 : ℂ)) /
      ((g 1 0 : ℂ) * conj (z : ℂ) + (g 1 1 : ℂ))) = (circleReflection c r hr z : ℂ)
    rw [circleReflection_coe]
    have hd : (g 1 0 : ℂ) * conj (z : ℂ) + (g 1 1 : ℂ) ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.conj_im,Complex.zero_im,zero_mul,add_zero] at hi
      change g 1 0 * -z.im = 0 at hi
      exact hc ((mul_eq_zero.mp hi).resolve_right (neg_ne_zero.mpr z.im_ne_zero))
    have hz : conj (z : ℂ) - (c : ℂ) ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      simp only [Complex.sub_im,Complex.conj_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
      change -z.im = 0 at hi
      exact z.im_ne_zero (neg_eq_zero.mp hi)
    have hrC : (r : ℂ) ^ 2 = (-g.val.det / (g 1 0) ^ 2 : ℝ) := by exact_mod_cast hr2
    rw [hrC]
    dsimp [c]
    rw [Matrix.det_fin_two]
    push_cast
    rw [ha]
    push_cast
    have hcC : (g 1 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
    have hz' : conj (z : ℂ) + (g 1 1 : ℂ) / (g 1 0 : ℂ) ≠ 0 := by
      have he : conj (z : ℂ) + (g 1 1 : ℂ) / (g 1 0 : ℂ) =
          ((g 1 0 : ℂ) * conj (z : ℂ) + (g 1 1 : ℂ)) / (g 1 0 : ℂ) := by
        field_simp
      rw [he]
      exact div_ne_zero hd hcC
    have hdn : (g 1 1 : ℂ) + conj (z : ℂ) * (g 1 0 : ℂ) ≠ 0 := by
      intro he
      apply hd
      calc
        (g 1 0 : ℂ) * conj (z : ℂ) + (g 1 1 : ℂ) =
            (g 1 1 : ℂ) + conj (z : ℂ) * (g 1 0 : ℂ) := by ring
        _ = 0 := he
    field_simp [hcC,hd,hz',hdn]
    ring_nf
    linear_combination -(g 1 1 : ℂ) * (mul_inv_cancel₀ hdn)

/-- Conjugating a genuine reflection by any native real isometry gives the reflection
in its actual image geodesic. Both determinant signs are allowed. -/
theorem HalfPlaneLine.reflection_conjugation_exists (L : HalfPlaneLine) (g : GL (Fin 2) ℝ) :
    ∃ M : HalfPlaneLine, M.carrier = (g • · : ℍ → ℍ) '' L.carrier ∧
      ∀ z : ℍ, g • L.reflection (g⁻¹ • z) = M.reflection z := by
  let C := g * L.reflectionMatrix * g⁻¹
  have hgi : g.val * (g⁻¹).val = 1 := by
    change (g * g⁻¹).val = (1 : GL (Fin 2) ℝ).val
    rw [mul_inv_cancel]
  have hdetgi : g.val.det * (g⁻¹).val.det = 1 := by
    simpa only [Matrix.det_mul,Matrix.det_one] using congrArg Matrix.det hgi
  have hcD : C.val.det < 0 := by
    change Matrix.det (g.val * L.reflectionMatrix.val * (g⁻¹).val) < 0
    rw [Matrix.det_mul,Matrix.det_mul]
    have he : g.val.det * L.reflectionMatrix.val.det * (g⁻¹).val.det = L.reflectionMatrix.val.det := by
      calc
        _ = L.reflectionMatrix.val.det * (g.val.det * (g⁻¹).val.det) := by ring
        _ = L.reflectionMatrix.val.det := by rw [hdetgi,mul_one]
    rw [he]
    exact L.reflectionMatrix_det_neg
  have hcT : Matrix.trace C.val = 0 := by
    change Matrix.trace (g.val * L.reflectionMatrix.val * (g⁻¹).val) = 0
    rw [Matrix.trace_units_conj,L.reflectionMatrix_trace]
  obtain ⟨M,hM⟩ := realGL_trace_zero_is_reflection C hcD hcT
  refine ⟨M,?_,?_⟩
  · ext z
    rw [← M.reflection_fixed_iff,← congrFun hM z]
    constructor
    · intro hz
      refine ⟨g⁻¹ • z,?_,smul_inv_smul g z⟩
      apply (L.reflection_fixed_iff _).mp
      have he := congrArg (fun w : ℍ => g⁻¹ • w) hz
      simpa only [C,mul_smul,inv_smul_smul,L.reflectionMatrix_action] using he
    · rintro ⟨w,hw,rfl⟩
      change C • (g • w) = g • w
      simp only [C,mul_smul,inv_smul_smul,L.reflectionMatrix_action,(L.reflection_fixed_iff w).mpr hw]
  · intro z
    have he := congrFun hM z
    simpa only [C,mul_smul,L.reflectionMatrix_action] using he

/-- A positive-determinant native real action is a product of two genuine line reflections. -/
theorem realGL_pos_two_reflections (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) :
    ∃ L M : HalfPlaneLine, (g • · : ℍ → ℍ) = M.reflection ∘ L.reflection := by
  have hex : ∃ L : HalfPlaneLine, Matrix.trace (g * L.reflectionMatrix).val = 0 := by
    by_cases hc : g 1 0 = 0
    · by_cases ha : g 0 0 = g 1 1
      · refine ⟨.vertical 0, ?_⟩
        simp [HalfPlaneLine.reflectionMatrix,verticalReflectionMatrix,Matrix.trace_fin_two,
          Matrix.mul_apply,Fin.sum_univ_two,ha]
      · refine ⟨.circle (-g 0 1 / (g 0 0 - g 1 1)) 1 (by norm_num), ?_⟩
        change Matrix.trace (g.val * !![-g 0 1/(g 0 0-g 1 1),
          1^2-(-g 0 1/(g 0 0-g 1 1))^2; 1, -(-g 0 1/(g 0 0-g 1 1))]) = 0
        simp only [Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
        change g 0 0 * (-g 0 1 / (g 0 0-g 1 1)) + g 0 1 * 1 +
          (g 1 0 * (1^2-(-g 0 1/(g 0 0-g 1 1))^2) +
            g 1 1 * -(-g 0 1/(g 0 0-g 1 1))) = 0
        rw [hc]
        field_simp [sub_ne_zero.mpr ha]
        ring
    · refine ⟨.vertical ((g 0 0-g 1 1)/(2*g 1 0)), ?_⟩
      change Matrix.trace (g.val * !![-1,2*((g 0 0-g 1 1)/(2*g 1 0));0,1]) = 0
      simp only [Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
      change g 0 0 * -1 + g 0 1 * 0 +
        (g 1 0 * (2*((g 0 0-g 1 1)/(2*g 1 0))) + g 1 1 * 1) = 0
      field_simp [hc]
      ring
  obtain ⟨L,hL⟩ := hex
  have hd : (g*L.reflectionMatrix).val.det < 0 := by
    change Matrix.det (g.val*L.reflectionMatrix.val) < 0
    rw [Matrix.det_mul]
    exact mul_neg_of_pos_of_neg hg L.reflectionMatrix_det_neg
  obtain ⟨M,hM⟩ := realGL_trace_zero_is_reflection (g*L.reflectionMatrix) hd hL
  refine ⟨L,M,?_⟩
  funext z
  have he := congrFun hM (L.reflection z)
  simpa only [mul_smul,L.reflectionMatrix_action,L.reflection_involutive z,Function.comp_apply] using he

/-- The actual determinant-one native action has a two-reflection representation. -/
theorem realSL_two_reflections (f : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ∃ L M : HalfPlaneLine, (f • · : ℍ → ℍ) = M.reflection ∘ L.reflection := by
  apply realGL_pos_two_reflections (Matrix.SpecialLinearGroup.mapGL ℝ f)
  change 0 < f.val.det
  rw [f.det_coe]
  norm_num

end LowDimensionalTopology.Geometry.Hyperbolic
