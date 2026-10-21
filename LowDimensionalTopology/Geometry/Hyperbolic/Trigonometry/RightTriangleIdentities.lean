/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleSineRules

@[expose] public section
open Set
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem HTriangle.right_sine_identities (T : HTriangle) (hγ : T.gamma = Real.pi / 2) :
    Real.sinh T.lengthA = Real.sinh T.lengthC * Real.sin T.alpha ∧
      Real.sinh T.lengthB = Real.sinh T.lengthC * Real.sin T.beta := by
  have hα := Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.1.1 T.angles_mem_Ioo.1.2
  have hβ := Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.2.1.1 T.angles_mem_Ioo.2.1.2
  have ha := T.sine_rule.1.trans T.sine_rule.2
  have hb := T.sine_rule.2
  rw [hγ,Real.sin_pi_div_two,div_one] at ha hb
  exact ⟨(div_eq_iff (ne_of_gt hα)).mp ha,(div_eq_iff (ne_of_gt hβ)).mp hb⟩

theorem HTriangle.right_cosine_identities (T : HTriangle) (hγ : T.gamma = Real.pi / 2) :
    Real.cosh T.lengthA * Real.sin T.beta = Real.cos T.alpha ∧
      Real.cosh T.lengthB * Real.sin T.alpha = Real.cos T.beta := by
  have hα := Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.1.1 T.angles_mem_Ioo.1.2
  have hβ := Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.2.1.1 T.angles_mem_Ioo.2.1.2
  have ha := hyperbolic_second_cosine_rule T.lengths_pos.2.1 T.lengths_pos.2.2 T.lengths_pos.1
    T.angles_mem_Ioo.2.1 T.angles_mem_Ioo.2.2 T.cosine_rule_B T.cosine_rule_I T.cosine_rule_A
  have hb := hyperbolic_second_cosine_rule T.lengths_pos.2.2 T.lengths_pos.1 T.lengths_pos.2.1
    T.angles_mem_Ioo.2.2 T.angles_mem_Ioo.1 T.cosine_rule_I T.cosine_rule_A T.cosine_rule_B
  rw [hγ,Real.sin_pi_div_two,Real.cos_pi_div_two,mul_zero,zero_add,mul_one] at ha
  rw [hγ,Real.sin_pi_div_two,Real.cos_pi_div_two,zero_mul,zero_add,one_mul] at hb
  exact ⟨(eq_div_iff (ne_of_gt hβ)).mp ha,(eq_div_iff (ne_of_gt hα)).mp hb⟩

/-- All three relations for the actual right triangle. -/
theorem HTriangle.rightTriangle_sinh_tanh_side_angle_identities (T : HTriangle) (hγ : T.gamma = Real.pi / 2) :
    Real.tanh T.lengthB = Real.sinh T.lengthA * Real.tan T.beta ∧
      Real.sinh T.lengthB = Real.sinh T.lengthC * Real.sin T.beta ∧
        Real.tanh T.lengthA = Real.tanh T.lengthC * Real.cos T.beta := by
  obtain ⟨hsa,hsb⟩ := T.right_sine_identities hγ
  obtain ⟨_,hcb⟩ := T.right_cosine_identities hγ
  have hsinα := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.1.1 T.angles_mem_Ioo.1.2)
  have hca := ne_of_gt (Real.cosh_pos T.lengthA)
  have hcb' := ne_of_gt (Real.cosh_pos T.lengthB)
  refine ⟨?_,hsb,?_⟩
  · rw [Real.tanh_eq_sinh_div_cosh,Real.tan_eq_sin_div_cos,← hcb,hsa,hsb]
    field_simp
  · rw [Real.tanh_eq_sinh_div_cosh,Real.tanh_eq_sinh_div_cosh,← hcb,hsa,T.cosh_hypotenuse_eq_cosh_mul_cosh hγ]
    field_simp

/-- both identities with two actual angles. -/
theorem HTriangle.rightTriangle_cosh_sine_cotangent_angle_identities (T : HTriangle) (hγ : T.gamma = Real.pi / 2) :
    Real.cosh T.lengthA * Real.sin T.beta = Real.cos T.alpha ∧
      Real.cosh T.lengthC = Real.cot T.alpha * Real.cot T.beta := by
  refine ⟨(T.right_cosine_identities hγ).1,?_⟩
  have h := T.cosine_rule_II
  rw [hγ,Real.cos_pi_div_two,add_zero] at h
  rw [h,Real.cot_eq_cos_div_sin,Real.cot_eq_cos_div_sin]
  ring

theorem DiscTriangle.rightTriangle_sinh_tanh_side_angle_identities (T : DiscTriangle) (hγ : T.gamma = Real.pi / 2) :
    Real.tanh T.lengthB = Real.sinh T.lengthA * Real.tan T.beta ∧
      Real.sinh T.lengthB = Real.sinh T.lengthC * Real.sin T.beta ∧
        Real.tanh T.lengthA = Real.tanh T.lengthC * Real.cos T.beta := by
  rw [T.lengths_eq_halfPlane.1,T.lengths_eq_halfPlane.2.1,T.lengths_eq_halfPlane.2.2,
    T.angles_eq_halfPlane.2.1]
  exact T.toHalfPlane.rightTriangle_sinh_tanh_side_angle_identities ((T.angles_eq_halfPlane.2.2.symm).trans hγ)

theorem DiscTriangle.rightTriangle_cosh_sine_cotangent_angle_identities (T : DiscTriangle) (hγ : T.gamma = Real.pi /
  2) :
    Real.cosh T.lengthA * Real.sin T.beta = Real.cos T.alpha ∧
      Real.cosh T.lengthC = Real.cot T.alpha * Real.cot T.beta := by
  rw [T.lengths_eq_halfPlane.1,T.lengths_eq_halfPlane.2.2,
    T.angles_eq_halfPlane.1,T.angles_eq_halfPlane.2.1]
  exact T.toHalfPlane.rightTriangle_cosh_sine_cotangent_angle_identities ((T.angles_eq_halfPlane.2.2.symm).trans hγ)

end
end LowDimensionalTopology.Geometry.Hyperbolic
