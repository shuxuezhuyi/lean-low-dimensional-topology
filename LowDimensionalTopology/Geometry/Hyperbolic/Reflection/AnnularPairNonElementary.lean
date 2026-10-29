module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularDiscGroup
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.PureHyperbolicSharpness
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.HyperbolicProducts

@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The original ordered annular reflection pair is non-elementary in its actual Cayley group. -/
theorem annularPairReflectionDiscGroup_nonElementary (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hin : 1 + r < x) :
    DiscreteGroups.IsNonElementary
      (annularPairReflectionDiscGroup E r x (zero_lt_one.trans hE) hr) := by
  have hE0 : 0 < E := zero_lt_one.trans hE
  have hx : 0 < x := by linarith
  let C0 := HalfPlaneLine.circle 0 1 zero_lt_one
  let CE := HalfPlaneLine.circle 0 E hE0
  let Cs := HalfPlaneLine.circle x r hr
  let A0 := reflectionProductSL C0 CE
  let A1 := reflectionProductSL Cs C0
  have ha0 : A0.val = !![E⁻¹, 0; 0, E] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A0, C0, CE, reflectionProductSL, HalfPlaneLine.reflectionScale,
        HalfPlaneLine.reflectionMatrix, circleReflectionMatrix,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals field_simp [hE0.ne']
  have ha1 : A1.val = (1 / r) • !![r ^ 2 - x ^ 2, x; -x, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A1, Cs, C0, reflectionProductSL, HalfPlaneLine.reflectionScale,
        HalfPlaneLine.reflectionMatrix, circleReflectionMatrix,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]
  have ht0 : 4 < (Matrix.trace A0.val) ^ 2 := by
    rw [ha0, Matrix.trace_fin_two]
    change 4 < (E⁻¹ + E) ^ 2
    have ht : 2 < E⁻¹ + E := by
      apply (mul_lt_mul_iff_left₀ hE0).mp
      rw [add_mul, inv_mul_cancel₀ hE0.ne']
      nlinarith [sq_pos_of_pos (sub_pos.mpr hE)]
    nlinarith
  have ht1 : 4 < (Matrix.trace A1.val) ^ 2 := by
    have ht : Matrix.trace A1.val < -2 := by
      rw [ha1, Matrix.trace_smul, Matrix.trace_fin_two]
      change (1 / r) * (r ^ 2 - x ^ 2 + 1) < -2
      rw [one_div_mul_eq_div]
      apply (div_lt_iff₀ hr).mpr
      nlinarith [(sq_lt_sq₀ (by linarith : 0 ≤ 1 + r) hx.le).mpr hin]
    nlinarith
  have hyp0 := (realSLMobius_hyperbolic_iff A0
    (Fuchsian.realSLMobius_ne_one_of_trace_sq_gt_four A0 ht0)).mpr ht0
  have hyp1 := (realSLMobius_hyperbolic_iff A1
    (Fuchsian.realSLMobius_ne_one_of_trace_sq_gt_four A1 ht1)).mpr ht1
  have hb0 : A0 0 1 = 0 := congrArg (fun M => M 0 1) ha0
  have hc0 : A0 1 0 = 0 := congrArg (fun M => M 1 0) ha0
  have hb1 : A1 0 1 ≠ 0 := by
    rw [ha1]
    exact mul_ne_zero (one_div_ne_zero hr.ne') hx.ne'
  have hc1 : A1 1 0 ≠ 0 := by
    rw [ha1]
    exact mul_ne_zero (one_div_ne_zero hr.ne') (neg_ne_zero.mpr hx.ne')
  have hf0 : (realSLMobius A0).val (0 : ℂ) = (0 : ℂ) := by
    rw [realSLMobius, MonoidHom.comp_apply, Mobius.invariantDisc_specialLinear_action,
      Mobius.Classification.fractionalLinear_fixed_coe_iff]
    change (A0 1 0 : ℂ) * (0 * 0) + ((A0 1 1 : ℂ) - A0 0 0) * 0 + -(A0 0 1 : ℂ) = 0
    simp [hb0]
  have hfi : (realSLMobius A0).val ∞ = ∞ :=
    (realSLMobius_fixed_infty_iff A0).mpr hc0
  have hn0 : (realSLMobius A1).val (0 : ℂ) ≠ (0 : ℂ) := by
    intro hf
    exact hb1 (by simpa using hSL_fixed_real_polynomial A1 0 hf)
  have hni : (realSLMobius A1).val ∞ ≠ ∞ :=
    fun hf => hc1 ((realSLMobius_fixed_infty_iff A1).mp hf)
  have hpair : DiscreteGroups.IsNonElementary
      (Subgroup.closure ({realSLMobius A0, realSLMobius A1} : Set _)) := by
    apply Fuchsian.loxodromic_pair_nonElementary_of_no_common_fixed _ _ hyp0.1 hyp1.1
    rintro ⟨p, hp0, hp1⟩
    rcases (Mobius.mobius_boundary_fixed_iff_zero_infty _ hyp0.1.1 hf0 hfi p).mp hp0 with
      rfl | rfl
    · exact hn0 hp1
    · exact hni hp1
  let K := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
  let hK := annularPairReflectionGroup_le_conformal E r x (zero_lt_one.trans hE) hr
  let F := Fuchsian.nativeConformalSubgroupMobiusHom K hK
  have hnA0 : hSLIsometry A0 ∈ K := by
    change hSLIsometry (reflectionProductSL C0 CE) ∈ K
    rw [← Fuchsian.reflectionProductSL_native]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hnA1 : hSLIsometry A1 ∈ K := by
    change hSLIsometry (reflectionProductSL Cs C0) ∈ K
    rw [← Fuchsian.reflectionProductSL_native]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hm0 : realSLMobius A0 ∈ F.range :=
    ⟨⟨hSLIsometry A0, hnA0⟩, Fuchsian.nativeConformalSubgroupMobiusHom_matrix K hK A0 hnA0⟩
  have hm1 : realSLMobius A1 ∈ F.range :=
    ⟨⟨hSLIsometry A1, hnA1⟩, Fuchsian.nativeConformalSubgroupMobiusHom_matrix K hK A1 hnA1⟩
  have hle : Subgroup.closure ({realSLMobius A0, realSLMobius A1} : Set _) ≤ F.range := by
    apply (Subgroup.closure_le _).mpr
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl <;> assumption
  have hNE : DiscreteGroups.IsNonElementary F.range := fun he => hpair (he.mono hle)
  change DiscreteGroups.IsNonElementary (F.range.map (MulAut.conj cayleyMobius).toMonoidHom)
  exact hNE.conjugation cayleyMobius

end LowDimensionalTopology.Geometry.Hyperbolic
