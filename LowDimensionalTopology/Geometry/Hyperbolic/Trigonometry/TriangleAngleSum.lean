/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleCongruence
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.OneIdealTriangleTrigonometry
@[expose] public section
open Set
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- Positivity of the sine of the sum of two actual finite triangle angles. -/
theorem HTriangle.sin_alpha_add_beta_pos (T : HTriangle) :
    0 < Real.sin (T.alpha + T.beta) := by
  have hα := T.angles_mem_Ioo.1
  have hsina := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  have hsa := Real.sinh_pos_iff.mpr T.lengths_pos.1
  have hsc := Real.sinh_pos_iff.mpr T.lengths_pos.2.2
  have hcc := Real.one_lt_cosh.mpr (ne_of_gt T.lengths_pos.2.2)
  have hcross := hyperbolic_sine_cross_eq T.lengths_pos.1 T.lengths_pos.2.1 T.lengths_pos.2.2
    T.angles_mem_Ioo.1 T.angles_mem_Ioo.2.1 T.cosine_rule_A T.cosine_rule_B
  have hA : Real.sinh T.lengthB * Real.sinh T.lengthC * Real.cos T.alpha =
      Real.cosh T.lengthB * Real.cosh T.lengthC - Real.cosh T.lengthA := by
    linarith only [T.cosine_rule_A]
  have hB : Real.sinh T.lengthA * Real.sinh T.lengthC * Real.cos T.beta =
      Real.cosh T.lengthA * Real.cosh T.lengthC - Real.cosh T.lengthB := by
    nlinarith only [T.cosine_rule_B]
  have he : (Real.sinh T.lengthA * Real.sinh T.lengthC) * Real.sin (T.alpha+T.beta) =
      Real.sin T.alpha * (Real.cosh T.lengthC-1) * (Real.cosh T.lengthA+Real.cosh T.lengthB) := by
    calc
      _ = Real.sin T.alpha * (Real.sinh T.lengthA * Real.sinh T.lengthC * Real.cos T.beta) +
          (Real.sinh T.lengthA * Real.sin T.beta) * (Real.sinh T.lengthC * Real.cos T.alpha) := by
        rw [Real.sin_add]
        ring
      _ = Real.sin T.alpha * (Real.sinh T.lengthA * Real.sinh T.lengthC * Real.cos T.beta) +
          Real.sin T.alpha * (Real.sinh T.lengthB * Real.sinh T.lengthC * Real.cos T.alpha) := by
        rw [hcross]
        ring
      _ = _ := by rw [hA,hB]; ring
  have hp : 0 < (Real.sinh T.lengthA * Real.sinh T.lengthC) * Real.sin (T.alpha+T.beta) := by
    rw [he]
    exact mul_pos (mul_pos hsina (sub_pos.mpr hcc)) (add_pos (Real.cosh_pos _) (Real.cosh_pos _))
  exact (mul_pos_iff_of_pos_left (mul_pos hsa hsc)).mp hp

theorem HTriangle.alpha_add_beta_lt_pi (T : HTriangle) : T.alpha + T.beta < Real.pi := by
  by_contra! he
  have ha := T.angles_mem_Ioo.1
  have hb := T.angles_mem_Ioo.2.1
  have hn := Real.sin_nonpos_of_nonpos_of_neg_pi_le
    (show T.alpha+T.beta-2*Real.pi ≤ 0 by linarith [ha.2,hb.2])
    (show -Real.pi ≤ T.alpha+T.beta-2*Real.pi by linarith)
  rw [Real.sin_sub_two_pi] at hn
  exact (not_le_of_gt T.sin_alpha_add_beta_pos) hn

/-- The angle-sum corollary, in actual finite H geometry. -/
theorem HTriangle.angle_sum_lt_pi (T : HTriangle) : T.alpha + T.beta + T.gamma < Real.pi := by
  have hα := T.angles_mem_Ioo.1
  have hβ := T.angles_mem_Ioo.2.1
  have hγ := T.angles_mem_Ioo.2.2
  have hsina := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  have hsinb := Real.sin_pos_of_pos_of_lt_pi hβ.1 hβ.2
  have hcc := Real.one_lt_cosh.mpr (ne_of_gt T.lengths_pos.2.2)
  have he := (eq_div_iff (ne_of_gt (mul_pos hsina hsinb))).mp T.cosine_rule_II
  have hc : Real.cos (Real.pi-(T.alpha+T.beta)) < Real.cos T.gamma := by
    rw [Real.cos_pi_sub,Real.cos_add]
    nlinarith only [he,mul_pos (sub_pos.mpr hcc) (mul_pos hsina hsinb)]
  have hm : T.gamma < Real.pi-(T.alpha+T.beta) := by
    by_contra! h
    have hle := Real.cos_le_cos_of_nonneg_of_le_pi
      (sub_pos.mpr T.alpha_add_beta_lt_pi).le hγ.2.le h
    exact (not_le_of_gt hc) hle
  linarith

theorem DiscTriangle.angle_sum_lt_pi (T : DiscTriangle) : T.alpha + T.beta + T.gamma < Real.pi := by
  rw [T.angles_eq_halfPlane.1,T.angles_eq_halfPlane.2.1,T.angles_eq_halfPlane.2.2]
  exact T.toHalfPlane.angle_sum_lt_pi

/-- The actual finite triangle recovered when all three closed-model vertices are interior. -/
def ClosedDiscTriangle.finiteTriangle (T : ClosedDiscTriangle)
    (ha : ‖(T.a : ℂ)‖ < 1) (hb : ‖(T.b : ℂ)‖ < 1) (hc : ‖(T.c : ℂ)‖ < 1) : DiscTriangle where
  a := closedDiscFinitePoint T.a ha
  b := closedDiscFinitePoint T.b hb
  c := closedDiscFinitePoint T.c hc
  noncollinear := by
    rintro ⟨L,hA,hB,hC⟩
    apply T.noncollinear
    refine ⟨L,?_,?_,?_⟩
    · rw [← closedDiscFinitePoint_spec T.a ha]
      exact (L.closedCarrier_mem_interior_iff _).mpr hA
    · rw [← closedDiscFinitePoint_spec T.b hb]
      exact (L.closedCarrier_mem_interior_iff _).mpr hB
    · rw [← closedDiscFinitePoint_spec T.c hc]
      exact (L.closedCarrier_mem_interior_iff _).mpr hC

theorem ClosedDiscTriangle.finiteTriangle_toClosedDiscTriangle (T : ClosedDiscTriangle)
    (ha : ‖(T.a : ℂ)‖ < 1) (hb : ‖(T.b : ℂ)‖ < 1) (hc : ‖(T.c : ℂ)‖ < 1) :
    (T.finiteTriangle ha hb hc).toClosedDiscTriangle = T := by
  cases T
  rfl

theorem ClosedDiscTriangle.alpha_mem_Ico (T : ClosedDiscTriangle) : T.alpha ∈ Ico (0:ℝ) Real.pi := by
  by_cases ha : ‖(T.a : ℂ)‖ < 1
  · have h := T.alpha_bounds_of_finite (closedDiscFinitePoint T.a ha)
      (closedDiscFinitePoint_spec T.a ha).symm
    exact ⟨h.1.le,h.2⟩
  · rw [T.alpha_of_ideal (le_antisymm T.a.norm_le_one (not_lt.mp ha))]
    exact ⟨le_rfl,Real.pi_pos⟩

theorem ClosedDiscTriangle.angle_sum_lt_pi_of_one_ideal (T : ClosedDiscTriangle)
    (hα : T.alpha ≠ 0) (hβ : T.beta ≠ 0) (hγ : T.gamma = 0) :
    T.alpha+T.beta+T.gamma < Real.pi := by
  have hαb := T.alpha_mem_Ico
  have hβb : T.beta ∈ Ico (0:ℝ) Real.pi := T.cycle.alpha_mem_Ico
  have hαp : 0 < T.alpha := lt_of_le_of_ne hαb.1 hα.symm
  have hβp : 0 < T.beta := lt_of_le_of_ne hβb.1 hβ.symm
  have hsa := Real.sin_pos_of_pos_of_lt_pi hαp hαb.2
  have hsb := Real.sin_pos_of_pos_of_lt_pi hβp hβb.2
  have ha : ‖(T.a : ℂ)‖ < 1 := by
    by_contra! he
    exact hα (T.alpha_of_ideal (le_antisymm T.a.norm_le_one he))
  have hb : ‖(T.b : ℂ)‖ < 1 := by
    by_contra! he
    exact hβ (T.beta_of_ideal (le_antisymm T.b.norm_le_one he))
  let a := closedDiscFinitePoint T.a ha
  let b := closedDiscFinitePoint T.b hb
  have hab : a ≠ b := by
    intro he
    apply T.a_ne_b
    rw [← closedDiscFinitePoint_spec T.a ha,← closedDiscFinitePoint_spec T.b hb]
    exact congrArg discToClosedModel he
  have hlen : T.lengthC.toReal = dist (discToHalfPlane a) (discToHalfPlane b) := by
    rw [ClosedDiscTriangle.lengthC,← closedDiscFinitePoint_spec T.a ha,
      ← closedDiscFinitePoint_spec T.b hb,extendedDiscSideLength_finite,
      ENNReal.toReal_ofReal (by rw [discPathDist_eq_halfPlane]; exact dist_nonneg),
      discPathDist_eq_halfPlane]
  have hsp : 0 < Real.sinh T.lengthC.toReal := by
    rw [hlen]
    exact Real.sinh_pos_iff.mpr (dist_pos.mpr (cayleyHomeomorph.symm.injective.ne hab))
  have he := (eq_div_iff (ne_of_gt (mul_pos hsa hsb))).mp (T.one_ideal_vertex_cosh_sinh_finite_side_formulas hα hβ hγ).2
  have hp : 0 < Real.cos T.alpha + Real.cos T.beta := by
    rw [← he]
    exact mul_pos hsp (mul_pos hsa hsb)
  have hcos : Real.cos (Real.pi-T.beta) < Real.cos T.alpha := by
    rw [Real.cos_pi_sub]
    linarith only [hp]
  have hm : T.alpha < Real.pi-T.beta := by
    by_contra! h
    have hn := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hβb.2]) hαb.2.le h
    exact (not_le_of_gt hcos) hn
  linarith only [hm,hγ]

/-- The angle-sum corollary includes every actual finite-or-ideal native triangle. -/
theorem ClosedDiscTriangle.angle_sum_lt_pi (T : ClosedDiscTriangle) :
    T.alpha+T.beta+T.gamma < Real.pi := by
  have hαb := T.alpha_mem_Ico
  have hβb : T.beta ∈ Ico (0:ℝ) Real.pi := T.cycle.alpha_mem_Ico
  have hγb : T.gamma ∈ Ico (0:ℝ) Real.pi := T.cycle.cycle.alpha_mem_Ico
  by_cases hα : T.alpha = 0
  · by_cases hβ : T.beta = 0
    · linarith only [hα,hβ,hγb.2]
    · by_cases hγ : T.gamma = 0
      · linarith only [hα,hγ,hβb.2]
      · have hc : T.cycle.gamma = 0 := by
          change T.cycle.cycle.cycle.alpha = 0
          rw [T.cycle_three,hα]
        have he := T.cycle.angle_sum_lt_pi_of_one_ideal hβ hγ hc
        change T.beta+T.gamma+T.cycle.gamma < Real.pi at he
        have hcy : T.cycle.gamma = T.alpha := by
          change T.cycle.cycle.cycle.alpha = T.alpha
          rw [T.cycle_three]
        rw [hcy] at he
        linarith only [he]
  · by_cases hβ : T.beta = 0
    · by_cases hγ : T.gamma = 0
      · linarith only [hβ,hγ,hαb.2]
      · have hc : T.cycle.cycle.gamma = 0 := by
          change T.cycle.cycle.cycle.cycle.alpha = 0
          rw [T.cycle_three]
          exact hβ
        have hb : T.cycle.cycle.beta ≠ 0 := by
          change T.cycle.cycle.cycle.alpha ≠ 0
          rwa [T.cycle_three]
        have he := T.cycle.cycle.angle_sum_lt_pi_of_one_ideal hγ hb hc
        have hcy : T.cycle.cycle.beta = T.alpha := by
          change T.cycle.cycle.cycle.alpha = T.alpha
          rw [T.cycle_three]
        change T.gamma+T.cycle.cycle.beta+T.cycle.cycle.gamma < Real.pi at he
        rw [hcy,hc] at he
        linarith only [he,hβ]
    · by_cases hγ : T.gamma = 0
      · exact T.angle_sum_lt_pi_of_one_ideal hα hβ hγ
      · have ha : ‖(T.a : ℂ)‖ < 1 := by
          by_contra! h
          exact hα (T.alpha_of_ideal (le_antisymm T.a.norm_le_one h))
        have hb : ‖(T.b : ℂ)‖ < 1 := by
          by_contra! h
          exact hβ (T.beta_of_ideal (le_antisymm T.b.norm_le_one h))
        have hc : ‖(T.c : ℂ)‖ < 1 := by
          by_contra! h
          exact hγ (T.gamma_of_ideal (le_antisymm T.c.norm_le_one h))
        let U := T.finiteTriangle ha hb hc
        have he := U.angle_sum_lt_pi
        rw [← U.closed_angles.1,← U.closed_angles.2.1,← U.closed_angles.2.2] at he
        change (T.finiteTriangle ha hb hc).toClosedDiscTriangle.alpha +
          (T.finiteTriangle ha hb hc).toClosedDiscTriangle.beta +
          (T.finiteTriangle ha hb hc).toClosedDiscTriangle.gamma < Real.pi at he
        rwa [T.finiteTriangle_toClosedDiscTriangle] at he

theorem ClosedHTriangle.angle_sum_lt_pi (T : ClosedHTriangle) :
    T.alpha+T.beta+T.gamma < Real.pi := T.toDiscTriangle.angle_sum_lt_pi

end
end LowDimensionalTopology.Geometry.Hyperbolic
